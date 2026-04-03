#!/usr/bin/env python3
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path


COMMON_HEADERS = """#include <assert.h>
#include <vector>
#include <string>
#include <map>
#include <list>
#include <cmath>
#include <algorithm>
#include <cstdlib>
using namespace std;
"""


INTERFACE_PATTERNS = [
    re.compile(r"cannot convert .*std::vector", re.IGNORECASE),
    re.compile(r"cannot convert .*std::string", re.IGNORECASE),
    re.compile(r"initializing argument .* of .*\*", re.IGNORECASE),
    re.compile(r"too few arguments to function", re.IGNORECASE),
    re.compile(r"no matching function for call", re.IGNORECASE),
]


def load_entries(jsonl_path: Path):
    entries = []
    for line in jsonl_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        obj = json.loads(line)
        task_num = int(obj["task_id"].split("/")[1])
        entries.append((task_num, obj))
    entries.sort(key=lambda x: x[0])
    return entries


def split_top_level_commas(s: str):
    out = []
    cur = []
    depth_angle = 0
    depth_paren = 0
    for ch in s:
        if ch == "<":
            depth_angle += 1
        elif ch == ">":
            if depth_angle > 0:
                depth_angle -= 1
        elif ch == "(":
            depth_paren += 1
        elif ch == ")":
            if depth_paren > 0:
                depth_paren -= 1

        if ch == "," and depth_angle == 0 and depth_paren == 0:
            piece = "".join(cur).strip()
            if piece:
                out.append(piece)
            cur = []
        else:
            cur.append(ch)

    piece = "".join(cur).strip()
    if piece:
        out.append(piece)
    return out


def parse_signature(sig_line: str):
    m = re.match(r"\s*(.+?)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)\s*\{\s*$", sig_line)
    if not m:
        return None
    ret_type = m.group(1).strip()
    fn_name = m.group(2).strip()
    params_raw = m.group(3).strip()
    params = []
    if params_raw and params_raw != "void":
        for p in split_top_level_commas(params_raw):
            p = p.strip()
            # Expect a trailing variable name.
            pm = re.match(r"\s*(.+?)\s+([A-Za-z_][A-Za-z0-9_]*)\s*$", p)
            if not pm:
                return None
            params.append({"type": pm.group(1).strip(), "name": pm.group(2).strip()})
    return {"ret": ret_type, "name": fn_name, "params": params}


def parse_original_decl(entry: dict):
    decl = entry.get("declaration", "")
    lines = [ln.rstrip() for ln in decl.splitlines() if ln.strip()]
    for ln in reversed(lines):
        if "(" in ln and ")" in ln and ln.strip().endswith("{"):
            sig = parse_signature(ln.strip())
            if sig:
                return sig
    return None


def find_converted_signature(c_text: str, fn_name: str):
    for ln in c_text.splitlines():
        s = ln.strip()
        if not s or s.startswith("/*") or s.startswith("//"):
            continue
        if f"{fn_name}(" not in s:
            continue
        if s.endswith("{"):
            sig = parse_signature(s)
            if sig and sig["name"] == fn_name:
                return sig
    return None


def norm_type(t: str):
    return " ".join(t.replace("*", " * ").split())


def compact_type(t: str):
    return norm_type(t).replace(" ", "")


def vector_inner_type(t: str):
    m = re.match(r"\s*vector\s*<\s*(.+)\s*>\s*$", t)
    if not m:
        return None
    return m.group(1).strip()


def is_c_string_ptr_type(t: str):
    nt = norm_type(t)
    return nt in {"char *", "const char *", "char **", "const char **"}


def params_same(a_params, b_params):
    if len(a_params) != len(b_params):
        return False
    for a, b in zip(a_params, b_params):
        if norm_type(a["type"]) != norm_type(b["type"]) or a["name"] != b["name"]:
            return False
    return True


def build_auto_wrapper(entry: dict, c_file: Path):
    orig = parse_original_decl(entry)
    if not orig:
        return None
    c_text = c_file.read_text(encoding="utf-8", errors="ignore")
    conv = find_converted_signature(c_text, orig["name"])
    if not conv:
        return None

    same_params = params_same(orig["params"], conv["params"])
    if norm_type(orig["ret"]) == norm_type(conv["ret"]) and same_params:
            return None

    call_args = []
    prep_lines = []
    conv_params = conv["params"]
    pos = 0

    for p in orig["params"]:
        otype = norm_type(p["type"])
        oname = p["name"]
        inner = vector_inner_type(otype)

        if inner is not None:
            if pos + 1 >= len(conv_params):
                return None
            data_type = conv_params[pos]["type"]
            size_type = conv_params[pos + 1]["type"]
            if data_type and "*" in data_type and size_type and norm_type(size_type) == "int":
                ndata = norm_type(data_type)
                if inner in {"int", "float", "double"}:
                    call_args.append(f"{oname}.data()")
                    call_args.append(f"(int){oname}.size()")
                    pos += 2
                    continue
                if inner == "string" and compact_type(ndata) in {"char**", "constchar**"}:
                    prep_lines.append(f"vector<const char*> _{oname}_cstr;")
                    prep_lines.append(f"_{oname}_cstr.reserve({oname}.size());")
                    prep_lines.append(f"for (const auto& _s : {oname}) _{oname}_cstr.push_back(_s.c_str());")
                    if compact_type(ndata) == "char**":
                        call_args.append(f"(char**)(_{oname}_cstr.data())")
                    else:
                        call_args.append(f"(const char**)(_{oname}_cstr.data())")
                    call_args.append(f"(int){oname}.size()")
                    pos += 2
                    continue
            return None

        if otype == "string":
            if pos >= len(conv_params):
                return None
            ct = conv_params[pos]["type"]
            if ct and ("char *" in norm_type(ct) or "const char *" in norm_type(ct)):
                call_args.append(f"{oname}.c_str()")
                pos += 1
                continue

        if pos >= len(conv_params):
            return None
        ct = conv_params[pos]["type"]
        if ct and norm_type(ct) == otype:
            call_args.append(oname)
            pos += 1
            continue

        return None

    if pos != len(conv_params):
        return None

    call_expr = f"::{orig['name']}({', '.join(call_args)})"
    orig_ret = norm_type(orig["ret"])
    conv_ret = norm_type(conv["ret"])

    if orig_ret == conv_ret:
        body_lines = prep_lines + [f"return {call_expr};"]
    elif orig_ret == "string" and (conv_ret == "const char *" or conv_ret == "char *"):
        body_lines = prep_lines + [f"auto _ret = {call_expr};", "return _ret ? string(_ret) : string();"]
    elif orig_ret == "vector<int>" and conv_ret == "IntArray":
        body_lines = prep_lines + [f"IntArray _ret = {call_expr};", "if (_ret.data == nullptr || _ret.size <= 0) return {};", "return vector<int>(_ret.data, _ret.data + _ret.size);"]
    elif orig_ret == "vector<float>" and conv_ret == "FloatArray":
        body_lines = prep_lines + [f"FloatArray _ret = {call_expr};", "if (_ret.data == nullptr || _ret.size <= 0) return {};", "return vector<float>(_ret.data, _ret.data + _ret.size);"]
    elif orig_ret == "vector<string>" and (conv_ret == "StrArray" or conv_ret == "StringArray"):
        body_lines = prep_lines + [f"{conv_ret} _ret = {call_expr};", "vector<string> _out;", "if (_ret.data == nullptr || _ret.size <= 0) return _out;", "for (int _i = 0; _i < _ret.size; ++_i) _out.push_back(_ret.data[_i] ? string(_ret.data[_i]) : string());", "return _out;"]
    elif orig_ret == "map<char,int>" and conv_ret == "CharIntMap":
        body_lines = prep_lines + [f"CharIntMap _ret = {call_expr};", "map<char,int> _out;", "if (_ret.keys == nullptr || _ret.values == nullptr || _ret.size <= 0) return _out;", "for (int _i = 0; _i < _ret.size; ++_i) _out[_ret.keys[_i]] = _ret.values[_i];", "return _out;"]
    else:
        return None

    params_sig = ", ".join([f"{p['type']} {p['name']}" for p in orig["params"]])
    body = "\n    ".join(body_lines)
    wrapper = f"\n{orig['ret']} {orig['name']}({params_sig}){{\n    {body}\n}}\n"

    rename_macro = f"{orig['name']}_c_impl"

    return {
        "wrapper": wrapper,
        "orig_name": orig["name"],
        "rename_macro": rename_macro,
    }


def classify_compile_error(stderr: str) -> str:
    low = stderr.lower()
    if "boost/any.hpp" in low or "boost::any" in low:
        return "unsupported_dependency"
    for pat in INTERFACE_PATTERNS:
        if pat.search(stderr):
            return "interface_mismatch"
    return "compile_error"


def build_harness(c_file: Path, test_code: str, wrapper_info=None) -> str:
    test_code = test_code.replace("#undef NDEBUG", "")
    wrapped = COMMON_HEADERS + "\n"
    rename_map = {}
    if wrapper_info and wrapper_info.get("rename_map"):
        rename_map.update(wrapper_info["rename_map"])
    elif wrapper_info and wrapper_info.get("rename_macro"):
        rename_map[wrapper_info["orig_name"]] = wrapper_info["rename_macro"]

    if rename_map:
        for k, v in rename_map.items():
            wrapped += f"#define {k} {v}\n"
        wrapped += f'#include "{c_file}"\n'
        for k in rename_map.keys():
            wrapped += f"#undef {k}\n"
    else:
        wrapped += f'#include "{c_file}"\n'

    if wrapper_info and wrapper_info.get("wrapper"):
        wrapper_code = wrapper_info["wrapper"]
        for k, v in rename_map.items():
            wrapper_code = wrapper_code.replace(f"::{k}(", f"::{v}(")
        wrapped += wrapper_code + "\n"

    wrapped += test_code
    return wrapped


def run_one(task_num: int, entry: dict, prompts_dir: Path, auto_adapt: bool):
    c_file = (prompts_dir / f"CPP_{task_num}.c").resolve()
    if not c_file.exists():
        return {
            "task": task_num,
            "status": "missing_c_file",
            "message": f"{c_file} not found",
        }

    test_code = entry.get("test") or entry.get("example_test") or ""
    if not test_code.strip():
        return {
            "task": task_num,
            "status": "no_test",
            "message": "No test/example_test content",
        }

    wrapper_info = None
    if auto_adapt:
        wrapper_info = build_manual_wrapper(task_num)
        if wrapper_info is None:
            wrapper_info = build_auto_wrapper(entry, c_file)
    harness = build_harness(c_file, test_code, wrapper_info)

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src = td_path / "test.cpp"
        exe = td_path / "test_bin"
        src.write_text(harness, encoding="utf-8")

        compile_cmd = ["g++", "-std=c++17", str(src), "-lm", "-o", str(exe)]
        cproc = subprocess.run(compile_cmd, capture_output=True, text=True)
        if cproc.returncode != 0:
            status = classify_compile_error(cproc.stderr)
            msg = cproc.stderr.splitlines()[0] if cproc.stderr else "compile failed"
            return {
                "task": task_num,
                "status": status,
                "message": msg,
            }

        rproc = subprocess.run([str(exe)], capture_output=True, text=True)
        if rproc.returncode == 0:
            return {
                "task": task_num,
                "status": "pass",
                "message": "ok",
            }

        return {
            "task": task_num,
            "status": "runtime_fail",
            "message": f"exit={rproc.returncode}",
        }


def write_reports(results, out_json: Path, out_txt: Path):
    out_json.write_text(json.dumps(results, ensure_ascii=True, indent=2), encoding="utf-8")

    counts = {}
    for item in results:
        counts[item["status"]] = counts.get(item["status"], 0) + 1

    lines = []
    lines.append("Summary")
    lines.append("=======")
    for k in sorted(counts.keys()):
        lines.append(f"{k}: {counts[k]}")

    lines.append("")
    lines.append("Details")
    lines.append("=======")
    for item in results:
        lines.append(f"CPP_{item['task']}: {item['status']} :: {item['message']}")

    out_txt.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description="Run humanevalx.json tests against converted C files")
    parser.add_argument("--jsonl", default="humanevalx.json", help="Path to humanevalx jsonl file")
    parser.add_argument("--prompts-dir", default="prompts_out", help="Directory containing CPP_*.c files")
    parser.add_argument("--exclude", default="162", help="Comma-separated task ids to exclude")
    parser.add_argument("--out-json", default="test_report.json", help="Output JSON report")
    parser.add_argument("--out-txt", default="test_report.txt", help="Output text report")
    parser.add_argument("--auto-adapt", action="store_true", help="Auto-generate simple wrappers for common signature mismatches")
    args = parser.parse_args()

    exclude = set()
    for x in args.exclude.split(","):
        x = x.strip()
        if x:
            exclude.add(int(x))

    jsonl_path = Path(args.jsonl)
    prompts_dir = Path(args.prompts_dir)

    entries = load_entries(jsonl_path)
    filtered = [(tid, e) for tid, e in entries if tid not in exclude]

    results = []
    for tid, entry in filtered:
        results.append(run_one(tid, entry, prompts_dir, args.auto_adapt))

    write_reports(results, Path(args.out_json), Path(args.out_txt))

    counts = {}
    for item in results:
        counts[item["status"]] = counts.get(item["status"], 0) + 1

    print(f"TOTAL: {len(results)}")
    for k in sorted(counts.keys()):
        print(f"{k}: {counts[k]}")
    print(f"REPORT_JSON: {Path(args.out_json).resolve()}")
    print(f"REPORT_TXT: {Path(args.out_txt).resolve()}")


def build_manual_wrapper(task_num: int):
    if task_num == 22:
        return {
            "rename_map": {"filter_integers": "filter_integers_c_impl"},
            "wrapper": r'''
struct _PyArg {
    int kind;
    int i;
    double d;
    string s;
    _PyArg() : kind(3), i(0), d(0.0), s("") {}
    _PyArg(int v) : kind(0), i(v), d(0.0), s("") {}
    _PyArg(double v) : kind(1), i(0), d(v), s("") {}
    _PyArg(char v) : kind(3), i(0), d(0.0), s(string(1, v)) {}
    _PyArg(const char* v) : kind(2), i(0), d(0.0), s(v ? v : "") {}
    _PyArg(const string& v) : kind(2), i(0), d(0.0), s(v) {}
    _PyArg(std::initializer_list<int>) : kind(3), i(0), d(0.0), s("") {}
};

vector<int> filter_integers(std::initializer_list<_PyArg> values){
    vector<PyValue> arr;
    vector<string> keep;
    arr.reserve(values.size());
    keep.reserve(values.size());
    for (const auto& v : values) {
        PyValue p{};
        if (v.kind == 0) {
            p.type = PY_INT;
            p.i = v.i;
        } else if (v.kind == 1) {
            p.type = PY_DOUBLE;
            p.d = v.d;
        } else if (v.kind == 2) {
            p.type = PY_STRING;
            keep.push_back(v.s);
            p.s = keep.back().c_str();
        } else {
            p.type = PY_DOUBLE;
            p.d = 0.0;
        }
        arr.push_back(p);
    }
    IntArray r = ::filter_integers_c_impl(arr.data(), (int)arr.size());
    if (r.data == nullptr || r.size <= 0) return {};
    return vector<int>(r.data, r.data + r.size);
}
'''
        }

    if task_num == 32:
        return {
            "rename_map": {"poly": "poly_c_impl", "find_zero": "find_zero_c_impl"},
            "wrapper": r'''
double poly(vector<double> xs, double x){
    return ::poly_c_impl(xs.data(), (int)xs.size(), x);
}
double find_zero(vector<double> xs){
    return ::find_zero_c_impl(xs.data(), (int)xs.size());
}
'''
        }

    if task_num == 38:
        return {
            "rename_map": {"encode_cyclic": "encode_cyclic_c_impl", "decode_cyclic": "decode_cyclic_c_impl"},
            "wrapper": r'''
string encode_cyclic(string s){
    auto p = ::encode_cyclic_c_impl(s.c_str());
    return p ? string(p) : string();
}
string decode_cyclic(string s){
    auto p = ::decode_cyclic_c_impl(s.c_str());
    return p ? string(p) : string();
}
'''
        }

    if task_num == 50:
        return {
            "rename_map": {"encode_shift": "encode_shift_c_impl", "decode_shift": "decode_shift_c_impl"},
            "wrapper": r'''
string encode_shift(string s){
    auto p = ::encode_shift_c_impl(s.c_str());
    return p ? string(p) : string();
}
string decode_shift(string s){
    auto p = ::decode_shift_c_impl(s.c_str());
    return p ? string(p) : string();
}
'''
        }

    if task_num == 52:
        return {
            "rename_map": {"below_threshold": "below_threshold_c_impl"},
            "wrapper": r'''
bool below_threshold(vector<int> l, int t){
    return ::below_threshold_c_impl(l.data(), (int)l.size(), t);
}
'''
        }

    if task_num == 87:
        return {
            "rename_map": {"get_row": "get_row_c_impl"},
            "wrapper": r'''
vector<vector<int>> get_row(vector<vector<int>> lst, int x){
    int rows = (int)lst.size();
    vector<int*> ptrs(rows, nullptr);
    vector<int> row_sizes(rows, 0);
    for (int i = 0; i < rows; ++i) {
        row_sizes[i] = (int)lst[i].size();
        ptrs[i] = lst[i].empty() ? nullptr : lst[i].data();
    }
    IntArray r = ::get_row_c_impl(ptrs.data(), row_sizes.data(), rows, x);
    vector<vector<int>> out;
    for (int i = 0; i < r.size; ++i) out.push_back({r.data[i * 2], r.data[i * 2 + 1]});
    return out;
}
'''
        }

    if task_num == 95:
        return {
            "rename_map": {"check_dict_case": "check_dict_case_c_impl"},
            "wrapper": r'''
bool check_dict_case(map<string,string> dict){
    vector<const char*> keys;
    keys.reserve(dict.size());
    for (auto &kv : dict) keys.push_back(kv.first.c_str());
    return ::check_dict_case_c_impl(keys.data(), (int)keys.size());
}
'''
        }

    if task_num == 114:
        return {
            "rename_map": {"minSubArraySum": "minSubArraySum_c_impl"},
            "wrapper": r'''
long long minSubArraySum(vector<long long> nums){
    return ::minSubArraySum_c_impl(nums.data(), (int)nums.size());
}
'''
        }

    if task_num == 115:
        return {
            "rename_map": {"max_fill": "max_fill_c_impl"},
            "wrapper": r'''
int max_fill(vector<vector<int>> grid, int capacity){
    int rows = (int)grid.size();
    int cols = rows == 0 ? 0 : (int)grid[0].size();
    vector<int*> ptrs(rows, nullptr);
    for (int i = 0; i < rows; ++i) ptrs[i] = grid[i].empty() ? nullptr : grid[i].data();
    return ::max_fill_c_impl(ptrs.data(), rows, cols, capacity);
}
'''
        }

    if task_num == 119:
        return {
            "rename_map": {"match_parens": "match_parens_c_impl"},
            "wrapper": r'''
string match_parens(vector<string> lst){
    if (lst.size() != 2) return "No";
    const char* r = ::match_parens_c_impl(lst[0].c_str(), lst[1].c_str());
    return r ? string(r) : string();
}
'''
        }

    if task_num == 129:
        return {
            "rename_map": {"minPath": "minPath_c_impl"},
            "wrapper": r'''
vector<int> minPath(vector<vector<int>> grid, int k){
    int n = (int)grid.size();
    vector<int*> ptrs(n, nullptr);
    for (int i = 0; i < n; ++i) ptrs[i] = grid[i].empty() ? nullptr : grid[i].data();
    IntArray r = ::minPath_c_impl(ptrs.data(), n, k);
    if (r.data == nullptr || r.size <= 0) return {};
    return vector<int>(r.data, r.data + r.size);
}
'''
        }

    return None


if __name__ == "__main__":
    main()
