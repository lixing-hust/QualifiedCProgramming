#!/usr/bin/env bash
set -euo pipefail

ROOT="/home/yangfp/QualifiedCProgramming/QCP_examples/CAV"
VERIFY_SCRIPT="$ROOT/scripts/run_codex_verify.py"
EXPORT_EXAMPLES=1

usage() {
  cat <<'EOF'
usage: run_codex_verify_many.sh [--no-export-examples] <name1> [name2 ...]

For each <name>, run:
  python3 scripts/run_codex_verify.py input/<name>.c --function-name <name> [--export-examples]

Options:
  --no-export-examples   Do not pass --export-examples to verify.
EOF
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        NAMES+=("$1")
        shift
      done
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      NAMES+=("$1")
      shift
      ;;
  esac
done

if [[ ${#NAMES[@]} -lt 1 ]]; then
  usage >&2
  exit 2
fi

cd "$ROOT"

for name in "${NAMES[@]}"; do
  echo "[verify-many] start name=$name"
  VERIFY_CMD=(python3 "$VERIFY_SCRIPT" "input/${name}.c" --function-name "$name")
  if [[ $EXPORT_EXAMPLES -eq 1 ]]; then
    VERIFY_CMD+=(--export-examples)
  fi
  "${VERIFY_CMD[@]}"
  echo "[verify-many] done name=$name"
done
