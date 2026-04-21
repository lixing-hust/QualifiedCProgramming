#!/usr/bin/env bash
set -euo pipefail

ROOT="/home/yangfp/QualifiedCProgramming/QCP_examples/CAV"
CONTRACT_SCRIPT="$ROOT/scripts/run_codex_contract.py"
VERIFY_SCRIPT="$ROOT/scripts/run_codex_verify.py"

EXPORT_EXAMPLES=1

usage() {
  cat <<'EOF'
usage: run_codex_contract_verify_many.sh [--no-export-examples] <name1> [name2 ...]

For each <name>, run:
  1. python3 scripts/run_codex_contract.py raw/<name>.md --function-name <name>
  2. python3 scripts/run_codex_verify.py input/<name>.c --function-name <name> [--export-examples]

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

FAILURES=()
SUCCESSES=()

for name in "${NAMES[@]}"; do
  RAW_PATH="raw/${name}.md"
  INPUT_PATH="input/${name}.c"

  if [[ ! -f "$RAW_PATH" ]]; then
    echo "[contract-verify-many] missing raw file: $RAW_PATH" >&2
    FAILURES+=("$name:missing_raw")
    continue
  fi

  echo "[contract-verify-many] contract start name=$name"
  if ! python3 "$CONTRACT_SCRIPT" "$RAW_PATH" --function-name "$name"; then
    echo "[contract-verify-many] contract failed name=$name" >&2
    FAILURES+=("$name:contract")
    continue
  fi
  echo "[contract-verify-many] contract done name=$name"

  if [[ ! -f "$INPUT_PATH" ]]; then
    echo "[contract-verify-many] missing generated input after contract: $INPUT_PATH" >&2
    FAILURES+=("$name:missing_input")
    continue
  fi

  VERIFY_CMD=(python3 "$VERIFY_SCRIPT" "$INPUT_PATH" --function-name "$name")
  if [[ $EXPORT_EXAMPLES -eq 1 ]]; then
    VERIFY_CMD+=(--export-examples)
  fi

  echo "[contract-verify-many] verify start name=$name"
  if ! "${VERIFY_CMD[@]}"; then
    echo "[contract-verify-many] verify failed name=$name" >&2
    FAILURES+=("$name:verify")
    continue
  fi

  SUCCESSES+=("$name")
  echo "[contract-verify-many] verify done name=$name"
done

echo "[contract-verify-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]}"

if [[ ${#SUCCESSES[@]} -gt 0 ]]; then
  echo "[contract-verify-many] successes:"
  for success in "${SUCCESSES[@]}"; do
    echo "  $success"
  done
fi

if [[ ${#FAILURES[@]} -gt 0 ]]; then
  echo "[contract-verify-many] failures:" >&2
  for failure in "${FAILURES[@]}"; do
    echo "  $failure" >&2
  done
  exit 1
fi

echo "[contract-verify-many] all done"
