#!/usr/bin/env bash

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
INT_DIR="$ROOT_DIR/QCP_examples/humaneval/IntClaude"
SYMEXEC="${SYMEXEC:-$ROOT_DIR/linux-binary/symexec}"
COQ_SWITCH="${COQ_SWITCH:-coq8201}"
KEEP_ARTIFACTS="${KEEP_ARTIFACTS:-0}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/run_intclaude_regression.sh [C_ID ...]

Examples:
  scripts/run_intclaude_regression.sh
  scripts/run_intclaude_regression.sh 13 59 150

Environment:
  SYMEXEC=/path/to/symexec      Override the symexec binary.
  COQ_SWITCH=coq8201           Override the opam switch used for coqc.
  KEEP_ARTIFACTS=1             Keep Coq build artifacts and symexec backups.

The script regenerates goal/auto/manual/goal_check with symexec.  Because
symexec rewrites C_XX_manual.v with Admitted stubs when --gen-and-backup is
used, the script preserves the existing manual proof before symexec and restores
it before compiling.  This makes the run a real regression check for the
hand-written proofs, not just a check that generated stubs typecheck.
USAGE
}

log() {
  printf '[%s] %s\n' "$(date '+%H:%M:%S')" "$*"
}

failures=()

cleanup_case() {
  local id="$1"
  [[ "$KEEP_ARTIFACTS" == "1" ]] && return 0

  local stem
  for stem in "coins_${id}" "C_${id}_goal" "C_${id}_auto" "C_${id}_manual" "C_${id}_goal_check"; do
    rm -f \
      "$INT_DIR/.${stem}.aux" \
      "$INT_DIR/${stem}.glob" \
      "$INT_DIR/${stem}.vo" \
      "$INT_DIR/${stem}.vos" \
      "$INT_DIR/${stem}.vok"
  done

  rm -f "$INT_DIR/C_${id}_manual_backup"*.v
}

run_symexec() {
  local id="$1"

  "$SYMEXEC" \
    --goal-file="$INT_DIR/C_${id}_goal.v" \
    --proof-auto-file="$INT_DIR/C_${id}_auto.v" \
    --proof-manual-file="$INT_DIR/C_${id}_manual.v" \
    --coq-logic-path=SimpleC.EE \
    -slp "$INT_DIR" SimpleC.EE \
    --input-file="$INT_DIR/C_${id}.c" \
    --gen-and-backup \
    --no-exec-info
}

compile_case() {
  local id="$1"

  (
    cd "$INT_DIR" || exit 1
    local coqincludes
    coqincludes="$(tr '\n' ' ' < _CoqProject)"

    coqc $coqincludes "coins_${id}.v" &&
    coqc $coqincludes "C_${id}_goal.v" &&
    coqc $coqincludes "C_${id}_auto.v" &&
    coqc $coqincludes "C_${id}_manual.v" &&
    coqc $coqincludes "C_${id}_goal_check.v"
  )
}

scan_for_holes() {
  local id="$1"

  (
    cd "$INT_DIR" || exit 1
    ! grep -nE 'Admitted\.|Axiom[[:space:]]' "coins_${id}.v" "C_${id}_manual.v"
  )
}

run_case() {
  local id="$1"
  local c_file="$INT_DIR/C_${id}.c"
  local coins_file="$INT_DIR/coins_${id}.v"
  local manual_file="$INT_DIR/C_${id}_manual.v"
  local manual_snapshot=""

  if [[ ! -f "$c_file" ]]; then
    log "C_${id}: missing $c_file"
    failures+=("C_${id}: missing C file")
    return 1
  fi
  if [[ ! -f "$coins_file" ]]; then
    log "C_${id}: missing $coins_file"
    failures+=("C_${id}: missing coins file")
    return 1
  fi

  if [[ -f "$manual_file" ]]; then
    manual_snapshot="$(mktemp)"
    cp "$manual_file" "$manual_snapshot"
  fi

  log "C_${id}: symexec"
  if ! run_symexec "$id"; then
    log "C_${id}: symexec failed"
    failures+=("C_${id}: symexec failed")
    [[ -n "$manual_snapshot" ]] && cp "$manual_snapshot" "$manual_file"
    [[ -n "$manual_snapshot" ]] && rm -f "$manual_snapshot"
    cleanup_case "$id"
    return 1
  fi

  if [[ -n "$manual_snapshot" ]]; then
    cp "$manual_snapshot" "$manual_file"
    rm -f "$manual_snapshot"
  fi

  log "C_${id}: coqc"
  if ! compile_case "$id"; then
    log "C_${id}: coqc failed"
    failures+=("C_${id}: coqc failed")
    cleanup_case "$id"
    return 1
  fi

  log "C_${id}: scan for Admitted/Axiom"
  if ! scan_for_holes "$id"; then
    log "C_${id}: found Admitted or Axiom"
    failures+=("C_${id}: found Admitted or Axiom")
    cleanup_case "$id"
    return 1
  fi

  cleanup_case "$id"
  log "C_${id}: ok"
}

main() {
  if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
  fi

  if [[ ! -x "$SYMEXEC" ]]; then
    printf 'symexec is not executable: %s\n' "$SYMEXEC" >&2
    exit 2
  fi

  if command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch="$COQ_SWITCH" --set-switch)"
  fi

  if ! command -v coqc >/dev/null 2>&1; then
    printf 'coqc not found. Check COQ_SWITCH or your PATH.\n' >&2
    exit 2
  fi

  local ids=()
  if [[ "$#" -gt 0 ]]; then
    ids=("$@")
  else
    while IFS= read -r file; do
      file="$(basename "$file")"
      ids+=("${file#C_}")
      ids[-1]="${ids[-1]%.c}"
    done < <(find "$INT_DIR" -maxdepth 1 -name 'C_*.c' -print | sort -V)
  fi

  log "Running IntClaude regression for ${#ids[@]} case(s)"
  for id in "${ids[@]}"; do
    run_case "$id"
  done

  if [[ "${#failures[@]}" -gt 0 ]]; then
    printf '\nFailed cases:\n' >&2
    printf '  - %s\n' "${failures[@]}" >&2
    exit 1
  fi

  log "All IntClaude cases passed"
}

main "$@"
