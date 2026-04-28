#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  ./clean_coq_artifacts.sh [--recursive] [--dry-run] DIR

Remove Coq build artifacts from DIR:
  *.vo *.vos *.vok *.glob *.aux .*.aux

Options:
  --recursive  Clean DIR and all subdirectories.
  --dry-run    Print files that would be removed without deleting them.

Examples:
  ./clean_coq_artifacts.sh IntArrayClaude
  ./clean_coq_artifacts.sh --recursive IntArrayClaude
  ./clean_coq_artifacts.sh --dry-run IntArrayClaude
EOF
}

recursive=0
dry_run=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --recursive)
      recursive=1
      shift
      ;;
    --dry-run)
      dry_run=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    -*)
      echo "Unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [[ $# -ne 1 ]]; then
  usage >&2
  exit 2
fi

target_dir=$1
if [[ ! -d "$target_dir" ]]; then
  echo "Not a directory: $target_dir" >&2
  exit 1
fi

find_args=("$target_dir")
if [[ "$recursive" -eq 0 ]]; then
  find_args+=(-maxdepth 1)
fi

find_args+=(
  -type f
  '('
    -name '*.vo'
    -o -name '*.vos'
    -o -name '*.vok'
    -o -name '*.glob'
    -o -name '*.aux'
    -o -name '.*.aux'
  ')'
)

if [[ "$dry_run" -eq 1 ]]; then
  find "${find_args[@]}" -print
else
  find "${find_args[@]}" -delete
fi
