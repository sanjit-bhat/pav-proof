#!/bin/bash

set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/.."

GO_JOURNAL_PATH=""
GO_NFSD_PATH=""

usage() {
  echo "Usage: $0 [--go-journal <path>] [--go-nfsd <path>]"
  echo ""
  echo "Options:"
  echo "  --go-journal <path>   Path to mit-pdos/go-journal repository"
  echo "  --go-nfsd <path>      Path to mit-pdos/go-nfsd repository"
}

# Check if no arguments provided
if [ $# -eq 0 ]; then
  usage
  exit 1
fi

# Parse arguments
while [[ $# -gt 0 ]]; do
  case $1 in
  --go-journal)
    GO_JOURNAL_PATH="$2"
    shift 2
    ;;
  --go-nfsd)
    GO_NFSD_PATH="$2"
    shift 2
    ;;
  -h | --help)
    usage
    exit 0
    ;;
  *)
    echo "error: unexpected argument $1"
    usage
    exit 1
    ;;
  esac
done

# Verify at least one path was provided
if [ -z "$GO_JOURNAL_PATH" ] && [ -z "$GO_NFSD_PATH" ]; then
  echo "Error: At least one repository path must be provided."
  usage
fi

# Translate go-journal if path provided
if [ -n "$GO_JOURNAL_PATH" ]; then
  go tool goose -out external/Goose -dir "$GO_JOURNAL_PATH" ./...
fi

# Translate go-nfsd if path provided
if [ -n "$GO_NFSD_PATH" ]; then
  go tool goose -out external/Goose -dir "$GO_NFSD_PATH" \
    ./kvs ./super ./fh ./simple ./nfstypes
fi
