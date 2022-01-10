#!/bin/bash
THIS=`realpath $(dirname "$0")`

OPTS=""
while test $# -gt 0
do
    case "$1" in
        --quick) OPTS="-o quick_and_dirty -o skip_proofs"
            ;;
        --*) echo "bad option $1"
            exit 1
            ;;
        *) echo "unknown argument $1"
            exit 1
            ;;
    esac
    shift
done

isabelle build \
  -D $THIS/thys \
  -o browser_info \
  -o document=pdf \
  -o document_variants="document:outline=/proof" \
  -o document_output="$THIS/output" \
  -f \
  $OPTS \
  -v
