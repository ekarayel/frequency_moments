#!/bin/bash
THIS=`dirname "$0"`

DEPLOY=false
OPTS=""
while test $# -gt 0
do
    case "$1" in
        --quick) OPTS="-o quick_and_dirty -o skip_proofs"
            ;;
        --deploy) DEPLOY=true
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
  $OPTS \
  -v

BROWSER_INFO=$(isabelle getenv -b ISABELLE_BROWSER_INFO)

if [ "$DEPLOY" = true ] ; then
  (
    cd $BROWSER_INFO
    git init
    git add -A
    git commit -m "Push $(date -Ins)"
    git remote add origin git@github.com:ekarayel/frequency-moments-doc.git
    git push -f origin master
    rm -rf .git
  )
fi

echo $BROWSER_INFO
