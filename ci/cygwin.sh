#!/bin/bash
set -eu
cd "$(dirname "$0")"
cd ..
echo "Entering directory '$PWD'"
case "$1" in
configure)
    set -x
    gcc -v
    ./configure --enable-debug --enable-multiple-threaded-vms CC=gcc
    ;;
compile)
    set -x
    make
    ;;
test)
    set -x
    make check
    ;;
*)
    exit 1
    ;;
esac
