#!/bin/bash
# User-space GAP install for lane bh-houghton-presentation (approved by coordinator 09-18).
set -e
D=/projects/standard/hsiehph/sauer354/gqsrc/bh-houghton-presentation/gap
mkdir -p $D && cd $D
V=4.13.1
if [ ! -f gap-$V.tar.gz ]; then
  curl -sL -m 300 -o gap-$V.tar.gz https://github.com/gap-system/gap/releases/download/v$V/gap-$V.tar.gz
fi
ls -la gap-$V.tar.gz
[ -d gap-$V ] || tar xzf gap-$V.tar.gz
cd gap-$V
ls pkg | grep -i -E '^(rcwa|resclasses|polycyclic|utils|gapdoc|grape)' || true
if [ ! -x gap ]; then
  ./configure > configure.log 2>&1
  nice -n 10 make -j1 > make.log 2>&1
fi
ls -la gap && echo BUILD_OK
