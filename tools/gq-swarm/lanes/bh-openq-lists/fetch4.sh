#!/bin/bash
cd /projects/standard/hsiehph/sauer354/gqsrc/bh-openq/hunt4
for id in $(cat ids4.txt); do
  d=src_$id; [ -d $d ] && continue; mkdir -p $d; cd $d
  curl -s -L -m 60 -A "Mozilla/5.0" "https://arxiv.org/e-print/$id" -o ep
  t=$(file -b ep)
  case "$t" in
    gzip*) tar xzf ep 2>/dev/null || gunzip -c ep > main.tex ;;
    *tar*) tar xf ep 2>/dev/null ;;
    *TeX*|*LaTeX*|*text*) cp ep main.tex ;;
  esac
  cd ..; sleep 2
done
echo FETCHDONE4
