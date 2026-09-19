#!/bin/bash
# random existence probe (no isomorph rejection): deepest level reached by single-cycle models of H(3,3^mb,3^mc,3^md)
cd $(dirname $0)
SET=${1:-"1 2 4"}; M=${2:-8}; MAX=${3:-10}
for mb in $SET; do for mc in $SET; do for md in $SET; do
  e="3,$((3**mb)),$((3**mc)),$((3**md))"
  r=$(nice -n 10 timeout 600 ./glift 0 $MAX noR e=$e rand=$M,1 first 2>/dev/null | grep -E "^level" | awk '$4>0{l=$2} END{print l}')
  echo "m=($mb,$mc,$md) e=$e deepest=$r"
done; done; done
