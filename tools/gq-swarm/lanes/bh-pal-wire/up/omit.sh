#!/usr/bin/env bash
# omit.sh ERRFILE SRCFILE : for each "unused section variable" error, insert `omit [..] in` above the reported line.
ERR=$1; SRC=$2
awk '/automatically included section variable\(s\) unused/{split($2,a,":"); ln=a[2]; getline; v=$0; sub(/^ +/,"",v); print ln "\t" v}' "$ERR" | sort -rn | while IFS=$'\t' read -r ln v; do
  awk -v n="$ln" -v v="$v" 'NR==n{print "omit " v " in"} {print}' "$SRC" > "$SRC.tmp" && mv "$SRC.tmp" "$SRC"
  echo "  $ln omit $v"
done
