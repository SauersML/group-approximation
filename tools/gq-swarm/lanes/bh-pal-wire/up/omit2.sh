#!/usr/bin/env bash
# omit2.sh ERRFILE SRCFILE: for each unused-section-variable error at line n, insert `omit [..] in`
# above the declaration's modifiers (docstring, attributes) that precede line n.
ERR=$1; SRC=$2
awk '/automatically included section variable\(s\) unused/{split($2,a,":"); ln=a[2]; getline; v=$0; sub(/^ +/,"",v); print ln "\t" v}' "$ERR" | sort -rn | while IFS=$'\t' read -r ln v; do
  s=$(awk -v n="$ln" '{L[NR]=$0} END{
    i=n
    while (1) {
      p=i-1
      if (p>=1 && L[p] ~ /^@\[/) { i=p; continue }
      if (p>=1 && L[p] ~ /-\/[ ]*$/) { j=p; while (j>=1 && L[j] !~ /^\/--/) j--; if (j>=1) { i=j; continue } }
      break
    }
    print i}' "$SRC")
  awk -v n="$s" -v v="$v" 'NR==n{print "omit " v " in"} {print}' "$SRC" > "$SRC.tmp" && mv "$SRC.tmp" "$SRC"
  echo "  $ln -> insert at $s: omit $v"
done
