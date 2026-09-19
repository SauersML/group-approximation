#!/bin/bash
# grab.sh <file> <regex> <before> <after> : print context around the first match
f=$1; re=$2; b=$3; a=$4
n=$(grep -n -E "$re" "$f" | head -1 | cut -d: -f1)
[ -z "$n" ] && { echo "NO MATCH: $re"; exit 0; }
s=$((n-b)); [ $s -lt 1 ] && s=1
sed -n "${s},$((n+a))p" "$f"
