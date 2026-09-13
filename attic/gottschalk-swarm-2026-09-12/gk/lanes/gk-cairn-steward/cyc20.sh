RD=/projects/standard/hsiehph/sauer354/gk-steward
W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1; PY=/usr/bin/python3.11
grep 'dependency cycle' "$RD/out/check.out" | grep -E 'ternary-anti-central-unit-class-is-nonpositive|products-with-a-sofic-factor-are-surjunctive' > "$RD/out/cyc20.txt"
cat "$RD/out/cyc20.txt"
echo "--- statuses:"
for id in $(sed 's/.*claims: //; s/ -> /\n/g' "$RD/out/cyc20.txt" | sort -u); do
  CAIRN_ROOT="$W" nice -n 10 "$PY" tools/cairn.py why "$id" 2>&1 | grep -v 'graph warning' | grep -m1 -E '^\S+ \[' | cut -c1-110
done
echo CYC20-DONE
