W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1; PY=/usr/bin/python3.11
for id in amenable-extensions-of-uqs-groups-are-surjunctive surjunctive-by-amenable-extensions-are-surjunctive surjunctive-groups-are-uniformly-quantitatively-surjunctive surjunctive-groups-are-quantitatively-surjunctive leavitt-units-are-not-quantitatively-surjunctive maximal-bernoulli-rokhlin-entropy-makes-groups-uqs; do
  CAIRN_ROOT="$W" nice -n 10 "$PY" tools/cairn.py why "$id" 2>&1 | grep -v 'graph warning' | grep -m1 -E '^\S+ \[' | cut -c1-150
done
echo ST21-DONE
