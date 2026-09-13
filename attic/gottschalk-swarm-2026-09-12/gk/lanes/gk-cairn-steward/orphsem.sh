W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1
echo "clone HEAD=$(git rev-parse --short HEAD)"
nice -n 10 /usr/bin/python3.11 - <<'PY'
import json
n = json.load(open('.cairn/cache/graph.json'))['nodes']
g = n['gottschalk-surjunctivity-conjecture']
print('claim meta keys:', sorted((g.get('meta') or {}).keys()))
roots = (g.get('meta') or {}).get('refuted_by') or []
if isinstance(roots, dict): roots = list(roots.keys())
print('roots reachable:', sum(1 for r in roots if n.get(r, {}).get('reachable')), 'of', len(roots))
orph = """cancellative-incidence-patterns-do-not-force-domination coset-shifts-split-off-full-shifts-at-lifted-alphabets
leavitt-toeplitz-commutator-is-a-v-conjugate-level-relation radu-lattice-radius-two-pairs-force-the-mark-into-the-radical
regular-hnn-intertwiner-coboundary-on-v-refutes-the-v-gate right-child-exchange-group-has-infinite-dihedral-root-closure
rigid-unbalanced-two-patch-rules-beyond-class-ii-not-injective separated-finite-stabilizers-give-modular-hecke-hopficity
stage-models-cannot-close-the-leavitt-hexagon ternary-anti-central-defect-ideal-is-the-evaluation-kernel
binary-jacobson-el3-is-finitely-presented data-exact-read-ancilla-words-realize-only-translations
depth-monotone-units-carry-weakly-finite-nonzero-defect four-transvection-set-escapes-depth-monotone-units
four-transvection-units-have-a-weakly-finite-symbol-image jacobson-el3-amalgam-kernel-is-residually-finite
jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel jacobson-el4-is-finitely-presented-steinberg-group
lex-decreasing-units-with-order-preserving-letters-are-amenable marker-realizations-reduce-to-two-linear-data-writes
one-transvection-s0-lift-has-no-left-inverse radu-lattice-one-sided-pairs-need-radius-five
split-cylinder-data-cannot-force-defect-submultiplicativity toeplitz-commutators-do-not-normally-generate-amalgam-kernel
v-rank-functions-split-as-augmentation-plus-reduced""".split()
ment = {o: [] for o in orph}
for k, d in n.items():
    m = d.get('meta') or {}
    for key, val in m.items():
        if key in ('id', 'title', 'rg', 'kind', 'artifacts'): continue
        s = json.dumps(val)
        for o in orph:
            if k != o and ('"%s"' % o in s or '%s' % o == val): ment[o].append('%s.%s' % (k[:40], key))
for o in orph:
    d = n.get(o, {})
    print('%-5s %-11s %-62s named-by: %s' % (d.get('reachable'), d.get('status'), o[:62], ', '.join(ment[o][:3]) or 'nothing'))
PY
echo SEM-DONE
