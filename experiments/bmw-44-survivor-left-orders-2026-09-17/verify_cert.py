# Independent checker for a non-left-orderability certificate (cert_<class>.json) of Gamma^+ for a class
# of census_40_40.json.  usage: verify_cert.py census_40_40.json cert_<class>.json
# Uses only the census file (the 16 squares of the class) and the certificate; no code shared with the search.
#  1. checks the 16 squares form a VH-datum with involutive letters and that the rewriting system
#     {xx -> 1, h v -> v' h'} is locally confluent (so normal forms V-word.H-word are unique);
#  2. checks every element is nontrivial and lies in Gamma^+ (even V- and H-length);
#  3. checks every relation a*b = c by rewriting the concatenated word;
#  4. builds the CNF (exactly one of p_g, p_{g^-1}; p_a & p_b -> p_c) and refutes it with
#     three library SAT solvers, and checks a DRUP refutation with a self-contained RUP checker.
import json, sys
D = json.load(open(sys.argv[1]))
C = json.load(open(sys.argv[2]))
CI = C['class']
SQ = {tuple(a): tuple(b) for a, b in D['reps'][CI]}      # (h, v) -> (v', h'):  h v = v' h'
assert sorted(SQ) == [(h, v) for h in range(4) for v in range(4)]
assert sorted(SQ.values()) == [(v, h) for v in range(4) for h in range(4)]   # bijection H x V -> V x H
def nf(word):
    """word: list of ('v'|'h', letter). Rewrite to normal form (V-word, H-word)."""
    w = list(word); changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            (x, a), (y, b) = w[i], w[i + 1]
            if x == y and a == b:
                del w[i:i + 2]; changed = True; break
            if x == 'h' and y == 'v':
                v2, h2 = SQ[(a, b)]; w[i], w[i + 1] = ('v', v2), ('h', h2); changed = True; break
    vs = tuple(a for x, a in w if x == 'v'); hs = tuple(a for x, a in w if x == 'h')
    assert [x for x, _ in w] == ['v'] * len(vs) + ['h'] * len(hs)
    return vs, hs
# local confluence on the two overlap types h h v and h v v (letters are involutions)
for h in range(4):
    for v in range(4):
        v2, h2 = SQ[(h, v)]
        assert nf([('h', h), ('v', v2), ('h', h2)]) == ((v,), ()), (h, v)      # h (h v2 h2) = v
        assert nf([('v', v2), ('h', h2), ('v', v)]) == ((), (h,)), (h, v)      # (v2 h2) v = h v v
def parse(s):
    a, b = s.split('|')
    return tuple(int(c) for c in a[1::2]), tuple(int(c) for c in b[1::2])
def word(g): return [('v', a) for a in g[0]] + [('h', a) for a in g[1]]
def mul(g, k): return nf(word(g) + word(k))
def inv(g): return nf([('h', a) for a in reversed(g[1])] + [('v', a) for a in reversed(g[0])])
E = {int(k): parse(s) for k, s in C['elements'].items()}
for i, g in E.items():
    assert g != ((), ()) and nf(word(g)) == g, i
    assert len(g[0]) % 2 == 0 and len(g[1]) % 2 == 0, i
    assert mul(g, g) != ((), ()), i
for p, q, k in C['relations']:
    assert mul(E[p], E[q]) == (E[k] if k else ((), ())), (p, q, k)
# CNF over the closure of the element set under inversion
els = sorted(set(E.values()) | {inv(g) for g in E.values()})
var = {g: i + 1 for i, g in enumerate(els)}
cnf = []
for g in els:
    j, k = var[g], var[inv(g)]
    assert j != k
    if j < k: cnf += [[j, k], [-j, -k]]
for p, q, k in C['relations']:
    cnf.append([-var[E[p]], -var[E[q]]] + ([var[E[k]]] if k else []))
def propagate(db, assign):
    """unit propagation to fixpoint; returns False on conflict."""
    changed = True
    while changed:
        changed = False
        for c in db:
            if any(assign.get(abs(l)) == (l > 0) for l in c): continue
            rest = [l for l in c if abs(l) not in assign]
            if not rest: return False
            if len(rest) == 1: assign[abs(rest[0])] = rest[0] > 0; changed = True
    return True
def rup_check(cnf, proof):
    """Check a DRUP refutation by reverse unit propagation (deletions ignored: still sound)."""
    db = [sorted(set(c)) for c in cnf]              # a*a = c gives a clause with a repeated literal
    for line in proof:
        lits = [int(x) for x in line.split()]
        assert lits[-1] == 0; lits = lits[:-1]
        assign = {abs(l): l < 0 for l in lits}
        if propagate(db, assign): return False          # lemma not RUP
        if not lits: return True                        # empty clause derived
        db.append(lits)
    return False
sys.setrecursionlimit(10000)
print('class', CI, 'generators', C.get('generators'), flush=True)
print('elements', len(E), 'with inverses', len(els), 'relations', len(C['relations']), 'clauses', len(cnf), flush=True)
try:
    from pysat.solvers import Glucose4, Minisat22, Cadical153
    for S in (Glucose4, Minisat22, Cadical153):
        with S(bootstrap_with=cnf) as s: print(S.__name__, 'SAT' if s.solve() else 'UNSAT', flush=True)
except ImportError:
    pass
from pysat.solvers import Glucose4
with Glucose4(bootstrap_with=cnf, with_proof=True) as g:
    assert not g.solve(); proof = [l for l in g.get_proof() if not l.startswith('d')]
print('DRUP proof lines', len(proof), 'self-checked by reverse unit propagation:', rup_check(cnf, proof), flush=True)
