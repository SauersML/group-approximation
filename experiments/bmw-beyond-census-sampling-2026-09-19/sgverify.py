# sgverify.py cert.json : independent check of a subgroup-cone certificate from sgcert.py, in any degrees.
# Uses only the certificate (squares, inverse maps, elements, relations, lemmas); no code shared with the
# search. Generalizes ../bmw-44-survivor-left-orders-2026-09-17/verify_cert.py.
#  1. the squares are a bijection H x V -> V x H, and {x x^-1 -> 1, h v -> v' h'} is locally confluent
#     (it terminates, so normal forms V-word.H-word are unique);
#  2. every element is a nontrivial normal form of even V- and H-length (so in Gamma^+), not an involution;
#  3. every relation p*q = c holds, by rewriting the concatenated word;
#  4. CNF: "exactly one of p_g, p_{g^-1}" over the inversion closure, "p_a & p_b -> p_c" per relation;
#     every lemma is RUP (own unit propagation), the last is the empty clause; and three library solvers
#     say UNSAT. A positive cone of a left order of Gamma^+ would satisfy the CNF, so none exists.
import json, sys
C = json.load(open(sys.argv[1])); iA, iB = C['iA'], C['iB']; m, n = len(iA), len(iB)
SQ = {tuple(a): tuple(b) for a, b in C['sq']}
assert sorted(SQ) == [(h, v) for h in range(m) for v in range(n)]
assert sorted(SQ.values()) == [(v, h) for v in range(n) for h in range(m)]
assert all(iA[iA[x]] == x for x in range(m)) and all(iB[iB[x]] == x for x in range(n))
INV = {'h': iA, 'v': iB}
def nf(word):
    w = list(word); changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            (x, a), (y, b) = w[i], w[i + 1]
            if x == y and INV[x][a] == b: del w[i:i + 2]; changed = True; break
            if x == 'h' and y == 'v':
                v2, h2 = SQ[(a, b)]; w[i], w[i + 1] = ('v', v2), ('h', h2); changed = True; break
    vs = tuple(a for x, a in w if x == 'v'); hs = tuple(a for x, a in w if x == 'h')
    assert [x for x, _ in w] == ['v'] * len(vs) + ['h'] * len(hs)
    return vs, hs
for h in range(m):                       # critical pairs h^-1 (h v) and (h v) v^-1
    for v in range(n):
        v2, h2 = SQ[(h, v)]
        assert nf([('h', iA[h]), ('v', v2), ('h', h2)]) == ((v,), ()), (h, v)
        assert nf([('v', v2), ('h', h2), ('v', iB[v])]) == ((), (h,)), (h, v)
def parse(s):
    a, b = s.split('|'); return tuple(int(c) for c in a[1::2]), tuple(int(c) for c in b[1::2])
def word(g): return [('v', a) for a in g[0]] + [('h', a) for a in g[1]]
def mul(g, k): return nf(word(g) + word(k))
def inv(g): return nf([('h', iA[a]) for a in reversed(g[1])] + [('v', iB[a]) for a in reversed(g[0])])
E = {int(k): parse(s) for k, s in C['elements'].items()}
for i, g in E.items():
    assert g != ((), ()) and nf(word(g)) == g, i
    assert len(g[0]) % 2 == 0 and len(g[1]) % 2 == 0, i
    assert mul(g, g) != ((), ()), i
for p, q, k in C['relations']:
    assert mul(E[p], E[q]) == (E[k] if k else ((), ())), (p, q, k)
els = sorted(set(E.values()) | {inv(g) for g in E.values()}); var = {g: i + 1 for i, g in enumerate(els)}
cnf = []
for g in els:
    j, k = var[g], var[inv(g)]; assert j != k
    if j < k: cnf += [[j, k], [-j, -k]]
for p, q, k in C['relations']:
    cnf.append(sorted(set([-var[E[p]], -var[E[q]]] + ([var[E[k]]] if k else []))))
def tr(l): return var[E[abs(l)]] * (1 if l > 0 else -1)
lem = [[tr(l) for l in c] for c in C['lemmas']]
def propagate(db, occ, assign):
    """unit propagation to fixpoint over clauses touching assigned variables; False on conflict."""
    todo = list(assign)
    while todo:
        v = todo.pop()
        for ci in occ.get(v, ()):
            c = db[ci]
            if any(assign.get(abs(l)) == (l > 0) for l in c): continue
            rest = [l for l in c if abs(l) not in assign]
            if not rest: return False
            if len(rest) == 1: assign[abs(rest[0])] = rest[0] > 0; todo.append(abs(rest[0]))
    return True
db = [list(c) for c in cnf]; occ = {}
for ci, c in enumerate(db):
    for l in c: occ.setdefault(abs(l), []).append(ci)
units = [c[0] for c in db if len(c) == 1]; ok = False
for c in lem:
    assign = {abs(l): l < 0 for l in c}
    for u in units:
        if abs(u) in assign and assign[abs(u)] != (u > 0): break
        assign[abs(u)] = u > 0
    else:
        if propagate(db, occ, assign): print('lemma not RUP', c); sys.exit(1)
    if not c: ok = True; break
    db.append(list(c)); ci = len(db) - 1
    for l in c: occ.setdefault(abs(l), []).append(ci)
    if len(c) == 1: units.append(c[0])
assert ok, 'no empty clause'
from pysat.solvers import Glucose4, Minisat22, Cadical153
res = []
for S in (Glucose4, Minisat22, Cadical153):
    with S(bootstrap_with=cnf) as s: res.append(s.solve())
assert res == [False] * 3, res
print('OK', C['pat'], 'seed', C['seed'], 'subgroup', C['gens'], 'elements', len(els), 'clauses', len(cnf),
      'lemmas', len(lem), 'RUP True, UNSAT with Glucose4, MiniSat22, CaDiCaL153')
