# Translate an LRAT refutation of the census positive-cone CNF (ctree CNF mode) into a cone-lemma
# certificate in group language, read by verify_lemmas.py.  The translation is not trusted: the
# checker re-derives every step from the census squares.
# Variable x means "element x is in P".  A clause C is the lemma "S(C) is not contained in P", where
# S(C) = {x : -x in C} u {x^{-1} : x in C}.  Each LRAT hint clause is unit (or falsified, for the last
# hint) under Q = the elements known to be in P; the forced literal becomes one of:
#   product clause (-a,-b,c), c = a b:  c = a b  |  a^{-1} = b c^{-1}  |  b^{-1} = c^{-1} a
#   product clause (-a,-a,c), c = a a:  c = a a  |  ["sq", a^{-1}, c^{-1}]  (a^{-1} a^{-1} = c^{-1})
#   pair / inverse clauses: no new element (x and x^{-1} both in Q is the contradiction)
#   earlier lemma j: ["L", j, s^{-1}] where s is the one element of S_j outside Q
# usage: lrat2cone.py in.cnf in.lrat pattern class R short > cert.json
import sys, json
cnf, lrat, pat, ci, R, SH = sys.argv[1:7]
wd, iv = {}, {}
for l in open(cnf + '.map'):
    x, w, y = l.split(); wd[int(x)] = w; iv[int(x)] = int(y)
cl = {}; kind = {}
n = 0
for l in open(cnf):
    if l[0] in 'pc': continue
    n += 1; c = [int(t) for t in l.split()[:-1]]; cl[n] = c
    if len(c) == 3: kind[n] = 'prod'
    elif c[0] > 0: kind[n] = 'pair'                        # (x, x^-1)
    elif iv[-c[0]] == -c[1]: kind[n] = 'inv'               # (-x, -x^-1): pair clause or product a a^-1 = 1
    else: raise SystemExit('unexpected clause %d %s' % (n, c))
def S_of(c): return sorted({-x if x < 0 else iv[x] for x in c})
els, eid = [], {}
def E(x):
    if x not in eid: eid[x] = len(els); els.append(wd[x])
    return eid[x]
lemmas, lid = [], {}
for line in open(lrat):
    t = line.split()
    if len(t) < 2 or t[1] == 'd': continue
    i = int(t[0]); z = t.index('0', 1)
    C = [int(x) for x in t[1:z]]; hints = [int(x) for x in t[z + 1:-1]]
    assert all(h > 0 for h in hints), 'RAT hint'
    S = S_of(C); Q = set(S); steps = []; end = None
    for h in hints:
        if h in cl: D = cl[h]; k = kind[h]
        else: D = lemmas[lid[h]]['C']; k = 'lem'
        free = [l for l in D if not (Q.__contains__(-l) if l < 0 else iv[l] in Q)]
        if k == 'lem':
            j = lid[h]; Sj = lemmas[j]['S']; out = [s for s in Sj if s not in Q]
            if not out: end = ['L', j]; break
            assert len(out) == 1; Q.add(iv[out[0]]); steps.append(['L', j, E(iv[out[0]])]); continue
        if k == 'prod':
            a, b, c = -D[0], -D[1], D[2]
            if len(free) == 0 or free == [c]:
                steps.append([E(c), E(a), E(b)]); Q.add(c)
                if len(free) == 0: end = [E(c), E(iv[c])]; break
            elif a == b and free == [-a, -a]: steps.append(['sq', E(iv[a]), E(iv[c])]); Q.add(iv[a])
            elif free == [-a]: steps.append([E(iv[a]), E(b), E(iv[c])]); Q.add(iv[a])
            elif free == [-b]: steps.append([E(iv[b]), E(iv[c]), E(a)]); Q.add(iv[b])
            else: raise SystemExit('hint %d not unit in lemma %d' % (h, i))
            continue
        x = abs(D[0])
        if len(free) == 0: end = [E(x), E(iv[x])]; break
        assert len(free) == 1, 'hint %d not unit' % h        # no new element
    assert end is not None, 'lemma %d: no conflict' % i
    lid[i] = len(lemmas)
    lemmas.append(dict(C=C, S=S, steps=steps, end=end))
    if not C: break
assert lemmas and not lemmas[-1]['C'], 'no empty clause'
out = dict(pat=pat, cls=int(ci), R=int(R), short=int(SH), els=els,
           lemmas=[dict(S=[E(s) for s in L['S']], steps=L['steps'], end=L['end']) for L in lemmas])
print(json.dumps(out, separators=(',', ':')))
