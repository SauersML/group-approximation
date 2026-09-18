# Independent cross-check of chains for verify_klein2.py: recomputes every step with a different
# normal-form algorithm (push each letter through the H-suffix using the square table, as in kpure2.py),
# and checks (K) a b a^-1 = b^-1, or (P) a = b^e (|e| >= 2), or (R) b = r^e, a = r^f, 1 <= |e| < |f|.
# usage: crosscheck2.py census.json chains.json
import sys, json
D = json.load(open(sys.argv[1])); CH = json.load(open(sys.argv[2]))
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
def winv(w, inv): return tuple(inv[c] for c in reversed(w))
def parse(s):
    a, b = s.split('|'); return tuple(int(c) for c in a[1:]), tuple(int(c) for c in b[1:])
for c, ch in CH.items():
    HV = {tuple(a): tuple(b) for a, b in D['reps'][int(c)]}
    def mul(g1, g2):
        vs = list(g1[0]); h = list(g1[1])
        for v in g2[0]:
            for i in range(len(h) - 1, -1, -1): v, h[i] = HV[(h[i], v)]
            if vs and vs[-1] == iB[v]: vs.pop()
            else: vs.append(v)
        for x in g2[1]:
            if h and h[-1] == iA[x]: h.pop()
            else: h.append(x)
        return (tuple(vs), tuple(h))
    def inv(g): return mul(((), winv(g[1], iA)), (winv(g[0], iB), ()))
    def pw(g, e):
        r = ((), ()); x = g if e > 0 else inv(g)
        for _ in range(abs(e)): r = mul(r, x)
        return r
    roots = ch.get('roots', {}) if isinstance(ch, dict) else {}
    X = [parse(s) for s in (ch['chain'] if isinstance(ch, dict) else ch)]
    K = 0
    for i in range(len(X)):
        b, a = X[i], X[(i + 1) % len(X)]
        assert b != ((), ()) and all(len(t) % 2 == 0 for t in b)
        if mul(mul(a, b), inv(a)) == inv(b): K += 1; continue
        if str(i) in roots:
            r = parse(roots[str(i)]); assert all(len(t) % 2 == 0 for t in r)
            E = lambda z: [e for k in range(1, 13) for e in (k, -k) if pw(r, e) == z]
            assert E(b) and E(a) and abs(E(b)[0]) < abs(E(a)[0]), (c, i); continue
        assert any(pw(b, e) == a for k in range(2, 13) for e in (k, -k)), (c, i)
    assert K >= 1
    print('class', c, 'ok:', len(X), 'steps,', K, 'inverting')
