# Independent checker for cone-lemma certificates (lrat2cone.py output). Uses only the census squares
# and its own rewriting normal form: the normal form, parse and critical-pair code is that of
# verify_cone.py (w10-107), copied.  Nothing from lo_census, ctree or the SAT solver is used.
# A certificate is a list of lemmas.  Lemma i is a finite set S_i of nontrivial elements of Gamma^+
# with the claim "S_i is not contained in P", for every positive cone P of a left order on Gamma^+.
# Its proof starts from Q = S_i and runs steps, each adding one element known to lie in P:
#   [z, u, w]    u, w in Q and z = u w in Gamma                       (P P in P)
#   ["sq", z, u] u in Q and u = z z; z is in Gamma^+ - {1}, so z in P or z^{-1} in P, and z^{-1} in P
#                would give u^{-1} = z^{-1} z^{-1} in P
#   ["L", j, z]  j < i, all of S_j but one element s lies in Q, z = s^{-1}   (lemma j: s not in P;
#                s in Gamma^+ - {1}, so s^{-1} in P)
# and ends with [x, y] (x, y in Q, x y = 1) or ["L", j] (S_j in Q): a contradiction with lemma j or
# with P disjoint from P^{-1}.  The last lemma has S = {}: no positive cone exists, so Gamma^+ is not
# left-orderable.  Elements are indices into the certificate's word table "els".
# usage: verify_lemmas.py cert.json[.gz] ...   (census file census_<pat>.json read from the census dir)
import sys, json, re, gzip
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
def check(cert):
    D = json.load(open(C + 'census_%s.json' % cert['pat'])); iA, iB = D['iA'], D['iB']
    SQ = {tuple(x): tuple(y) for x, y in D['reps'][cert['cls']]}
    assert len(SQ) == len(iA) * len(iB)
    def parse(s):
        w = [(c, int(x)) for c, x in re.findall(r'([hv])(\d)', s)]
        assert ''.join('%s%d' % p for p in w) == s, s
        return w
    def nf(w):
        w = list(w); i = 0
        while i < len(w) - 1:
            p, q = w[i], w[i + 1]
            if p[0] == q[0] and (iA if p[0] == 'h' else iB)[p[1]] == q[1]:
                del w[i:i + 2]; i = max(i - 1, 0); continue
            if p[0] == 'h' and q[0] == 'v':
                v2, h2 = SQ[(p[1], q[1])]; w[i], w[i + 1] = ('v', v2), ('h', h2); i = max(i - 1, 0); continue
            i += 1
        k = sum(1 for c in w if c[0] == 'v')
        assert all(c[0] == 'v' for c in w[:k]) and all(c[0] == 'h' for c in w[k:])
        return tuple(w)
    for h in range(len(iA)):
        for v in range(len(iB)):
            assert nf([('h', iA[h]), ('h', h), ('v', v)]) == (('v', v),)
            assert nf([('h', h), ('v', v), ('v', iB[v])]) == (('h', h),)
    assert all(iA[iA[x]] == x for x in range(len(iA))) and all(iB[iB[x]] == x for x in range(len(iB)))
    def inv(w): return [(c, (iA if c == 'h' else iB)[x]) for c, x in reversed(w)]
    W = [nf(parse(s)) for s in cert['els']]                    # normal form of each table entry
    for w in W:                                                # every table entry is in Gamma^+ - {1}
        assert w != () and sum(c == 'v' for c, _ in w) % 2 == 0 and sum(c == 'h' for c, _ in w) % 2 == 0
    Lm = cert['lemmas']; S = []; nsteps = 0
    for i, L in enumerate(Lm):
        Si = {W[e] for e in L['S']}; S.append(Si); Q = set(Si)
        for st in L['steps']:
            if st[0] == 'L':
                j, z = st[1], st[2]; assert 0 <= j < i
                out = [s for s in S[j] if s not in Q]
                assert len(out) == 1 and nf(inv(out[0])) == W[z], 'bad lemma step'
            elif st[0] == 'sq':
                z, u = st[1], st[2]; assert W[u] in Q and nf(W[z] + W[z]) == W[u], 'bad square step'
            else:
                z, u, w = st; assert W[u] in Q and W[w] in Q, 'factor not in P'
                assert nf(W[u] + W[w]) == W[z], 'bad product'
            Q.add(W[z]); nsteps += 1
        e = L['end']
        if e[0] == 'L': assert 0 <= e[1] < i and S[e[1]] <= Q, 'no contradiction'
        else: assert W[e[0]] in Q and W[e[1]] in Q and nf(W[e[0]] + W[e[1]]) == (), 'no contradiction'
    assert Lm and not Lm[-1]['S'], 'last lemma is not the empty set'
    return len(Lm), nsteps
if __name__ == '__main__':
    ok = bad = 0
    for f in sys.argv[1:]:
        op = gzip.open if f.endswith('.gz') else open
        for line in op(f, 'rt'):
            cert = json.loads(line)
            try:
                nl, ns = check(cert); ok += 1
                print(cert['pat'], cert['cls'], 'R=%d short=%d' % (cert['R'], cert['short']),
                      'certificate OK: %d lemmas, %d steps; Gamma^+ is not left-orderable' % (nl, ns), flush=True)
            except (AssertionError, IndexError, KeyError) as e:
                bad += 1; print(cert.get('pat'), cert.get('cls'), 'FAILED', e, flush=True)
    print('summary: %d certificates OK, %d failed' % (ok, bad))
    sys.exit(1 if bad or not ok else 0)
