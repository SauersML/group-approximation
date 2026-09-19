# Independent re-check of every solver-free certificate for the BMW census in degrees (3,3), (4,3), (4,4), (5,3),
# and of coverage: every class not certified reducible has a checked certificate.
# Written from the certificate FORMAT descriptions only; it imports nothing from the searching or checking scripts
# of earlier lanes, and uses no SAT solver.  Inputs are read from the census JSON files and the certificate files.
#   usage: python3 recheck.py ROOT [ROOT2 ...]      (each file is looked up in the roots in order)
import sys, json, gzip, re, os
ROOTS = sys.argv[1:] or ['.']
CEN = 'experiments/bmw-census-left-orders-2026-09-17/census_%s.json'
PATS = ['30_30', '31_30', '31_31', '40_30', '41_30', '41_31', '42_30', '42_31',
        '40_40', '41_40', '41_41', '42_40', '42_41', '42_42',
        '50_30', '50_31', '51_30', '51_31', '52_30', '52_31']

def find(rel):
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.exists(p): return p
    return None

def openany(p):
    return gzip.open(p, 'rt') if p.endswith('.gz') else open(p)

# ---------------------------------------------------------------- the group of one class
class BMW:
    """Letters are ('h', a) for a in range(m) and ('v', b) for b in range(n).  A census square
    [[h, v], [v2, h2]] is the relation h v = v2 h2.  Inverses: h^-1 = ('h', iA[h]), v^-1 = ('v', iB[v])."""
    def __init__(s, D, rep):
        s.m, s.n, s.iA, s.iB = D['m'], D['n'], D['iA'], D['iB']
        assert len(s.iA) == s.m and len(s.iB) == s.n
        assert all(s.iA[s.iA[a]] == a for a in range(s.m)) and all(s.iB[s.iB[b]] == b for b in range(s.n))
        s.sq = {}
        for (h, v), (v2, h2) in rep:
            assert (h, v) not in s.sq
            s.sq[(h, v)] = (v2, h2)
        assert len(s.sq) == s.m * s.n
        # the squares must be a bijection on pairs (every (v2,h2) occurs once): the BMW (VH) condition
        assert len(set(s.sq.values())) == s.m * s.n
    def inv(s, c):
        return ('h', s.iA[c[1]]) if c[0] == 'h' else ('v', s.iB[c[1]])
    # --- algorithm 1: generic rewriting to an irreducible word (any redex, leftmost first)
    def rewrite(s, w):
        w = list(w)
        i = 0
        while i < len(w) - 1:
            p, q = w[i], w[i + 1]
            if q == s.inv(p):
                del w[i:i + 2]; i = max(i - 1, 0); continue
            if p[0] == 'h' and q[0] == 'v':
                v2, h2 = s.sq[(p[1], q[1])]
                w[i], w[i + 1] = ('v', v2), ('h', h2); i = max(i - 1, 0); continue
            i += 1
        return tuple(w)
    # --- algorithm 2: normal form (V, H) built letter by letter
    def nf(s, w):
        V, H = [], []
        for c in w:
            if c[0] == 'h':
                if H and H[-1] == s.iA[c[1]]: H.pop()
                else: H.append(c[1])
            else:
                v = c[1]
                for i in range(len(H) - 1, -1, -1):
                    v, H[i] = s.sq[(H[i], v)]
                for i in range(len(H) - 1):
                    assert H[i + 1] != s.iA[H[i]], 'pushing broke reducedness'
                if V and V[-1] == s.iB[v]: V.pop()
                else: V.append(v)
        return (tuple(V), tuple(H))
    def word(s, g):
        return tuple(('v', x) for x in g[0]) + tuple(('h', x) for x in g[1])
    def invw(s, w):
        return tuple(s.inv(c) for c in reversed(w))
    def check_confluence(s):
        """Newman: the system  c c^-1 -> 1,  h v -> v2 h2  terminates (length, then number of h-before-v pairs,
        drop).  Its only critical overlaps are  h h^-1 v  and  h v v^-1 ; both must resolve."""
        for h in range(s.m):
            for v in range(s.n):
                a = s.inv(('h', h))
                v3, h3 = s.sq[(a[1], v)]
                # h (h^-1 v) -> h v3 h3  must reduce to  v
                assert s.rewrite([('h', h), ('v', v3), ('h', h3)]) == (('v', v),)
                v2, h2 = s.sq[(h, v)]
                # (h v) v^-1 -> v2 h2 v^-1  must reduce to  h
                assert s.rewrite([('v', v2), ('h', h2), s.inv(('v', v))]) == (('h', h),)
    def even(s, g):
        return len(g[0]) % 2 == 0 and len(g[1]) % 2 == 0

def load_class(pat, idx, cache={}):
    if pat not in cache:
        cache[pat] = json.load(open(find(CEN % pat)))
    D = cache[pat]
    G = BMW(D, D['reps'][idx])
    G.check_confluence()
    return G

TOK = re.compile(r'([vh])(\d)')
def parse_lp(s):
    """'v0v1h2h1' -> word; also accepts '' for the identity word."""
    assert TOK.sub('', s) == '', s
    return tuple((a, int(b)) for a, b in TOK.findall(s))
def parse_bar(s):
    """'v03|h12' -> v0 v3 h1 h2."""
    a, b = s.split('|')
    assert a[0] == 'v' and b[0] == 'h'
    return tuple(('v', int(x)) for x in a[1:]) + tuple(('h', int(x)) for x in b[1:])

# ---------------------------------------------------------------- certificate checkers
class Bad(Exception): pass
def need(c, msg):
    if not c: raise Bad(msg)

def kelt(G, w):
    """Normal form of a word that must name an element of Gamma^+ - {1}."""
    g = G.nf(w)
    need(g != ((), ()), 'trivial element %r' % (w,))
    need(G.even(g), 'element outside Gamma^+ %r' % (w,))
    return g

def mulnf(G, *gs):
    return G.nf(sum((G.word(g) for g in gs), ()))

def check_tree(G, T, parse, assumed=()):
    """Cone-propagation tree.  ['split', g, T1, T2]: g in Gamma^+ - {1}; T1 assumes g in P, T2 assumes g^-1 in P.
    ['leaf', [x, y], steps]: each step [z, u, w] needs u, w already in the set and z = u w (z added); at the end
    x, y are in the set and x y = 1.  Returns the number of leaves."""
    if T[0] == 'split':
        need(len(T) == 4, 'split arity')
        g = kelt(G, parse(T[1]))
        gi = G.nf(G.invw(G.word(g)))
        return check_tree(G, T[2], parse, assumed + (g,)) + check_tree(G, T[3], parse, assumed + (gi,))
    need(T[0] == 'leaf' and len(T) == 3, 'leaf shape')
    Q = set(assumed)
    for st in T[2]:
        need(len(st) == 3, 'step arity')
        z, u, w = (G.nf(parse(t)) for t in st)
        need(u in Q and w in Q, 'step factor not in set')
        need(mulnf(G, u, w) == z, 'wrong product')
        kelt(G, G.word(z))
        Q.add(z)
    x, y = (G.nf(parse(t)) for t in T[1])
    need(x in Q and y in Q, 'end not in set')
    need(mulnf(G, x, y) == ((), ()), 'end is not a contradiction')
    return 1

def check_lemmas(G, rec):
    """Cone lemmas S_i (not a subset of P), proved in order; the last must have S = {}."""
    E = [kelt(G, parse_lp(t)) for t in rec['els']]
    S = []
    for i, L in enumerate(rec['lemmas']):
        Si = set(E[k] for k in L['S'])
        Q = set(Si)
        for st in L['steps']:
            if st[0] == 'sq':
                z, u = E[st[1]], E[st[2]]
                need(u in Q, 'sq: u not in set'); need(mulnf(G, z, z) == u, 'sq: z z != u')
                Q.add(z)
            elif st[0] == 'L':
                j, z = st[1], E[st[2]]
                need(isinstance(j, int) and 0 <= j < i, 'L: bad lemma index')
                out = [s for s in S[j] if s not in Q]
                need(len(out) == 1, 'L: not exactly one element outside')
                need(G.nf(G.invw(G.word(out[0]))) == z, 'L: z is not s^-1')
                Q.add(z)
            else:
                z, u, w = E[st[0]], E[st[1]], E[st[2]]
                need(u in Q and w in Q, 'product factor not in set'); need(mulnf(G, u, w) == z, 'wrong product')
                Q.add(z)
        end = L['end']
        if end[0] == 'L':
            j = end[1]
            need(isinstance(j, int) and 0 <= j < i and S[j] <= Q, 'L-end fails')
        else:
            x, y = E[end[0]], E[end[1]]
            need(x in Q and y in Q and mulnf(G, x, y) == ((), ()), 'end is not a contradiction')
        S.append(Si)
    need(S and S[-1] == set(), 'last lemma not empty')
    return len(S)

def inverts(G, a, b):
    """a b a^-1 = b^-1."""
    return mulnf(G, a, b, G.nf(G.invw(G.word(a))), b) == ((), ())

def power(G, r, k):
    w = G.word(r) if k > 0 else G.invw(G.word(r))
    return G.nf(w * abs(k))

def rstep(G, x, y, r, E=12, F=40):
    """x = r^e, y = r^f with 1 <= |e| < |f|  (then |x| < |y| in any left order of a torsion-free group)."""
    pe = {power(G, r, e): e for e in list(range(1, E + 1)) + list(range(-E, 0))}
    if x not in pe: return None
    e = pe[x]
    for f in list(range(abs(e) + 1, F + 1)) + list(range(-F, -abs(e))):
        if power(G, r, f) == y: return (e, f)
    return None

def check_chain(G, xs, roots=None):
    """Cycle x_0 -> x_1 -> ... -> x_0: each step is (K) x_{i+1} inverts x_i, or (R) a power step with root
    roots[i] (default x_i).  All x_i in Gamma^+ - {1}; at least one (K).  Returns (#K, #R)."""
    X = [kelt(G, w) for w in xs]
    nk = nr = 0
    for i in range(len(X)):
        a, b = X[i], X[(i + 1) % len(X)]
        if inverts(G, b, a):
            nk += 1; continue
        r = G.nf(roots[str(i)]) if roots and str(i) in roots else a
        need(rstep(G, a, b, r) is not None, 'step %d is neither (K) nor (R)' % i)
        nr += 1
    need(nk >= 1, 'no (K) step')
    return nk, nr

# ---------------------------------------------------------------- reducibility: finite automaton images
def finite_order(G, horizontal, cap=4000):
    """Order of the image of <A> in Aut(T_V) (horizontal) or of <B> in Aut(T_H), or None if more than cap.
    Letter a acts on the first input letter x by the square and continues with the section a'.  R is the set of
    distinct elements of length <= k (closed under sections); the group is finite iff R . gens adds nothing."""
    if horizontal:
        L, I = G.m, G.n
        tr = {(a, x): G.sq[(a, x)] for a in range(L) for x in range(I)}          # (output v', section h')
    else:
        # h v = v2 h2  <=>  v2^-1 h = h2 v^-1 : state v2^-1, input h -> output h2, section v^-1
        tr = {}
        for (h, v), (v2, h2) in G.sq.items(): tr[(G.iB[v2], h)] = (h2, G.iB[v])
        L, I = G.n, G.m
    # R: list of (perm, succ) with succ indices into R; element 0 = identity
    R = [(tuple(range(I)), (0,) * I)]
    while True:
        nR = len(R)
        # candidate states: R itself, then pairs (r, a) meaning "apply a, then r"
        pid = {}
        def P(r, a):
            if (r, a) not in pid: pid[(r, a)] = nR + len(pid)
            return pid[(r, a)]
        perm = [p for p, _ in R]; succ = [list(sc) for _, sc in R]
        todo = [(r, a) for r in range(nR) for a in range(L)]
        for r, a in todo: P(r, a)
        k = 0
        items = list(pid.items())
        while k < len(items):
            (r, a), i = items[k]; k += 1
            pr, sr = R[r]
            pm = tuple(pr[tr[(a, x)][0]] for x in range(I))
            sc = [P(sr[tr[(a, x)][0]], tr[(a, x)][1]) for x in range(I)]
            if len(pid) > len(items): items = list(pid.items())
            while len(perm) <= i: perm.append(None); succ.append(None)
            perm[i], succ[i] = pm, sc
        N = len(perm)
        # Moore refinement
        cls = {}; part = [cls.setdefault(p, len(cls)) for p in perm]
        while True:
            sig = {}; new = [sig.setdefault((part[i], tuple(part[j] for j in succ[i])), len(sig)) for i in range(N)]
            if len(sig) == len(set(part)): break
            part = new
        ncls = len(set(part))
        if ncls == nR: return nR
        if ncls > cap: return None
        # new R: one representative per class, identity first
        rep = {}
        for i in range(N): rep.setdefault(part[i], i)
        order = sorted(rep.values(), key=lambda i: (part[i] != part[0], i))
        num = {part[i]: t for t, i in enumerate(order)}
        R = [(perm[i], tuple(num[part[j]] for j in succ[i])) for i in order]

# ---------------------------------------------------------------- driver
import glob, random, time
PATRE = re.compile(r'(\d\d_\d\d)')
def selftest(G, rng, k=60):
    """The two normal-form algorithms agree on random words (letter-by-letter vs generic rewriting)."""
    letters = [('h', a) for a in range(G.m)] + [('v', b) for b in range(G.n)]
    for _ in range(k):
        w = [rng.choice(letters) for _ in range(rng.randrange(1, 15))]
        assert G.rewrite(w) == G.word(G.nf(w))

def certificates():
    """Yield (pattern, class, kind, source, payload) for every certificate file found under the roots."""
    seen = set()
    def files(pattern):
        out = []
        for r in ROOTS:
            for p in sorted(glob.glob(os.path.join(r, pattern))):
                rel = os.path.relpath(p, r)
                if rel not in seen: seen.add(rel); out.append((rel, p))
        return out
    for d in ['bmw-klein-chains-2026-09-17', 'bmw-klein-chains-transposed-2026-09-17', 'bmw-klein-frames-2026-09-18']:
        for rel, p in files('experiments/%s/chains_*.json' % d):
            pat = PATRE.search(os.path.basename(p)).group(1)
            for c, v in json.load(open(p)).items():
                yield pat, int(c), 'chain', rel, v
    for rel, p in files('experiments/bmw-klein-free-2026-09-18/tree_*.json'):
        pat = PATRE.search(os.path.basename(p)).group(1)
        rec = json.loads([l for l in open(p) if l.startswith('{')][-1])
        yield pat, rec['cls'], 'tree', rel, rec['tree']
    for rel, p in files('experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz'):
        for l in openany(p):
            rec = json.loads(l); yield rec['pat'], rec['cls'], 'tree', rel, rec['tree']
    for rel, p in files('experiments/bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz'):
        for l in openany(p):
            rec = json.loads(l); yield rec['pat'], rec['cls'], 'lemmas', rel, rec

def main():
    t0 = time.time(); rng = random.Random(1)
    ok = {}; nbad = 0; bysrc = {}
    oklog = os.environ.get('RECHECK_OKLOG')   # coverage-only rerun: take the checked set from an earlier full log
    if oklog:
        for l in open(oklog):
            mo = re.match(r'(OK |BAD) (\d\d_\d\d) #(\d+) ', l)
            if mo and mo.group(1) == 'OK ': ok.setdefault((mo.group(2), int(mo.group(3))), []).append(oklog)
            elif mo: nbad += 1
        print('checked set read from %s: %d classes, %d rejected' % (oklog, len(ok), nbad))
    for pat, c, kind, src, pay in ([] if oklog else certificates()):
        G = load_class(pat, c); selftest(G, rng)
        try:
            if kind == 'chain':
                if isinstance(pay, dict): res = check_chain(G, [parse_bar(w) for w in pay['chain']],
                                                            {k: parse_bar(w) for k, w in pay.get('roots', {}).items()})
                else: res = check_chain(G, [parse_bar(w) for w in pay])
                info = 'K=%d R=%d' % res
            elif kind == 'tree':
                info = 'leaves=%d' % check_tree(G, pay, parse_lp)
            else:
                info = 'lemmas=%d' % check_lemmas(G, pay)
            ok.setdefault((pat, c), []).append(src)
            bysrc[src] = bysrc.get(src, 0) + 1
            print('OK  %s #%d %s %s  [%s]' % (pat, c, kind, info, src), flush=True)
        except Bad as e:
            nbad += 1; print('BAD %s #%d %s %s  [%s]' % (pat, c, kind, e, src), flush=True)
    print('certificate files:'); [print('  %5d OK  %s' % (n, s)) for s, n in sorted(bysrc.items())]
    print('certificates: %d classes with a checked certificate, %d rejected' % (len(ok), nbad))
    # coverage against the census
    tot = dict(classes=0, reducible=0, cand=0, covered=0)
    missing = []
    print('pattern classes reducible(both images finite) candidates covered')
    sel = os.environ.get('RECHECK_PATS')
    pats = sel.split(',') if sel else PATS
    for pat in pats:
        D = json.load(open(find(CEN % pat))); nc = len(D['reps'])
        outp = find('experiments/bmw-census-left-orders-2026-09-17/out_%s.jsonl' % pat)
        old = {r['idx']: r for r in map(json.loads, open(outp))} if outp else {}
        red = cand = cov = 0
        for i in range(nc):
            G = load_class(pat, i)
            fh = finite_order(G, True); fv = finite_order(G, False) if fh is not None else None
            if old: assert fh == old[i]['finH'] and (fh is None or fv == old[i]['finV']), (pat, i, fh, fv, old[i])
            if fh is not None and fv is not None: red += 1; continue
            cand += 1
            if (pat, i) in ok: cov += 1
            else: missing.append((pat, i))
        print('%s %5d %5d %5d %5d' % (pat, nc, red, cand, cov), flush=True)
        for k, x in zip(['classes', 'reducible', 'cand', 'covered'], [nc, red, cand, cov]): tot[k] += x
    print('total', tot)
    print('uncovered candidates at cap 4000:', missing)
    # second pass: an uncovered candidate may still be certified reducible at a larger cap
    still = []
    for pat, i in missing:
        G = load_class(pat, i)
        fh = finite_order(G, True, 60000); fv = finite_order(G, False, 60000) if fh is not None else None
        print('  %s #%d at cap 60000: finH=%s finV=%s' % (pat, i, fh, fv), flush=True)
        if fh is None or fv is None: still.append((pat, i))
        else: tot['reducible'] += 1; tot['cand'] -= 1
    missing = still
    print('uncovered candidates:', missing)
    print('summary: %d certificates rejected; %d of %d irreducibility candidates covered; %.0f s'
          % (nbad, tot['covered'], tot['cand'], time.time() - t0))

if __name__ == '__main__':
    main()
