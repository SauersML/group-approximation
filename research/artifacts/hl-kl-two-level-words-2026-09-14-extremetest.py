#!/usr/bin/env python3
# Model test for kl-holds-when-extreme-height-blocks-have-infinite-order (lane hl-kl-two-level-words).
# Free products of finite groups (S3, Z/4) and Z, exact normal forms. No external packages.
import itertools, random, sys
random.seed(20260914)

def pmul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(len(q)))
def pinv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)
S3 = [tuple(p) for p in itertools.permutations(range(3))]
GROUPS = {
    'S3': dict(elems=S3, mul=pmul, inv=pinv, e=(0, 1, 2), finite=True),
    'Z4': dict(elems=list(range(4)), mul=lambda a, b: (a + b) % 4, inv=lambda a: (-a) % 4, e=0, finite=True),
    'Z':  dict(elems=None, mul=lambda a, b: a + b, inv=lambda a: -a, e=0, finite=False),
}
def rand_nontriv(gname):
    g = GROUPS[gname]
    if g['elems'] is None:
        x = 0
        while x == 0:
            x = random.randint(-3, 3)
        return x
    return random.choice([x for x in g['elems'] if x != g['e']])
def order_is_finite(gname, x):
    return GROUPS[gname]['finite'] or x == GROUPS[gname]['e']

# A syllable is (factor, groupname, element). Factors are hashable labels; groupname fixes the multiplication.
def reduce_word(word):
    st = []
    for (f, gn, x) in word:
        G = GROUPS[gn]
        if x == G['e']:
            continue
        if st and st[-1][0] == f:
            y = G['mul'](st[-1][2], x)
            st.pop()
            if y != G['e']:
                st.append((f, gn, y))
        else:
            st.append((f, gn, x))
    return st
def inv_word(word):
    return [(f, gn, GROUPS[gn]['inv'](x)) for (f, gn, x) in reversed(word)]

def finite_order_by_cyclic_reduction(word):
    w = reduce_word(word)
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        w = reduce_word([w[-1]] + w[:-1])
    if len(w) == 0:
        return True
    if len(w) == 1:
        return order_is_finite(w[0][1], w[0][2])
    return False  # cyclically reduced of length >= 2
def finite_order_by_palindrome(word):
    w = word  # assumed reduced
    L = len(w)
    if L == 0:
        return True
    if L % 2 == 0:
        return False
    for r in range(L // 2):
        a, b = w[r], w[L - 1 - r]
        if a[0] != b[0] or GROUPS[a[1]]['inv'](a[2]) != b[2]:
            return False
    mid = w[L // 2]
    return order_is_finite(mid[1], mid[2])

fails = 0
# ---------------- T3: palindrome criterion vs cyclic reduction ----------------
def rand_reduced_block(nfactors, gnames, L, same_ends):
    # random reduced word in a free product of factors 0..nfactors-1 whose end syllables share a factor
    # (bounded retries; returns None when no such word exists, e.g. L = 2, or L even with two factors)
    for attempt in range(200):
        w = []
        for _ in range(L):
            choices = [x for x in range(nfactors) if not w or x != w[-1][0]]
            f = random.choice(choices)
            gn = gnames[f]
            w.append((f, gn, rand_nontriv(gn)))
        if same_ends and w[0][0] != w[-1][0]:
            continue
        return w
    return None
t3 = 0
for trial in range(4000):
    nf = random.randint(2, 4)
    gnames = [random.choice(['S3', 'Z4', 'Z']) for _ in range(nf)]
    L = random.randint(1, 9)
    w = rand_reduced_block(nf, gnames, L, same_ends=True)
    if w is None:
        continue
    if random.random() < 0.5 and L >= 3:  # force an inverse palindrome around a random middle
        half = w[:L // 2]
        mid = w[L // 2]
        choices = [x for x in range(nf) if x != half[-1][0]] if half else list(range(nf))
        mf = random.choice(choices)
        mid = (mf, gnames[mf], rand_nontriv(gnames[mf]))
        w = half + [mid] + inv_word(half)
        if reduce_word(w) != w:
            continue
    a = finite_order_by_cyclic_reduction(w)
    b = finite_order_by_palindrome(w)
    t3 += 1
    if a != b:
        fails += 1
        print('T3 MISMATCH', w, a, b)
print('T3 palindrome-vs-cyclic-reduction trials=%d failures=%d' % (t3, fails))

# ---------------- T2: stripped infinite order <=> gp(A,u) = A * <u>_inf ----------------
# A = one factor 'A' (group gA), B = one factor 'B' (group gB). u in (A*B) \ A.
t2_inf = t2_fin = t2_fail = 0
for trial in range(3000):
    gA = random.choice(['S3', 'Z4', 'Z'])
    gB = random.choice(['S3', 'Z4', 'Z'])
    L = random.randint(1, 7)
    u = []
    for _ in range(L):
        f = 'A' if (not u or u[-1][0] == 'B') else 'B'
        if not u:
            f = random.choice(['A', 'B'])
        gn = gA if f == 'A' else gB
        u.append((f, gn, rand_nontriv(gn)))
    if all(s[0] == 'A' for s in u):
        continue
    if random.random() < 0.4:
        # make the stripped core an inverse palindrome with a B- or A-middle
        core_len = random.choice([1, 3, 5])
        half = []
        for i in range(core_len // 2):
            f = 'B' if i % 2 == 0 else 'A'
            gn = gB if f == 'B' else gA
            half.append((f, gn, rand_nontriv(gn)))
        mf = 'B' if (core_len // 2) % 2 == 0 else 'A'
        gn = gB if mf == 'B' else gA
        core = half + [(mf, gn, rand_nontriv(gn))] + inv_word(half)
        pre = [('A', gA, rand_nontriv(gA))] if random.random() < 0.5 else []
        post = [('A', gA, rand_nontriv(gA))] if random.random() < 0.5 else []
        u = reduce_word(pre + core + post)
        if all(s[0] == 'A' for s in u):
            continue
    u = reduce_word(u)
    # strip A-syllables at both ends
    x = [u[0]] if u[0][0] == 'A' else []
    xp = [u[-1]] if u[-1][0] == 'A' else []
    core = u[len(x):len(u) - len(xp)]
    assert core and core[0][0] == 'B' and core[-1][0] == 'B'
    fin = finite_order_by_cyclic_reduction(core)
    assert fin == finite_order_by_palindrome(core)
    if not fin:
        t2_inf += 1
        # theta: A * <z> -> A * B, z -> u ; random reduced omega must map to a nontrivial element
        for rep in range(25):
            m = random.randint(1, 4)
            omega_img = []
            for i in range(m):
                if i > 0 or random.random() < 0.5:
                    omega_img.append(('A', gA, rand_nontriv(gA)))
                e = random.choice([-2, -1, 1, 2])
                piece = u if e > 0 else inv_word(u)
                omega_img += piece * abs(e)
            if random.random() < 0.5:
                omega_img.append(('A', gA, rand_nontriv(gA)))
            if reduce_word(omega_img) == []:
                t2_fail += 1
                print('T2 RELATION FOUND FOR INFINITE-ORDER CORE', u)
    else:
        t2_fin += 1
        # sharpness: omega = (x^-1 z x'^-1)^k maps to core^k; find k with core^k = 1
        k = None
        for kk in range(1, 25):
            if reduce_word(core * kk) == []:
                k = kk
                break
        if k is None:
            if any(not GROUPS[s[1]]['finite'] for s in core):
                t2_fail += 1
                print('T2 no finite power for finite-order core', core)
            continue
        rel_img = reduce_word((inv_word(x) + u + inv_word(xp)) * k)
        omega_nontrivial = True  # (x^-1 z x'^-1)^k is a nonempty reduced word in A * <z>, k >= 1
        if rel_img != [] or not omega_nontrivial:
            t2_fail += 1
            print('T2 SHARPNESS FAILED', u, k)
print('T2 stripped-core trials: infinite=%d finite=%d failures=%d' % (t2_inf, t2_fin, t2_fail))
fails += t2_fail

# ---------------- T1: canonical cut and form (1) decomposition ----------------
def canonical_blocks(coeffs, ks, gname):
    n = len(coeffs)
    assert sum(ks) == 1
    h = [0] * n
    for j in range(1, n):
        h[j] = h[j - 1] + ks[j - 1]
    M = max(h)
    valid = []
    for j0 in range(n):
        hh = [(h[(j0 + q) % n] + (1 if j0 + q >= n else 0)) for q in range(n)]
        if all(x <= h[j0] for x in hh):
            valid.append(j0)
    assert len(valid) == 1, ('valid cuts', valid)
    j0 = valid[0]
    assert j0 == h.index(M)
    rc = coeffs[j0:] + coeffs[:j0]
    rk = ks[j0:] + ks[:j0]
    hr = [0] * n
    for j in range(1, n):
        hr[j] = hr[j - 1] + rk[j - 1]
    idx = [-x for x in hr]
    assert idx[0] == 0 and min(idx) >= 0
    s = max(idx)
    return rc, rk, idx, s
def decompose(idx, s):
    n = len(idx)
    marks = [('B' if i == 0 else ('T' if i == s else None)) for i in idx]
    runs = []
    for j, mk in enumerate(marks):
        if mk is None:
            continue
        if runs and runs[-1][0] == mk:
            runs[-1][1].append(j)
        else:
            runs.append([mk, [j]])
    return runs
t1 = t1_fail = 0
for trial in range(3000):
    gname = random.choice(['S3', 'Z4', 'Z'])
    n = random.randint(2, 9)
    while True:
        ks = [random.choice([-3, -2, -1, 1, 2, 3]) for _ in range(n)]
        d = 1 - sum(ks[:-1])
        if d != 0 and abs(d) <= 6:
            ks[-1] = d
            break
    coeffs = [rand_nontriv(gname) for _ in range(n)]
    rc, rk, idx, s = canonical_blocks(coeffs, ks, gname)
    if s == 0:
        continue
    runs = decompose(idx, s)
    assert runs[0][0] == 'B' and 0 in runs[0][1]
    # regions: b_i from after previous T-run's last mark (or 0) to last mark of B-run_i;
    # h_i from after that to last mark of T-run_i; c = rest
    v = [(idx[j], gname, rc[j]) for j in range(n)]  # syllables g_j^[i_j]
    pieces = []
    pos = 0
    ok = True
    i = 0
    while i < len(runs):
        if runs[i][0] == 'B' and i + 1 < len(runs):
            bend = runs[i][1][-1] + 1
            b = v[pos:bend]
            tend = runs[i + 1][1][-1] + 1
            hseg = v[bend:tend]
            if not (min(x[0] for x in b) == 0 and max(x[0] for x in b) <= s - 1):
                ok = False
            if not (min(x[0] for x in hseg) >= 1 and max(x[0] for x in hseg) == s):
                ok = False
            pieces += b + hseg
            pos = tend
            i += 2
        else:
            break
    c = v[pos:]
    if c and max(x[0] for x in c) > s - 1:
        ok = False
    pieces += c
    if pieces != v:
        ok = False
    # consecutive syllables of v lie in different factors (reduced word)
    if any(v[j][0] == v[j + 1][0] for j in range(n - 1)):
        ok = False
    # the trailing B-run (if any) must lie inside c
    if runs[-1][0] == 'B' and len(runs) % 2 == 1 and len(runs) > 1:
        if runs[-1][1][0] < pos:
            ok = False
    t1 += 1
    if not ok:
        t1_fail += 1
        print('T1 FAIL', coeffs, ks, idx, runs)
print('T1 canonical-cut decomposition trials=%d failures=%d' % (t1, t1_fail))
fails += t1_fail

# ---------------- T4: sign-index-two words: constrained blocks are the two sign-change coefficients ----------------
t4 = t4_fail = 0
for trial in range(1500):
    gname = random.choice(['S3', 'Z4', 'Z'])
    p = random.randint(2, 6)
    q = p - 1
    a = [rand_nontriv(gname) for _ in range(p - 1)]
    nn = [rand_nontriv(gname) for _ in range(q - 1)]
    y = rand_nontriv(gname)
    x = rand_nontriv(gname)
    # w = t a_1 t ... a_(p-1) t  y  t^-1 n_1 t^-1 ... n_(q-1) t^-1  x   (cyclic)
    coeffs = a + [y] + nn + [x]
    ks = [1] * (p - 1) + [1] + [-1] * (q - 1) + [-1]
    # letters before a_1: one t; rotate so each coefficient is followed by its letter
    # cyclic word: t a_1 t a_2 ... t a_(p-1) t y t^-1 n_1 ... t^-1 n_(q-1) t^-1 x
    # coefficient-then-letter form: a_1 t a_2 t ... a_(p-1) t y t^-1 n_1 t^-1 ... n_(q-1) t^-1 x t
    ks = [1] * (p - 1) + [-1] + [-1] * (q - 1) + [1]
    if sum(ks) != 1:
        t4_fail += 1
        print('T4 degree error', p, q, ks)
        continue
    tags = ['a'] * (p - 1) + ['y'] + ['n'] * (q - 1) + ['x']
    tagged = list(zip(tags, coeffs))
    rc, rk, idx, s = canonical_blocks(tagged, ks, gname)
    runs = decompose(idx, s)
    constrained = []
    for r_i, (mk, js) in enumerate(runs):
        final_bottom = (mk == 'B' and r_i == len(runs) - 1 and len(runs) > 1 and runs[r_i - 1][0] == 'T')
        if final_bottom:
            continue
        constrained.append(tuple(rc[j][0] for j in range(js[0], js[-1] + 1)))
    t4 += 1
    if sorted(constrained) != [('x',), ('y',)]:
        t4_fail += 1
        print('T4 FAIL', p, q, idx, runs, constrained)
print('T4 sign-index-two constrained blocks trials=%d failures=%d' % (t4, t4_fail))
fails += t4_fail
print('TOTAL_FAILURES', fails)
