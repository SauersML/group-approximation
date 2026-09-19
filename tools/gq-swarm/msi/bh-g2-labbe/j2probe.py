#!/usr/bin/env python3
"""j2probe.py -- exact bounded probes of scale-D quantum rigidity of Z^2 SFTs (lane bh-g2-labbe, 2026-09-18).

Part A  box languages: Labbe's Omega_U from omega^k windows (as in recog.py); calibrations: checkerboard (rigid),
        Ledrappier (rigid: triangle-permutive), full 2-shift (not rigid: walls).
Part B  two-sided determinism closure C_D (node determinism-closure-certifies-quantum-rigidity): the offsets v whose
        commutation [P_0, P_v] = 0 is certified in the scale-D presentation by determinism alone.
Part C  band walls.  Window K = [0, w) x [0, 2H], w = 2D+2+2m; ends L = (m, H), R = (m+2D+1, H); band = columns
        m+1..m+2D.  Two patterns on K, every s x s box of which is legal (s = 2D+1), that agree on the band and differ
        at L and at R give a 2-dim representation of the window algebra C_D(K) (relations supported in K) with
        [P_L^a, P_R^b] != 0.  So no certificate of that commutation, of ANY degree, uses only relations in K.
        Done for v along e_1 and (transposed language) along e_2.
Single-threaded, stdlib only, exact, no randomness.  Usage: python3 j2probe.py [--smoke]
"""
import sys, time, itertools
from collections import defaultdict
T0 = time.time()
SMOKE = '--smoke' in sys.argv
BUDGET = 50 if SMOKE else 2100
def el(): return time.time() - T0
def log(*a): print('[%7.1fs]' % el(), *a, flush=True)

# ---------------------------------------------------------------- Labbe data (verbatim from recog.py / labbe_lang.py)
tilesU = ['FOJO','FOHL','JMFP','DMFK','HPJP','HPHN','HKFP','HKDP','BOIO','GLEO','GLCL','ALIO',
          'EPGP','EPIP','IPGK','IPIK','IKBM','IKAK','CNIP']
alpha = {0: [[11]], 1: [[8]], 2: [[13]], 3: [[9]], 4: [[17]], 5: [[16]], 6: [[14]], 7: [[15]], 8: [[11, 1]], 9: [[8, 0]], 10: [[18, 5]], 11: [[12, 6]], 12: [[13, 7]], 13: [[13, 4]], 14: [[10, 1]], 15: [[9, 1]], 16: [[17, 3]], 17: [[16, 3]], 18: [[14, 6]], 19: [[15, 7]], 20: [[14, 2]]}
beta = {0: [[4]], 1: [[5]], 2: [[7], [0]], 3: [[4], [1]], 4: [[5], [1]], 5: [[6], [1]], 6: [[7], [1]], 7: [[2], [3]], 8: [[16]], 9: [[17]], 10: [[18]], 11: [[20]], 12: [[18], [8]], 13: [[19], [8]], 14: [[20], [9]], 15: [[11], [15]], 16: [[12], [15]], 17: [[10], [14]], 18: [[13], [15]]}
gamma = {0: [[0]], 1: [[1]], 2: [[2]], 3: [[7]], 4: [[3]], 5: [[4]], 6: [[6]], 7: [[5]], 8: [[10]], 9: [[8]], 10: [[9]], 11: [[11]], 12: [[13]], 13: [[12]], 14: [[16]], 15: [[15]], 16: [[17]], 17: [[18]], 18: [[14]]}
ci = {c: i for i, c in enumerate('RTLB')}
RT = [t[ci['R']] for t in tilesU]; TP = [t[ci['T']] for t in tilesU]
LF = [t[ci['L']] for t in tilesU]; BT = [t[ci['B']] for t in tilesU]

def apply(s, M):  # M: list of columns, each bottom -> top
    out = []
    for col in M:
        imgs = [s[a] for a in col]
        w = len(imgs[0])
        if any(len(im) != w for im in imgs):
            raise ValueError('width')
        for j in range(w):
            c = []
            for im in imgs:
                c.extend(im[j])
            out.append(c)
    if any(len(c) != len(out[0]) for c in out):
        raise ValueError('height')
    return out

def omega(M): return apply(alpha, apply(beta, apply(gamma, M)))
def omega_pow(M, k):
    for _ in range(k): M = omega(M)
    return M
def valid(M):
    W, H = len(M), len(M[0])
    for x in range(W):
        for y in range(H):
            t = M[x][y]
            if x + 1 < W and RT[t] != LF[M[x + 1][y]]: return False
            if y + 1 < H and TP[t] != BT[M[x][y + 1]]: return False
    return True

big = omega_pow([[0]], 7)
L22 = set()
def add22(I, S):
    for x in range(len(I) - 1):
        for y in range(len(I[0]) - 1):
            S.add((I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]))
add22(big, L22)
while True:
    new = set(L22)
    for q in L22: add22(omega([[q[0], q[1]], [q[2], q[3]]]), new)
    if new == L22: break
    L22 = new
Q2 = sorted(L22)
minside = {}
for k in range(1, 9):
    imgs = [omega_pow([[a]], k) for a in range(19)]
    minside[k] = min(min(len(I) for I in imgs), min(len(I[0]) for I in imgs))
IMG = {}
def labbe_windows(w, h):
    """All globally legal w x h patterns of Omega_U, column form (tuple of w columns, each bottom->top)."""
    need = max(w, h) - 1
    k = next(k for k in range(1, 9) if minside[k] >= need)
    if k not in IMG:
        IMG[k] = [omega_pow([[q[0], q[1]], [q[2], q[3]]], k) for q in Q2]
    S = set()
    for Y in IMG[k]:
        W, H = len(Y), len(Y[0])
        for x in range(W - w + 1):
            cols = Y[x:x + w]
            for y in range(H - h + 1):
                S.add(tuple(tuple(c[y:y + h]) for c in cols))
    return S

# ---------------------------------------------------------------- calibration languages (column form)
def lang_checker(s): return set(tuple(tuple((i + j + ph) % 2 for j in range(s)) for i in range(s)) for ph in (0, 1))
def lang_ledrappier(s):
    """x(i,j+1) = x(i,j) + x(i+1,j) mod 2; box patterns = free bottom row + free right column (group shift, all extend)."""
    S = set()
    for bits in itertools.product((0, 1), repeat=2 * s - 1):
        g = [[0] * s for _ in range(s)]
        for i in range(s): g[i][0] = bits[i]
        for j in range(1, s):
            g[s - 1][j] = bits[s - 1 + j]
            for i in range(s - 1): g[i][j] = g[i][j - 1] ^ g[i + 1][j - 1]
        S.add(tuple(tuple(g[i]) for i in range(s)))
    return S
def lang_full(s): return set(tuple(tuple(b[i * s:(i + 1) * s]) for i in range(s)) for b in itertools.product((0, 1), repeat=s * s))
def transpose(P):
    w, h = len(P), len(P[0])
    return tuple(tuple(P[i][j] for i in range(w)) for j in range(h))

# ---------------------------------------------------------------- Part B: determinism closure
def closure(L, s, Rmax):
    D = (s - 1) // 2
    Lst = list(L)
    C = set((a, b) for a in range(-2 * D, 2 * D + 1) for b in range(-2 * D, 2 * D + 1))
    pos = [(i, j) for i in range(s) for j in range(s)]
    cache = {}
    def is_rule(q, Fq):
        key = (q, Fq)
        r = cache.get(key)
        if r is not None: return r
        Fl = sorted(Fq); seen = {}; ok = True
        for P in Lst:
            k = tuple(P[i][j] for (i, j) in Fl); c = P[q[0]][q[1]]
            o = seen.get(k)
            if o is None: seen[k] = c
            elif o != c: ok = False; break
        cache[key] = ok
        return ok
    sweeps = 0
    changed = True
    while changed:
        changed = False; sweeps += 1
        for a in range(-Rmax, Rmax + 1):
            for b in range(-Rmax, Rmax + 1):
                v = (a, b)
                if v in C: continue
                hit = False
                for q in pos:
                    for sg in (1, -1):   # (w): v + f in C ; (z): v - f in C ; f = p - q
                        Fq = frozenset(p for p in pos if p != q and
                                       (a + sg * (p[0] - q[0]), b + sg * (p[1] - q[1])) in C)
                        if is_rule(q, Fq): hit = True; break
                    if hit: break
                if hit:
                    C.add(v); C.add((-a, -b)); changed = True
    return C, sweeps

def show(C, Rmax):
    for b in range(Rmax, -Rmax - 1, -1):
        print('   ' + ''.join('0' if (a, b) == (0, 0) else ('#' if (a, b) in C else '.') for a in range(-Rmax, Rmax + 1)))

# ---------------------------------------------------------------- Part C: locally legal windows and band walls
def to_rows(P): return transpose(P)
def local_levels(Lbox, s, w, hmax, cap, tlimit):
    """Yield (h, list of row-form w x h patterns whose s x s boxes are all legal), h = s..hmax."""
    colext = defaultdict(set)
    for P in Lbox: colext[P[:-1]].add(P[-1])
    strips = set(Lbox); width = s
    while width < w:
        new = set()
        for P in strips:
            for c in colext.get(P[-(s - 1):], ()): new.add(P + (c,))
        strips = new; width += 1
    level = [to_rows(P) for P in strips]
    up = defaultdict(set)
    for P in Lbox:
        B = to_rows(P); up[B[:-1]].add(B[-1])
    h = s
    yield h, level
    while h < hmax:
        if el() > tlimit: log('   time limit at height', h); return
        nxt = []
        for P in level:
            top = P[-(s - 1):]
            partial = [()]
            for c in range(w - s + 1):
                cands = up.get(tuple(r[c:c + s] for r in top))
                if not cands: partial = []; break
                npart = []
                for pr in partial:
                    if c == 0: npart.extend(cands)
                    else:
                        for t in cands:
                            if t[:s - 1] == pr[c:c + s - 1]: npart.append(pr + (t[-1],))
                partial = npart
                if not partial: break
            for r in partial: nxt.append(P + (r,))
            if len(nxt) > cap: log('   cap %d reached at height %d' % (cap, h + 1)); return
        level = nxt; h += 1
        yield h, level

def band_walls(pats, s, m, H):
    D = (s - 1) // 2; Lc, Rc = m, m + 2 * D + 1
    groups = defaultdict(set)
    for P in pats: groups[tuple(row[m + 1:m + 2 * D + 1] for row in P)].add((P[H][Lc], P[H][Rc]))
    lund = rund = walls = 0; ex = None
    for key, S in groups.items():
        if len(set(a for a, b in S)) > 1: lund += 1
        if len(set(b for a, b in S)) > 1: rund += 1
        Sl = list(S); f = None
        for i in range(len(Sl)):
            for j in range(i + 1, len(Sl)):
                if Sl[i][0] != Sl[j][0] and Sl[i][1] != Sl[j][1]: f = (Sl[i], Sl[j]); break
            if f: break
        if f:
            walls += 1
            if ex is None: ex = f
    return len(groups), lund, rund, walls, ex

def band_run(name, Lbox, s, m, Hmax, cap, glob=None):
    """glob(w, h) -> set of globally legal row-form w x h patterns (or None)."""
    D = (s - 1) // 2; w = 2 * D + 2 + 2 * m
    res = {}
    for h, level in local_levels(Lbox, s, w, 2 * Hmax + 1, cap, BUDGET):
        if h % 2 == 0 or h < s: continue
        H = (h - 1) // 2
        nb, lu, ru, wl, ex = band_walls(level, s, m, H)
        line = 'BAND %s D=%d m=%d w=%d H=%d h=%d local=%d bands=%d left_undet=%d right_undet=%d walls=%d' % (
            name, D, m, w, H, h, len(level), nb, lu, ru, wl)
        if glob is not None:
            G = glob(w, h)
            gnb, glu, gru, gwl, gex = band_walls(G, s, m, H)
            line += ' | global=%d walls=%d' % (len(G), gwl)
        log(line + ('  e.g. ends %s' % (ex,) if ex else ''))
        res[H] = wl
    return res

# ---------------------------------------------------------------- Part D: contextual closure
# Sound criterion (proof in the artifact): let B_R ⊆ C (certified), W = R+1, so every W x W window T is pairwise
# commuting.  For T ∋ 0, T' ∋ v, S = T ∩ T', e_tau = prod_S P^tau commutes with P_0 and P_v, sum_tau e_tau = 1, and
# e_tau P_0^a = [a = a0] e_tau whenever all locally legal T-patterns extending tau have the letter a0 at 0 (expand over
# T; locally illegal terms contain an illegal box).  So if no tau is extendable in both T and T' with BOTH ends
# undetermined, [P_0^a, P_v^b] = 0 in the scale-D presentation.  Rings |v|_inf = R+1 are certified one at a time.
def square_patterns(Lbox, s, W, cap):
    if W == s: return [to_rows(P) for P in Lbox]
    last = None
    for h, level in local_levels(Lbox, s, W, W, cap, BUDGET): last = (h, level)
    if last is None or last[0] != W: return None
    return last[1]

def rule_tester(L, s):
    """det_ok(v, C): v is added by one (w)/(z) determinism step of Part B, using the current certified set C."""
    Lst = list(L); pos = [(i, j) for i in range(s) for j in range(s)]; cache = {}
    def is_rule(q, Fq):
        key = (q, Fq); r = cache.get(key)
        if r is not None: return r
        Fl = sorted(Fq); seen = {}; ok = True
        for P in Lst:
            k = tuple(P[i][j] for (i, j) in Fl); c = P[q[0]][q[1]]
            o = seen.get(k)
            if o is None: seen[k] = c
            elif o != c: ok = False; break
        cache[key] = ok
        return ok
    def det_ok(v, C):
        for q in pos:
            for sg in (1, -1):
                Fq = frozenset(p for p in pos if p != q and (v[0] + sg * (p[0] - q[0]), v[1] + sg * (p[1] - q[1])) in C)
                if is_rule(q, Fq): return True
        return False
    return det_ok

# Legality used by certificates: a pattern on a pairwise-commuting rectangle T has e_pi = 0 unless, for EVERY s x s box
# B meeting T, pi restricted to T ∩ B extends to a legal B-pattern (expand over B \ T, which commutes with T ∩ B).
PROJ = {}
def proj_sets(tag, Lbox, s):
    key = (tag, s)
    if key not in PROJ:
        d = {}
        for ix0 in range(s):
            for iw in range(1, s - ix0 + 1):
                for iy0 in range(s):
                    for ih in range(1, s - iy0 + 1):
                        d[(ix0, iy0, iw, ih)] = set(tuple(tuple(P[ix0 + i][iy0:iy0 + ih]) for i in range(iw)) for P in Lbox)
        PROJ[key] = d
    return PROJ[key]

COLS = {}
def columns(tag, Lbox, s, b, cap):
    key = (tag, s, b)
    if key in COLS: return COLS[key]
    pj = proj_sets(tag, Lbox, s)
    cp = {}
    for iy0 in range(s):
        for ih in range(1, s - iy0 + 1):
            S = None
            for ix in range(s):
                T = set(c[0] for c in pj[(ix, iy0, 1, ih)])
                S = T if S is None else (S & T)
            cp[(iy0, ih)] = S
    letters = sorted(set(x for P in Lbox for col in P for x in col))
    cols = [()]
    for j in range(b):
        bys = [j - (s - 1)] if j < b - 1 else list(range(b - s, b))
        new = []
        for c in cols:
            for x in letters:
                cc = c + (x,); ok = True
                for by in bys:
                    lo = max(0, by)
                    if cc[lo:j + 1] not in cp[(lo - by, j - lo + 1)]: ok = False; break
                if ok: new.append(cc)
        cols = new
        if len(cols) > cap: cols = None; break
    COLS[key] = cols
    return cols

PATCACHE = {}
METHOD = {}
COMPAT = {}
def rect_patterns(tag, Lbox, s, a, b, cap):
    """Row-form a x b patterns satisfying partial-box legality for every box meeting the rectangle (None if over cap/time)."""
    key = (tag, s, a, b)
    if key in PATCACHE: return PATCACHE[key]
    pj = proj_sets(tag, Lbox, s)
    cols = columns(tag, Lbox, s, b, cap)
    res = None
    def boxes_ok(Q, c, bxs):
        """All boxes with lower-left column bx in bxs, every row placement: restriction of Q (columns 0..c) is legal."""
        for bx in bxs:
            lo = max(0, bx); iw = c - lo + 1; ix0 = lo - bx
            for by in range(-(s - 1), b):
                ylo = max(0, by); yhi = min(b - 1, by + s - 1)
                if tuple(Q[x][ylo:yhi + 1] for x in range(lo, c + 1)) not in pj[(ix0, ylo - by, iw, yhi - ylo + 1)]:
                    return False
        return True
    if cols is not None:
        ck = (tag, s, b)
        if ck not in COMPAT:
            def pair_ok(c1, c2):   # necessary: every box position ix0, ix0+1 of an adjacent pair, every row placement
                for ix0 in range(s - 1):
                    for by in range(-(s - 1), b):
                        ylo = max(0, by); yhi = min(b - 1, by + s - 1)
                        if (c1[ylo:yhi + 1], c2[ylo:yhi + 1]) not in pj[(ix0, ylo - by, 2, yhi - ylo + 1)]: return False
                return True
            COMPAT[ck] = {c1: [c2 for c2 in cols if pair_ok(c1, c2)] for c1 in cols}
        compat = COMPAT[ck]
        first_bx = [1 - s] if a > 1 else list(range(1 - s, 1))
        pats = [(c,) for c in cols if boxes_ok((c,), 0, first_bx)]
        ok_all = True
        for c in range(1, a):
            bxs = [c - (s - 1)] if c < a - 1 else list(range(a - s, a))
            new = []
            for P in pats:
                for col in compat[P[-1]]:
                    Q = P + (col,)
                    if boxes_ok(Q, c, bxs): new.append(Q)
            pats = new
            if len(pats) > cap or el() > BUDGET: ok_all = False; break
        if ok_all: res = [to_rows(P) for P in pats]
    PATCACHE[key] = res
    return res

def contextual_closure(name, Lbox, s, Rstop, cap, maxtry, Wmax):
    """Certified set C grown ring by ring; contexts are overlaps of pairwise-commuting rectangles (all offsets in C)."""
    D = (s - 1) // 2
    C = set((a, b) for a in range(-2 * D, 2 * D + 1) for b in range(-2 * D, 2 * D + 1))
    det_ok = rule_tester(Lbox, s)
    ucache = {}
    def comm_rect(a, b): return all((dx, dy) in C for dx in range(-(a - 1), a) for dy in range(-(b - 1), b))
    def shapes():
        full = set()
        for a in range(1, Wmax + 1):   # every width, with its maximal commuting height
            if not comm_rect(a, 1): break
            b = 1
            while b + 1 <= Wmax and comm_rect(a, b + 1): b += 1
            full.add((a, b))
        pareto = [x for x in full if not any(y != x and y[0] >= x[0] and y[1] >= x[1] for y in full)]
        return sorted(pareto)
    def umap(shape, p, rect):
        key = (shape, p, rect); d = ucache.get(key)
        if d is None:
            pats = rect_patterns(name, Lbox, s, shape[0], shape[1], cap)
            if pats is None: ucache[key] = False; return False
            rx0, ry0, rw, rh = rect; d = {}
            for P in pats:
                t = tuple(P[y][rx0:rx0 + rw] for y in range(ry0, ry0 + rh)); val = P[p[1]][p[0]]
                o = d.get(t)
                if o is None: d[t] = val
                elif o != val: d[t] = -1
            ucache[key] = d
        return d
    def top_pairs(n0, n1, c, K):   # 1-dim placements: [x0, x0+n0) ∋ 0 and [x1, x1+n1) ∋ c, by overlap
        out = []
        for x0 in range(-(n0 - 1), 1):
            for x1 in range(c - (n1 - 1), c + 1):
                o = min(x0 + n0, x1 + n1) - max(x0, x1)
                if o > 0: out.append((o, x0, x1))
        out.sort(key=lambda t: (-t[0], t[1], t[2]))
        return out[:K]
    def certify(v, shp):
        cand = []
        for A in shp:
            for B in shp:
                for ox, x0, x1 in top_pairs(A[0], B[0], v[0], 6):
                    for oy, y0, y1 in top_pairs(A[1], B[1], v[1], 6):
                        cand.append((ox * oy, A, B, x0, y0, x1, y1, ox, oy))
        cand.sort(key=lambda c: (-c[0],) + tuple(c[1:]))
        for area, A, B, x0, y0, x1, y1, ox, oy in cand[:maxtry]:
            sx, sy = max(x0, x1), max(y0, y1)
            d0 = umap(A, (-x0, -y0), (sx - x0, sy - y0, ox, oy))
            d1 = umap(B, (v[0] - x1, v[1] - y1), (sx - x1, sy - y1, ox, oy))
            if d0 is False or d1 is False: continue
            if not any(a == -1 and d1.get(t) == -1 for t, a in d0.items()):
                return (A, B, x0, y0, x1, y1)
        return None
    pending = []
    for r in range(2 * D + 1, Rstop + 1):
        if el() > BUDGET: log('CTX %s: time budget reached before ring %d' % (name, r)); break
        pending += [(a, b) for a in range(-r, r + 1) for b in range(-r, r + 1) if max(abs(a), abs(b)) == r and (a, b) not in C]
        ndet = nctx = 0; ex = None
        progress = True
        while pending and progress and el() < BUDGET:
            progress = False; shp = shapes(); rest = []
            for v in pending:
                if v in C: continue
                if det_ok(v, C): C.add(v); C.add((-v[0], -v[1])); ndet += 1; progress = True; METHOD[v] = "det"; continue
                w = certify(v, shp)
                if w:
                    C.add(v); C.add((-v[0], -v[1])); nctx += 1; progress = True
                    METHOD[v] = ("ctx",) + tuple(w)
                    if ex is None: ex = (v, w)
                else: rest.append(v)
            pending = [v for v in rest if v not in C]
        ball = next(q for q in range(0, r + 2) if any(max(abs(a), abs(b)) == q + 1 and (a, b) not in C
                                                          for a in range(-q - 1, q + 2) for b in range(-q - 1, q + 2)))
        log('CTX %s D=%d ring %d: +det %d +ctx %d; uncertified within ring %d: %d; ball radius %d; shapes %s%s' % (
            name, D, r, ndet, nctx, r, len(pending), ball, shapes(), ('  e.g. %s via %s' % ex) if ex else ''))
    unc = sorted(pending)
    ball = next(q for q in range(0, Rstop + 2) if any(max(abs(a), abs(b)) == q + 1 and (a, b) not in C
                                                      for a in range(-q - 1, q + 2) for b in range(-q - 1, q + 2)))
    log('CTX %s RESULT: certified ball radius %d; %d offsets within radius %d uncertified: %s' % (
        name, ball, len(unc), Rstop, unc[:60]))
    return ball, unc

# ---------------------------------------------------------------- run
def main():
    Rm = 4 if SMOKE else 10
    log('PART A: languages')
    LAB3, LAB5 = labbe_windows(3, 3), labbe_windows(5, 5)
    log('Labbe |L_3x3| = %d  |L_5x5| = %d  |L_2x2| = %d' % (len(LAB3), len(LAB5), len(Q2)))
    assert len(LAB3) == 94 and len(LAB5) == 229, 'Labbe language counts differ from recog.py'
    assert all(valid([list(c) for c in P]) for P in LAB5)
    CH3, CH5, LE3, LE5, FU3 = lang_checker(3), lang_checker(5), lang_ledrappier(3), lang_ledrappier(5), lang_full(3)
    log('checker %d/%d  Ledrappier %d/%d  full %d' % (len(CH3), len(CH5), len(LE3), len(LE5), len(FU3)))

    log('PART B: determinism closure, region |v|_inf <= %d' % Rm)
    full_region = (2 * Rm + 1) ** 2
    calib = True
    for name, L, s, expect in [('checker', CH3, 3, 'fill'), ('ledrappier', LE3, 3, 'fill'), ('ledrappier', LE5, 5, 'fill'),
                               ('full2', FU3, 3, 'ball'), ('labbe', LAB3, 3, None), ('labbe', LAB5, 5, None)]:
        C, sw = closure(L, s, Rm); D = (s - 1) // 2
        rad = max(max(abs(a), abs(b)) for a, b in C)
        st = 'fills region' if len(C) == full_region else ('= B_%d' % (2 * D) if len(C) == (4 * D + 1) ** 2 else 'bounded')
        ok = (expect == 'fill' and len(C) == full_region) or (expect == 'ball' and len(C) == (4 * D + 1) ** 2) or expect is None
        calib = calib and ok
        log('CLOSURE %s D=%d |C|=%d max|v|=%d sweeps=%d: %s%s' % (name, D, len(C), rad, sw, st,
            '' if expect is None else ('  [calibration %s]' % ('PASS' if ok else 'FAIL'))))
        if name == 'labbe':
            show(C, Rm)
            ring = sorted(v for v in itertools.product(range(-Rm, Rm + 1), repeat=2)
                          if max(abs(v[0]), abs(v[1])) == 2 * D + 1 and v not in C)
            log('   open offsets at |v|_inf = %d: %d of %d, e.g. %s' % (2 * D + 1, len(ring), 8 * (2 * D + 1), ring[:12]))
    log('CLOSURE CALIBRATION %s' % ('PASS' if calib else 'FAIL'))
    if not calib: log('ABORT: calibration failed'); return

    log('PART C: band walls (window certificates)')
    Hm = 3 if SMOKE else 10
    cap = 20000 if SMOKE else 400000
    c1 = band_run('full2', FU3, 3, 0, Hm, cap)
    c2 = band_run('checker', CH5, 5, 0, Hm, cap)
    c3 = band_run('ledrappier', LE3, 3, 0, Hm, cap)
    c4 = band_run('ledrappier', LE5, 5, 0, Hm, cap)
    bc = all(v > 0 for v in c1.values()) and len(c1) > 0 and all(v == 0 for d in (c2, c3, c4) for v in d.values())
    log('BAND CALIBRATION %s (full2 walls at every H; checker/Ledrappier none)' % ('PASS' if bc else 'FAIL'))
    if not bc: log('ABORT: band calibration failed'); return
    gx = lambda w, h: set(to_rows(P) for P in labbe_windows(w, h))
    gy = lambda w, h: set(labbe_windows(h, w))   # original window h x w (columns); its column form = transposed row form
    LAB5T = set(transpose(P) for P in LAB5)
    for m in (0,) if SMOKE else (0, 1):
        band_run('labbe-e1', LAB5, 5, m, 3 if SMOKE else 6, cap, gx)
        band_run('labbe-e2', LAB5T, 5, m, 3 if SMOKE else 6, cap, gy)

    # displacement (6,0): window [0,6] x [0,2H], ends (0,H), (6,H); separating bands of 4 agreeing columns [1,4] or [2,5]
    def walls6(name, Lbox, Hmax):
        for h, level in local_levels(Lbox, 5, 7, 2 * Hmax + 1, cap, BUDGET):
            if h % 2 == 0: continue
            H = (h - 1) // 2; out = []
            for lo in (1, 2):
                g = defaultdict(set)
                for P in level: g[tuple(row[lo:lo + 4] for row in P)].add((P[H][0], P[H][6]))
                wl = sum(1 for S in g.values() if any(p[0] != q[0] and p[1] != q[1] for p in S for q in S))
                out.append('band[%d,%d] bands=%d walls=%d' % (lo, lo + 3, len(g), wl))
            log('WALL6 %s H=%d h=%d local=%d  %s' % (name, H, h, len(level), '  '.join(out)))
    walls6('labbe-e1', LAB5, 3 if SMOKE else 6)
    walls6('labbe-e2', LAB5T, 3 if SMOKE else 6)
    log('PART D: contextual closure (window case-split certificates)')
    mt = 40
    r1 = contextual_closure('full2', FU3, 3, 6, cap, mt, 6)[0]
    r2 = contextual_closure('checker', CH3, 3, 6, cap, mt, 8)[0]
    rs = 5 if SMOKE else 7
    r3 = contextual_closure('ledrappier', LE3, 3, rs, cap, mt, 8)[0]
    r4 = contextual_closure('ledrappier', LE5, 5, rs, cap, mt, 8)[0]
    dc = r1 == 2 and r2 == 6 and r3 == rs and r4 == rs
    log('CTX CALIBRATION %s (full2 blocked at 2; checker, Ledrappier reach the stop radius)' % ('PASS' if dc else 'FAIL'))
    if not dc: log('ABORT: contextual calibration failed'); return
    contextual_closure('labbe', LAB3, 3, 6 if SMOKE else 10, cap, mt, 8 if SMOKE else 12)
    contextual_closure('labbe', LAB5, 5, 7 if SMOKE else 20, cap, mt, 9 if SMOKE else 14)
    log('DONE')

if __name__ == '__main__':
    if "--ring5" in sys.argv:
        LAB5 = labbe_windows(5, 5)
        contextual_closure("labbe", LAB5, 5, 5, 400000, 40, 9)
        for v in sorted(METHOD): print("METHOD", v, METHOD[v])
    else:
        main()
