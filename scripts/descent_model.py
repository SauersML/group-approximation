"""Numerical model of the column-adapted Milnor 10.6 descent, with
UNIT letters (exponents +-1 only), which is Milnor's actual setting.

Words: lists of (i, e), i in 0..5 = (e12,e13,e21,e23,e31,e32), e = +-1.
Left action on integer columns.  Suffix vectors from base corner b.
Violation at j: s(j) < s(j+1).  Measure (lam, mu-dist, len).

Rule engine: at the chosen violation, try all catalog moves; pick one
that strictly decreases the lex measure; verify eval-preservation via
SL3 matrices (allowing an emitted monomial pushed to the right end).
Record which move wins per configuration to extract the Lean case
table.  If no move decreases, dump the configuration (a missing case).
"""
import numpy as np, random, sys
from collections import Counter

def letter_mat(i, c):
    M = np.eye(3, dtype=object)
    pos = [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)][i]
    M[pos] = c
    return M

W12 = letter_mat(0,1) @ letter_mat(2,-1) @ letter_mat(0,1)
W13 = letter_mat(1,1) @ letter_mat(4,-1) @ letter_mat(1,1)
W23 = letter_mat(3,1) @ letter_mat(5,-1) @ letter_mat(3,1)
MONGENS = {'w': W12, 'w13': W13, 'w23': W23}
CONJ = {
 'w':   {0:(2,-1),1:(3,-1),2:(0,-1),3:(1,1),4:(5,-1),5:(4,1)},
 'w13': {0:(5,-1),1:(4,-1),2:(3,-1),3:(2,1),4:(1,-1),5:(0,1)},
 'w23': {0:(1,-1),1:(0,1),2:(4,-1),3:(5,-1),4:(2,1),5:(3,-1)},
}
INVNAME = {'w':'w^3','w13':'w13^3','w23':'w23^3'}

def conj_letter(mname, l):
    i, c = l; j, s = CONJ[mname][i]; return (j, s*c)

def conj_word(mname, W):
    return [conj_letter(mname, l) for l in W]

def eval_word(W):
    M = np.eye(3, dtype=object)
    for (i,c) in W: M = M @ letter_mat(i,c)
    return M

def vecs(W, b):
    out = [np.array(b, dtype=object)]
    for (i,c) in reversed(W): out.append(letter_mat(i,c) @ out[-1])
    return list(reversed(out))

def norms(W, b):
    return [int(sum(abs(int(x)) for x in v)) for v in vecs(W, b)]

def measure(W, b):
    s = norms(W, b)
    viol = [j for j in range(len(W)) if s[j] < s[j+1]]
    if not viol: return (0, 0, len(W))
    lam = max(s[j+1] for j in viol)
    mu = min(j for j in viol if s[j+1] == lam)   # TOPMOST worst violation
    return (lam, len(W) - mu, len(W))

SWAPL = {  # x_a(s) x_b(t) = x_k(s*t) x_b(t) x_a(s)
 (0,3): 1, (1,5): 0, (2,1): 3, (3,4): 2, (4,0): 5, (5,2): 4,
}
COMMUTE = {(0,1),(1,0),(0,5),(5,0),(1,3),(3,1),(2,3),(3,2),(2,4),(4,2),(4,5),(5,4)}
OPP = {(0,2),(2,0),(1,4),(4,1),(3,5),(5,3)}
BLOCK_OF = {(0,2):'w',(2,0):'w',(1,4):'w13',(4,1):'w13',(3,5):'w23',(5,3):'w23'}
POSNEG = {'w':(0,2),'w13':(1,4),'w23':(3,5)}

def sanity():
    for (a,bf),k in SWAPL.items():
        for s in (-1,1):
            for t in (-1,1):
                L = eval_word([(a,s),(bf,t)])
                R = eval_word([(k,s*t),(bf,t),(a,s)])
                assert (L == R).all(), ("swapL", a, bf)
    for mname, M in MONGENS.items():
        Minv = np.round(np.linalg.inv(M.astype(float))).astype(int).astype(object)
        for i in range(6):
            for c in (-1,1):
                L = M @ letter_mat(i,c) @ Minv
                j, cc = conj_letter(mname,(i,c))
                assert (L == letter_mat(j,cc)).all(), ("conj", mname, i)
    print("identity tables OK")
sanity()

def wvariant_matrix(mname, e):
    """w_blk(e) = x_pos(e) x_neg(-e) x_pos(e)"""
    pos, neg = POSNEG[mname]
    return eval_word([(pos,e),(neg,-e),(pos,e)])

def wvariant_conj(mname, e, l):
    """conjugation of letter l by w_blk(e): for e=+1 it's CONJ table;
    for e=-1, w_blk(-1) = w_blk(1)^-1: inverse conjugation."""
    if e == 1: return conj_letter(mname, l)
    # inverse table
    i, c = l
    for j in range(6):
        jj, s = CONJ[mname][j]
        if jj == i:
            return (j, s*c)   # since conj(m, (j, s*c... invert mapping
    raise AssertionError


# ---- generic short-rewrite table -------------------------------------
LETTERS12 = [(i,c) for i in range(6) for c in (-1,1)]
SHORTWORDS = {}
def _key(M): return tuple(int(x) for x in M.flatten())
from itertools import product as _prod
for L in range(0, 4):
    for wd in _prod(LETTERS12, repeat=L):
        M = eval_word(list(wd))
        SHORTWORDS.setdefault(_key(M), []).append(list(wd))
EMITS = [None] + [(m, e) for m in ('w','w13','w23') for e in (1,-1)]

def candidates(W, mu):
    i, c = W[mu]; ip, cp = W[mu+1]
    P = letter_mat(i,c) @ letter_mat(ip,cp)
    out = []
    for em in EMITS:
        if em is None:
            target = P
        else:
            mname, e = em
            Winv = wvariant_matrix(mname, -e)
            target = P @ Winv
        for wd in SHORTWORDS.get(_key(target), []):
            out.append((W[:mu] + wd + W[mu+2:],
                        [] if em is None else [em],
                        f"g{len(wd)}{'' if em is None else '+'+em[0]+str(em[1])}"))
    return out

def push_mon_right(mons, suffix):
    """Push emitted w-variants through the suffix: returns
    (new_suffix_letters, mon_matrix_product)."""
    Wt = list(suffix); M = np.eye(3, dtype=object)
    for (mname, e) in mons:
        Wt = [wvariant_conj(mname, e, l) for l in Wt]
    # recompute matrix: mons multiply in order
    M = np.eye(3, dtype=object)
    for (mname, e) in mons:
        M = M @ wvariant_matrix(mname, e)
    return Wt, M

def step(W, b, monM):
    lam, mud, _ = measure(W, b)
    if lam == 0: return None
    mu = len(W) - mud
    cands = candidates(W, mu)
    best = None
    m0 = measure(W, b)
    for (W2, mons, tag) in cands:
        if mons:
            # push emitted monomials right through the suffix AFTER the
            # pair position: they sit where the pair was; suffix = rest
            # of W2 after the inserted letters?  In candidates, emitted
            # mons belong right after the replaced pair position; the
            # letters after that are W[mu+2:] tail inside W2. Rebuild:
            # W2 = head + tail where tail = W[mu+2:]; find split point:
            ntail = len(W) - (mu+2)
            head, tail = W2[:len(W2)-ntail], W2[len(W2)-ntail:]
            tail2, Mm = push_mon_right(mons, tail)
            W3 = head + tail2
            newmon = Mm @ monM
            # eval check
            L = eval_word(W) @ monM
            R = eval_word(W3) @ newmon
            if not (L == R).all(): continue
            m2 = measure(W3, colof(newmon, b0_global))
        else:
            W3 = W2; newmon = monM
            L = eval_word(W) @ monM
            R = eval_word(W3) @ newmon
            if not (L == R).all(): continue
            m2 = measure(W3, colof(newmon, b0_global))
        if m2 < m0:
            if best is None or m2 < best[0]:
                best = (m2, W3, newmon, tag)
    return best

def colof(monM, e3):
    return monM @ np.array(e3, dtype=object)

b0_global = (0,0,1)

def run_one(W, verbose=False):
    monM = np.eye(3, dtype=object)
    b = colof(monM, b0_global)
    target = eval_word(W)
    steps = 0
    tags = Counter()
    while True:
        b = colof(monM, b0_global)
        m = measure(W, b)
        if m[0] == 0:
            assert (eval_word(W) @ monM == target).all()
            return True, steps, tags
        r = step(W, b, monM)
        if r is None:
            return (W, b, monM), steps, tags   # FAILURE: dump config
        m2, W, monM, tag = r
        tags[tag] += 1
        steps += 1
        if steps > 8000:
            return "LOOP", steps, tags

random.seed(7)
fails = 0; tagtotal = Counter()
for trial in range(400):
    n = random.randint(1, 14)
    W = [(random.randrange(6), random.choice([-1,1])) for _ in range(n)]
    res, steps, tags = run_one(W)
    tagtotal.update(tags)
    if res is not True:
        fails += 1
        print("FAIL", res if not isinstance(res, tuple) else
              (res[0], [int(x) for x in res[1]], "mu-pair dump"), file=sys.stderr)
        if fails > 4: break
print("fails:", fails, " tags:", dict(tagtotal))
