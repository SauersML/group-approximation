# Bounded search for a hidden relation in K_2 (lane gq-ring-fp-simple, 2026-09-18)

Evidence, not proof. Cleared by the coordinator as a bounded MSI search: single core, each run at most
10 minutes, about 16 minutes of compute in total, nothing left running. Target node:
`prime-shift-group-k2-is-finitely-presented`, Attempt 3.

## CORRECTION (added the same day): the searched words could never produce a hit

Found while tabulating the near misses. Every generator `σ_2^j M σ_2^-j` with `M in GL_2(Z)` preserves the
content `c(w)`, the positive generator of `Z w_1 + Z w_2`. The reason: `c(σ_2 w) = σ(c(w))` and
`c(M w) = c(w)`. So every searched word lies in the content-preserving subgroup `C`.
- **Test 1 is vacuous.** Suppose `V_1 = L V_2` with `V_1, V_2 in C`. Then `L in C` is linear. A linear map
  preserving content sends primitive vectors to primitive vectors, so it lies in `GL_2(Z)` and
  `|det L| = 1`. If `p` divides `det L`, some primitive `w` has `L w in p Z^2`.
- **Test 2 is vacuous.** Suppose `V = L r V'` with `V, V' in C`. Then `L r in C`. That forces `L` to be
  integral with primitive columns. But `r(1,1) = (168,-10)` has content 2, so `L r(1,1)` has content at
  least 2.
- **So "0 hits" is a theorem, not evidence.** The runs above say nothing about whether `r in N`. The
  calibration found hits only because it added `e`, which is not in `C`.
- **The correct search space.** `N = <σ_2^j SL_2(Q) σ_2^-j, D : j in Z>` (Attempt 5 of the node). Its
  generators include `σ_2^j x_12(q) σ_2^-j` for rational `q`, which do not preserve content. A meaningful
  search must use them, for example `q in {±1/2, ±2, ±1/3, ±3}`. That is not run here.
- **Tabulation (run `tab`, 55 s).** On the extra lines `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`, `(2,3)`,
  `(1,-2)`, all 185 near misses (length <= 5, `|j| <= 1`):
  - preserve content, with ratio exactly 1, as they must;
  - keep none of those lines.

  `r` keeps none of them either. It changes content by 2 on `(1,1)` and `(1,3)`, and by 1 on the other five.

## Question

Is the three-line fixer `r` of Attempt 3, equivalently `e = diag(2,1)`, in `N = <<GL_2(Z)>>` in
`K_2`? The search looks for any relation that proves a nontrivial element of `I_2` exists.

## Setup

- `σ` uses the example indexing of `gl-n-q-lies-in-prime-shift-permutation-group`: `p_k` is the `2k`-th
  prime for `k > 0` and the `(1-2k)`-th for `k <= 0`, so `σ(2) = 3`, `σ(3) = 7`, `σ(5) = 2` and `σ(11) = 5`.
  Exact integer and rational arithmetic is used throughout. Factoring is by trial division with a sieve to
  `5·10^6`. A word is dropped as *overflow* if some prime factor exceeds the sieve or a value exceeds `10^15`.
- **Generators of N.** The generators are `σ_2^j M σ_2^-j` for `|j| <= J`, with `M` in `{X^(±1), Y^(±1)}`, the
  elementary matrices. The "wide" runs add `X^(±2)` and `Y^(±2)`. There are also `W = [[0,1],[1,0]]` and
  `D = diag(-1,1)`, which commute with `σ_2`. Every word in these generators lies in `N` and has degree 0.
- **Ball.** Breadth-first search over freely reduced words, deduplicated by the exact images of the 10
  probe points `(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2),(3,5),(5,-3),(7,2),(2,9)`.

## Tests, and why a negative answer is sound for the searched class

- **Left-linear key.** For a word `V`, `L_V` is the matrix with columns `V(1,0)` and `V(0,1)`, and the key
  is `L_V^-1 V(p)` over the other 8 probes.
  - If `V_1 = L V_2` holds in `K_2` for a linear `L`, then the keys are equal and
    `|det L| = |det L_(V_1)| / |det L_(V_2)|`.
  - Then `L = V_1 V_2^-1` lies in `N ∩ GL_2(Q)`, so `|det L| in I_2`.
  - A hit with `|det L| != 1` would be a hidden relation. The reason is that `Π_2 -> Q^x ⋊ Z` shows every
    relation of `Π_2` gives `|det L| = 1`.
- **r-translated key.** For short `V'`, compute the key of `r ∘ V'` and look it up among the ball's keys.
  - A match `V = L r V'` gives `r = L^-1 V V'^-1`, so `|det L| / 2 in I_2`.
  - This is informative unless `|det L| = 2`, and `|det L| = 1` would give `e in N`.
- **Soundness of "no hit".** A true relation agrees on the probes. Deduplication by probe images loses
  nothing: two words with equal images have equal keys, and equal images after every extension.
  - So, apart from implementation errors and the listed overflow words, "0 hits" proves there is no
    relation of the tested shape among the searched words.
- **Hits would need certification.** Probe agreement does not determine a nonlinear element. So any hit
  would be re-checked on random points by the independent `k2verify.py`, which uses sympy `factorint`,
  `primepi` and `prime` and shares no code with the search. It would then be certified symbolically. No
  hit occurred.

## Runs (MSI agate node, python3, single core)

| run | generators | J | max length | ball size | overflow | linear hits | r-lookup (length <=) | r hits | time |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 14 | 1 | 5 | 186,331 | 2,170 | 0 | 1,523 words (3) | 0 | 51 s |
| 2 | 22 | 2 | 4 | 134,281 | 11,808 | 0 | 41,409 words (4) | 0 | 204 s |
| 3 | 14 | 1 | 6 (partial) | 1,644,026 | 50,410 | 0 | 1,523 words (3) | 0 | 524 s |
| 4 | 26 (wide) | 1 | 4 | 245,621 | 917 | 0 | 9,953 words (3) | 0 | 91 s |

Run 3 stopped at its time budget after 1,457,695 new elements of length 6. Levels up to 5 are complete.

## Calibration

The `calib` mode adds `e` itself as a generator, and looks up `k` in place of `r`.
- The linear test fires: 805 hits with `|det L| = 2`, such as `s0E` against the empty word.
- The translated lookup finds `k` in the ball with `|det L| = 2`, as it must, since `k = σ(g)^-1 σ_2 g σ_2^-1`.
- The independent verifier:
  - reports `L = I`, `det 1` and no mismatch on 40 random points for the true relation `D (σ X σ^-1) D = σ X^-1 σ^-1`;
  - reports a mismatch for the nonlinear pair `s1Y s1X` versus `s0X s0Y`.

## Near misses

Words that fix both axes and `(1,-1)`:
- runs 1 and 3: 185 and 2,250 of them;
- run 2: 1,715;
- run 4: 233.

None agrees with `r` on more than those three probes; the best is 3 of 10. The shortest are words such as
`s-1X s0x`, the element `X^-1 ∘ (σ_2^-1 X σ_2)`: the word applies its letters left to right. Both factors fix
the `x`-axis; on the `y`-axis, `(0,y) -> (y,y) -> (0,y)`.

## Reading (superseded by the correction above)

The paragraph below is kept as first written. By the correction, both tests are vacuous on this word class,
so the result carries no evidence either way.

Across these words the answer is "no relation": no `σ_2^(±1)`-, `σ_2^(±2)`- or wide-shear word of length
<= 5, and length-6 words partially, is a linear map of `|det| != 1`, and no pair of such words differs by one.
Nor is `r` a linear map times a quotient of such words, for short right factors. This is consistent with
`I_2 = 1`, and hence with `K_2` not finitely presented, but proves nothing about longer words, larger `J`,
or conjugators other than powers of `σ_2`. By the Bieri--Strebel test (`e7a442014`) and
`torus-amalgams-of-adelic-groups-are-not-finitely-presented`, finite presentation needs a relation of
exactly the kind searched for here.

## Run outputs

### run1.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('168', '-10'), ('1', '-1'), ('-29', '200'), ('701', '-2402'), ('-2097', '18958'), ('-346', '201'), ('-32', '95'), ('4216', '2118')]
generators: 14  J = 1  MAXLEN = 5  RLEN = 3
level 1 new elements 14 time 0.4 overflow 0
level 2 new elements 158 time 0.4 overflow 0
level 3 new elements 1646 time 0.8 overflow 0
level 4 new elements 16789 time 5.6 overflow 36
level 5 new elements 167723 time 48.5 overflow 2170
ball size 186331 overflow 2170 stopped_early False
linear-collision hits (|det L| != 1): 0
near misses (fix both axes and (1,-1)): 185
r-translated words checked 1523 overflow 296 matches 0
total time 51.3
```

### run2.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('168', '-10'), ('1', '-1'), ('-29', '200'), ('701', '-2402'), ('-2097', '18958'), ('-346', '201'), ('-32', '95'), ('4216', '2118')]
generators: 22  J = 2  MAXLEN = 4  RLEN = 4
level 1 new elements 22 time 0.3 overflow 0
level 2 new elements 422 time 0.4 overflow 0
level 3 new elements 7562 time 2.5 overflow 220
level 4 new elements 126274 time 38.4 overflow 11808
ball size 134281 overflow 11808 stopped_early False
linear-collision hits (|det L| != 1): 0
near misses (fix both axes and (1,-1)): 1715
r-translated words checked 41409 overflow 92872 matches 0
total time 204.1
```

### run3.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('168', '-10'), ('1', '-1'), ('-29', '200'), ('701', '-2402'), ('-2097', '18958'), ('-346', '201'), ('-32', '95'), ('4216', '2118')]
generators: 14  wide = False  J = 1  MAXLEN = 6  RLEN = 3
level 1 new elements 14 time 0.3 overflow 0
level 2 new elements 158 time 0.4 overflow 0
level 3 new elements 1646 time 0.8 overflow 0
level 4 new elements 16789 time 4.7 overflow 36
level 5 new elements 167723 time 49.8 overflow 2170
level 6 new elements 1457695 time 520.0 overflow 50410
ball size 1644026 overflow 50410 stopped_early True
linear-collision hits (|det L| != 1): 0
near misses (fix both axes and (1,-1)): 2250
r-translated words checked 1523 overflow 296 matches 0
total time 524.4
```

### run4.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('168', '-10'), ('1', '-1'), ('-29', '200'), ('701', '-2402'), ('-2097', '18958'), ('-346', '201'), ('-32', '95'), ('4216', '2118')]
generators: 26  wide = True  J = 1  MAXLEN = 4  RLEN = 3
level 1 new elements 26 time 0.3 overflow 0
level 2 new elements 554 time 0.5 overflow 0
level 3 new elements 11462 time 3.4 overflow 0
level 4 new elements 233578 time 68.2 overflow 917
ball size 245621 overflow 917 stopped_early False
linear-collision hits (|det L| != 1): 0
near misses (fix both axes and (1,-1)): 233
r-translated words checked 9953 overflow 2090 matches 0
total time 90.7
```

### calib.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('2', '1'), ('1/2', '-1/2'), ('-8', '29'), ('-4', '25'), ('-5/2', '43/2'), ('-31/2', '129/2'), ('-11', '38'), ('-5', '54')]
generators: 15  wide = False  J = 1  MAXLEN = 3  RLEN = 1
level 1 new elements 15 time 0.4 overflow 0
level 2 new elements 186 time 0.4 overflow 0
level 3 new elements 2160 time 0.9 overflow 0
ball size 2362 overflow 0 stopped_early False
linear-collision hits (|det L| != 1): 805
  HIT 2 | s0E | vs | 
  HIT 2 | s-1X s0E | vs | s-1X
  HIT 2 | s-1x s0E | vs | s-1x
  HIT 1/2 | s-1Y s-1x | vs | s-1X s0E
  HIT 2 | s-1Y s0E | vs | s-1Y
  HIT 1/2 | s-1y s-1X | vs | s-1x s0E
  HIT 2 | s-1y s0E | vs | s-1y
  HIT 1/2 | s0X s0X | vs | s0E
  HIT 1/2 | s0X s0Y | vs | s0E
  HIT 1/2 | s0X s0y | vs | s0E
  HIT 1/2 | s0X s0W | vs | s0E
  HIT 1/2 | s0X s0D | vs | s0E
  HIT 2 | s0X s0E | vs | 
  HIT 1/2 | s0x s0x | vs | s0E
  HIT 1/2 | s0x s0Y | vs | s0E
  HIT 1/2 | s0x s0y | vs | s0E
  HIT 1/2 | s0x s0W | vs | s0E
  HIT 1/2 | s0x s0D | vs | s0E
  HIT 2 | s0x s0E | vs | 
  HIT 1/2 | s0Y s0X | vs | s0E
near misses (fix both axes and (1,-1)): 12
r-translated words checked 16 overflow 0 matches 22
  RHIT |det L| = 2 uninformative | s1Y s1X | = L r | 
  RHIT |det L| = 4 NEW | s1Y s1X s0E | = L r | 
  RHIT |det L| = 2 uninformative | s-1X s1Y s1X | = L r | s-1X
  RHIT |det L| = 2 uninformative | s-1x s1Y s1X | = L r | s-1x
  RHIT |det L| = 2 uninformative | s-1Y s1Y s1X | = L r | s-1Y
  RHIT |det L| = 2 uninformative | s-1y s1Y s1X | = L r | s-1y
  RHIT |det L| = 2 uninformative | s0X s1Y s1X | = L r | s0X
  RHIT |det L| = 2 uninformative | s0x s1Y s1X | = L r | s0x
  RHIT |det L| = 2 uninformative | s0Y s1Y s1X | = L r | s0Y
  RHIT |det L| = 2 uninformative | s0y s1Y s1X | = L r | s0y
  RHIT |det L| = 2 uninformative | s1X s1Y s1X | = L r | s1X
```

## Script `k2search.py`

```python
#!/usr/bin/env python3
"""Bounded search for hidden relations in K_2 = <GL_2(Z), diag(2,1), sigma_2>.

Generators of N = <<GL_2(Z)>>: conjugates sigma_2^j M sigma_2^-j, M in {X, X^-1, Y, Y^-1}
(elementary matrices), |j| <= J, plus the signed permutations W, D (which commute with sigma_2).
All of them are degree-0 elements of N, so every word lies in N.

Elements are compared through their images of a fixed probe set of integer points.
A left-linear normal key detects words W1, W2 with W1 = L W2 on the probes; then
L = W1 W2^-1 is in N, and |det L| != 1 would be a hidden relation (Pi_2 -> K_2 not injective).
A second table is keyed by r o W' (r the three-line fixer of Attempt 3); a match W = L r W'
gives |det L|/2 in I_2, which is new unless |det L| = 2.
Probe agreement is a FILTER, not a proof: every hit must be re-verified on random points
and then certified symbolically.
"""
import sys, time, bisect, random
from fractions import Fraction as Fr

T0 = time.time()
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 540.0
MAXLEN = int(sys.argv[2]) if len(sys.argv) > 2 else 4
J = int(sys.argv[3]) if len(sys.argv) > 3 else 1
RLEN = int(sys.argv[4]) if len(sys.argv) > 4 else 3
WIDE = len(sys.argv) > 5 and sys.argv[5] == 'wide'
CALIB = len(sys.argv) > 5 and sys.argv[5] == 'calib'  # adds e = diag(2,1): hits MUST appear

LIMIT = 5_000_000
sieve = bytearray([1]) * (LIMIT + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(LIMIT ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(range(i * i, LIMIT + 1, i)))
PR = [i for i in range(LIMIT + 1) if sieve[i]]
del sieve


class Overflow(Exception):
    pass


def idx_to_k(n):  # n = 1-based prime index; p_k is the 2k-th prime (k>0), (1-2k)-th (k<=0)
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def k_to_idx(k):
    return 2 * k if k > 0 else 1 - 2 * k


FCACHE = {}


def factor(m):
    """m >= 1 -> tuple of (prime, exponent)."""
    if m in FCACHE:
        return FCACHE[m]
    orig, out = m, []
    for p in PR:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            out.append((p, e))
    if m > 1:
        if m > LIMIT:
            raise Overflow()
        out.append((m, 1))
    res = tuple(out)
    if len(FCACHE) < 3_000_000:
        FCACHE[orig] = res
    return res


def sig_int(m, j):
    if m == 0 or j == 0:
        return m
    s, a = (1, m) if m > 0 else (-1, -m)
    r = 1
    for p, e in factor(a):
        n = bisect.bisect_left(PR, p) + 1
        n2 = k_to_idx(idx_to_k(n) + j)
        if n2 > len(PR):
            raise Overflow()
        r *= PR[n2 - 1] ** e
        if r > 10 ** 15:
            raise Overflow()
    return s * r


def sig(q, j):
    if isinstance(q, int):
        return sig_int(q, j)
    return Fr(sig_int(q.numerator, j), sig_int(q.denominator, j))


def mat_apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def gen_apply(g, v):
    j, M = g
    if j == 0:
        return mat_apply(M, v)
    w = (sig(v[0], -j), sig(v[1], -j))
    w = mat_apply(M, w)
    return (sig(w[0], j), sig(w[1], j))


X = ((1, 1), (0, 1)); Xi = ((1, -1), (0, 1))
Y = ((1, 0), (1, 1)); Yi = ((1, 0), (-1, 1))
Wm = ((0, 1), (1, 0)); Dm = ((-1, 0), (0, 1))
X2 = ((1, 2), (0, 1)); X2i = ((1, -2), (0, 1)); Y2 = ((1, 0), (2, 1)); Y2i = ((1, 0), (-2, 1))
PAIRS = [(X, Xi), (Xi, X), (Y, Yi), (Yi, Y)]
if WIDE:
    PAIRS += [(X2, X2i), (X2i, X2), (Y2, Y2i), (Y2i, Y2)]
INVM = {a: b for a, b in PAIRS}
GENS, INV = [], []
for j in range(-J, J + 1):
    for M, Mi in PAIRS:
        GENS.append((j, M))
for M in (Wm, Dm):
    GENS.append((0, M))
Em = ((2, 0), (0, 1))
if CALIB:
    GENS.append((0, Em))
for g in GENS:
    j, M = g
    if M in (Wm, Dm, Em):
        INV.append(-1 if M == Em else GENS.index(g))
    else:
        Mi = INVM[M]
        INV.append(GENS.index((j, Mi)))
NG = len(GENS)

PROBES = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 5), (5, -3), (7, 2), (2, 9)]


def normkey(imgs):
    (a, c), (b, d) = imgs[0], imgs[1]
    det = a * d - b * c
    if det == 0:
        return None, None
    det = Fr(det)
    key = []
    for (x, y) in imgs[2:]:
        # L^-1 = (1/det) [[d, -b], [-c, a]]
        key.append(((d * x - b * y) / det, (-c * x + a * y) / det))
    return tuple(key), abs(det)


def word_str(w):
    return ' '.join('s%d%s' % (GENS[i][0], {X: 'X', Xi: 'x', Y: 'Y', Yi: 'y', X2: 'P', X2i: 'p', Y2: 'Q', Y2i: 'q', Wm: 'W', Dm: 'D', Em: 'E'}[GENS[i][1]]) for i in w)


# ---- the elements g, k, r of Attempts 2 and 3 ----
G2 = ((2, 1), (1, 1)); SG2inv = ((Fr(1, 2), Fr(-1, 2)), (Fr(-1, 2), Fr(3, 2)))  # sigma(g) = [[3,1],[1,1]]
assert sig(2, 1) == 3 and sig(3, 1) == 7 and sig(5, 1) == 2 and sig(11, 1) == 5


def k_apply(v):
    w = (sig(v[0], -1), sig(v[1], -1))
    w = mat_apply(G2, w)
    w = (sig(w[0], 1), sig(w[1], 1))
    return mat_apply(SG2inv, w)


Mm = ((1, 0), (-1, -1))


def MkM(v):
    return mat_apply(Mm, k_apply(mat_apply(Mm, v)))


def wMkMw(v):
    return mat_apply(Wm, MkM(mat_apply(Wm, v)))


def r_apply(v):
    v = (2 * v[0], 2 * v[1])
    return k_apply(MkM(wMkMw(v)))


def as_fr(v):
    return (Fr(v[0]), Fr(v[1]))


# sanity: k fixes the axes pointwise and halves (1,-1); r fixes three lines pointwise
assert as_fr(k_apply((1, 0))) == (1, 0) and as_fr(k_apply((0, 1))) == (0, 1)
assert as_fr(k_apply((1, -1))) == (Fr(1, 2), Fr(-1, 2))
for v in ((1, 0), (0, 1), (1, -1), (5, 0), (0, -7), (3, -3)):
    assert as_fr(r_apply(v)) == as_fr(v), v
if CALIB:  # calibration: look up k in place of r; the word s1Y s1X must be found with |det L| = 2
    r_apply = k_apply
R_IMG = [as_fr(r_apply(p)) for p in PROBES]
print('k(1,1) =', k_apply((1, 1)), ' r on probes:', [(str(a), str(b)) for a, b in R_IMG])
print('generators:', NG, ' wide =', WIDE, ' J =', J, ' MAXLEN =', MAXLEN, ' RLEN =', RLEN, flush=True)

# ---- BFS ball with dedup by exact probe images ----
ident = tuple(PROBES)
seen = {ident: ()}
frontier = [(ident, ())]
table = {}  # normkey -> dict |det| -> word
k0, d0 = normkey(ident)
table[k0] = {d0: ()}
hits, near, overflow = [], [], 0
levels = []
stopped = False
for L in range(1, MAXLEN + 1):
    nxt = []
    for imgs, w in frontier:
        if time.time() - T0 > BUDGET:
            stopped = True
            break
        last = w[-1] if w else None
        for gi in range(NG):
            if last is not None and gi == INV[last]:
                continue
            try:
                new = tuple(gen_apply(GENS[gi], v) for v in imgs)
            except Overflow:
                overflow += 1
                continue
            if new in seen:
                continue
            nw = w + (gi,)
            seen[new] = nw
            nxt.append((new, nw))
            key, dt = normkey(new)
            if key is None:
                continue
            ent = table.setdefault(key, {})
            for d2, w2 in ent.items():
                if d2 != dt:
                    hits.append(('linear', nw, w2, dt / d2))
            ent.setdefault(dt, nw)
            if new[0] == (1, 0) and new[1] == (0, 1) and new[3] == (1, -1):
                agree = sum(1 for a, b in zip(new, R_IMG) if as_fr(a) == b)
                near.append((agree, nw))
    levels.append((L, len(nxt), round(time.time() - T0, 1)))
    print('level', L, 'new elements', len(nxt), 'time', round(time.time() - T0, 1), 'overflow', overflow, flush=True)
    frontier = nxt
    if stopped:
        break

# ---- r-translated lookup over short words ----
rhits, rchecked, roverflow = [], 0, 0
for imgs, w in list(seen.items()):
    if len(w) > RLEN or time.time() - T0 > BUDGET + 40:
        continue
    try:
        rim = [r_apply(v) for v in imgs]
    except Overflow:
        roverflow += 1
        continue
    rchecked += 1
    key, dt = normkey(rim)
    if key in table:
        for d2, w2 in table[key].items():
            # W2 = L r W with |det L| = d2 / dt
            ratio = d2 / dt
            rhits.append((ratio, w2, w))

print('ball size', len(seen), 'overflow', overflow, 'stopped_early', stopped)
print('linear-collision hits (|det L| != 1):', len(hits))
for h in hits[:20]:
    print('  HIT', h[3], '|', word_str(h[1]), '| vs |', word_str(h[2]))
print('near misses (fix both axes and (1,-1)):', len(near))
near.sort(key=lambda t: -t[0])
for a, w in near[:10]:
    print('  near', a, '/', len(PROBES), 'probes agree with r |', word_str(w))
print('r-translated words checked', rchecked, 'overflow', roverflow, 'matches', len(rhits))
for ratio, w2, w in rhits[:20]:
    tag = 'uninformative' if ratio == 2 else ('E-IN-N' if ratio == 1 else 'NEW')
    print('  RHIT |det L| =', ratio, tag, '|', word_str(w2), '| = L r |', word_str(w))
print('total time', round(time.time() - T0, 1))
```

## Script `k2verify.py`

```python
#!/usr/bin/env python3
"""Independent re-check of a candidate relation from k2search.py.

Second implementation: sympy.factorint for factoring and sympy.primepi / sympy.prime for the
prime indexing, with no shared code. Usage: k2verify.py 'word1' 'word2' [npoints]
where words use the k2search notation (s<j><X|x|Y|y|W|D>, leftmost letter applied FIRST, as in k2search).
It tests, on random integer points, whether word1 = L o word2 for a single linear L,
and prints det L.
"""
import sys, random
from fractions import Fraction as Fr
from sympy import factorint, primepi, prime


def k_of_prime(p):
    n = int(primepi(p))
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def prime_of_k(k):
    return int(prime(2 * k if k > 0 else 1 - 2 * k))


def sig(m, j):
    m = Fr(m)
    if m == 0 or j == 0:
        return m
    out = Fr(-1 if m < 0 else 1)
    for part, sgn in ((abs(m.numerator), 1), (m.denominator, -1)):
        for p, e in factorint(part).items():
            out *= Fr(prime_of_k(k_of_prime(p) + j)) ** (sgn * e)
    return out


MATS = {'P': ((1, 2), (0, 1)), 'p': ((1, -2), (0, 1)), 'Q': ((1, 0), (2, 1)), 'q': ((1, 0), (-2, 1)),
        'X': ((1, 1), (0, 1)), 'x': ((1, -1), (0, 1)), 'Y': ((1, 0), (1, 1)),
        'y': ((1, 0), (-1, 1)), 'W': ((0, 1), (1, 0)), 'D': ((-1, 0), (0, 1))}


def letter(tok, v):
    j, M = int(tok[1:-1]), MATS[tok[-1]]
    a, b = sig(v[0], -j), sig(v[1], -j)
    a, b = M[0][0] * a + M[0][1] * b, M[1][0] * a + M[1][1] * b
    return (sig(a, j), sig(b, j))


def word(w, v):
    for tok in w.split():  # k2search order: first letter is applied first
        v = letter(tok, v)
    return v


w1, w2 = sys.argv[1], sys.argv[2]
A1, B1 = word(w1, (1, 0)), word(w1, (0, 1))
A2, B2 = word(w2, (1, 0)), word(w2, (0, 1))
# L maps w2-images to w1-images: L [A2 B2] = [A1 B1]
det2 = A2[0] * B2[1] - B2[0] * A2[1]
inv2 = ((B2[1] / det2, -B2[0] / det2), (-A2[1] / det2, A2[0] / det2))
C = ((A1[0], B1[0]), (A1[1], B1[1]))
L = tuple(tuple(sum(C[i][k] * inv2[k][j] for k in range(2)) for j in range(2)) for i in range(2))
print('L =', L, 'det L =', L[0][0] * L[1][1] - L[0][1] * L[1][0])
random.seed(1)
bad = 0
for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 60):
    v = (random.randint(-40, 40), random.randint(-40, 40))
    if v == (0, 0):
        continue
    u2 = word(w2, v)
    lhs = word(w1, v)
    rhs = (L[0][0] * u2[0] + L[0][1] * u2[1], L[1][0] * u2[0] + L[1][1] * u2[1])
    if lhs != rhs:
        bad += 1
        print('MISMATCH at', v, lhs, rhs)
        break
print('mismatches:', bad)
```

### tab.out

```text
k(1,1) = (Fraction(2, 1), Fraction(1, 1))  r on probes: [('1', '0'), ('0', '1'), ('168', '-10'), ('1', '-1'), ('-29', '200'), ('701', '-2402'), ('-2097', '18958'), ('-346', '201'), ('-32', '95'), ('4216', '2118')]
generators: 14  wide = False  J = 1  MAXLEN = 5  RLEN = 1
level 1 new elements 14 time 0.4 overflow 0
level 2 new elements 158 time 0.4 overflow 0
level 3 new elements 1646 time 1.0 overflow 0
level 4 new elements 16789 time 6.0 overflow 36
level 5 new elements 167723 time 54.9 overflow 2170
ball size 186331 overflow 2170 stopped_early False
linear-collision hits (|det L| != 1): 0
near misses (fix both axes and (1,-1)): 185
r-translated words checked 14 overflow 1 matches 0
TABULATION over 185 near misses (words in N_0 fixing both axes and (1,-1))
  line (1, 1) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (1, 2) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (2, 1) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (1, 3) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (3, 1) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (2, 3) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  line (1, -2) : evaluated 185 kept 0 content ratio 1: 185 scalars when kept: {}
  r on (1, 1) -> ('168', '-10') line kept False scalar None content ratio 2
  r on (1, 2) -> ('701', '-2402') line kept False scalar None content ratio 1
  r on (2, 1) -> ('-29', '200') line kept False scalar None content ratio 1
  r on (1, 3) -> ('1436', '678') line kept False scalar None content ratio 2
  r on (3, 1) -> ('6135', '-5567') line kept False scalar None content ratio 1
  r on (2, 3) -> ('3715', '-2682') line kept False scalar None content ratio 1
  r on (1, -2) -> ('-49', '-46') line kept False scalar None content ratio 1
total time 55.1
```

## Rational-shear search (second round): blindness pre-check, done before any run

Searched subgroup: `G = <σ_2^j x_12(q) σ_2^-j, σ_2^j x_21(q) σ_2^-j, W, D>` with `|j| <= 1`. There are two
choices of `q`:
- `q in Q_2 = {±1, ±2, ±1/2}`;
- `q in Q_23 = Q_2 ∪ {±3, ±1/3}`.

`G ⊆ N` by Attempt 5. Put `S = {σ^j(p) : p | q, |j| <= 1}`, where `p | q` means `p` divides the numerator or
the denominator of `q`. So `S = {2, 3, 5}` for `Q_2` and `S = {2, 3, 5, 7}` for `Q_23`.

Every invariant known to be preserved by all generators of `G`, and whether `r` violates it:

| invariant | preserved by `G` | `r` |
|---|---|---|
| degree 0 (commutes with scalars) | yes | yes |
| maps lines through 0 to lines, linearly on each | yes | yes |
| `v_p(content)` for primes `p ∉ S`: `σ_2^j x(q) σ_2^-j` changes content only at primes `σ^j(p)`, `p \| q` | yes | yes: `r` changes content only at 2, which is in `S` |
| the set `Z[1/S]^2` | yes | yes: its factors lie in `GL_2(Z[1/2])` or are `σ_2`-conjugates of `GL_2(Z)` |
| full content | no (`x_12(1/2)`) | — |
| pair determinants | no (`σ_2 x_21(1) x_12(1) σ_2^-1` doubles the axis-pair determinant, Attempt 1) | — |
| axis character `χ`, three-line scalar `χ_3` | not known to be invariant | `χ(r) = χ_3(r) = 1`, so no violation either way |
| scalars on `ℓ_x, ℓ_y, ℓ_-` | not an invariant | `(1,1,1)`, as for the identity |

`r` violates none of these, so the search is not blind by any known invariant.
- *Test 1 is not blind.* The quotient `V_1 V_2^-1 = L` must preserve `p`-content for `p ∉ S`, so
  `L in GL_2(Z[1/S])`. Then `|det L|` is an `S`-unit and may be 2.
- *Test 2 is not blind.* `L r in G` forces only `L in GL_2(Z_(p))` for `p ∉ S`.

**Calibration inside `G`.** Take the planted target `P = X(-1) ∘ σ_2^-1 X(1) σ_2`, word `s-1X(1) s0X(-1)`.
It lies in `G` and fixes both axes and `(1,-1)`.
- Run `qcal` (`Q_2`, length <= 3, 38,619 elements) found all 39 of 39 translated words with `|det L| = 1`.
- It counted 902 words equal on the probes to a linear map of determinant ±1 other than `±I`, for example
  `x_12(1/2)` itself.
- It found no linear hit with `|det L| != 1`, as is necessary unless a hidden relation exists.

### Results (runs `qrunA`, `qrunB`, `qrunC`; MSI, single core, each run under 9 minutes; this round used about 25 minutes)

| run | `q` set | `J` | generators | levels complete | ball | overflow | linear hits, `\|det L\| != 1` | linear, `\|det\| = 1`, not `±I` | `r`-translated (length <= 2) | `r` hits |
|---|---|---|---|---|---|---|---|---|---|---|
| qcal (planted) | `Q_2` | 1 | 38 | 3 | 38,619 | 4 | 0 | 902 | 39 (planted target) | 39, all `\|det L\| = 1` |
| qrunA | `Q_2` | 1 | 38 | 3, and 448,115 of length 4 | 486,734 | 1,806 | 0 | 1,794 | 1,162 | 0 |
| qrunB | `Q_23` | 1 | 62 | 3, and 342,052 of length 4 | 518,003 | 3,418 | 0 | 3,884 | 3,039 | 0 |
| qrunC | `Q_2` | 2 | 62 | 3, and 246,641 of length 4 | 437,130 | 64,413 | 0 | 912 | 2,656 | 0 |

**Reading.** Within the searched words, every hit would be sound. No known invariant makes the search
blind, and the calibration planted inside `G` is found.
- Among these words, no product of rational-shear conjugates of length <= 3 is a linear map with
  `|det| != 1`. The same holds for part of length 4.
- No pair of such words differs by such a map.
- No short word `V'` has `L r V'` in the ball for any `L`.
- This is bounded evidence, consistent with `r ∉ N`, that is with `2 ∉ I_2`. It is not a proof: the lengths
  are short, since each rational-shear generator costs a lot of fraction arithmetic, and only `|j| <= 2` is
  covered.

### qcal.out

```text
generators 38 J 1 QSET two MAXLEN 3 RLEN 1 target planted s-1X(1) s0X(-1)
level 1 new 38 time 0.4 overflow 0
level 2 new 1202 time 1.4 overflow 0
level 3 new 37378 time 32.4 overflow 4
ball 38619 overflow 4 stopped_early False
linear hits |det L| != 1: 0
calibration B: words equal to a linear map of |det| 1 other than +-I: 902
near misses (fix both axes and (1,-1)): 16
target-translated words checked 39 overflow 0 matches 39
total time 32.5
  THIT |det L| = 1 planted | s-1X(1) | = L target | 
  THIT |det L| = 1 planted | s-1X(2) | = L target | s-1X(1)
  THIT |det L| = 1 planted | s-1X(1) s-1Y(-2) | = L target | s-1Y(1)
  THIT |det L| = 1 planted |  | = L target | s-1X(-1)
  THIT |det L| = 1 planted | s-1X(-1) | = L target | s-1Y(-1)
```

### qrunA.out

```text
generators 38 J 1 QSET two MAXLEN 4 RLEN 2 target r
level 1 new 38 time 0.4 overflow 0
level 2 new 1202 time 1.4 overflow 0
level 3 new 37378 time 33.5 overflow 4
level 4 new 448115 time 470.0 overflow 1806
ball 486734 overflow 1806 stopped_early True
linear hits |det L| != 1: 0
calibration B: words equal to a linear map of |det| 1 other than +-I: 1794
near misses (fix both axes and (1,-1)): 144
target-translated words checked 1162 overflow 79 matches 0
total time 473.1
```

### qrunB.out

```text
generators 62 J 1 QSET twothree MAXLEN 4 RLEN 2 target r
level 1 new 62 time 0.4 overflow 0
level 2 new 3290 time 3.2 overflow 0
level 3 new 172598 time 154.8 overflow 180
level 4 new 342052 time 470.0 overflow 3418
ball 518003 overflow 3418 stopped_early True
linear hits |det L| != 1: 0
calibration B: words equal to a linear map of |det| 1 other than +-I: 3884
near misses (fix both axes and (1,-1)): 89
target-translated words checked 3039 overflow 314 matches 0
total time 480.1
```

### qrunC.out

```text
generators 62 J 2 QSET two MAXLEN 4 RLEN 2 target r
level 1 new 62 time 0.4 overflow 0
level 2 new 3440 time 3.4 overflow 2
level 3 new 186986 time 173.2 overflow 2830
level 4 new 246641 time 470.0 overflow 64413
ball 437130 overflow 64413 stopped_early True
linear hits |det L| != 1: 0
calibration B: words equal to a linear map of |det| 1 other than +-I: 912
near misses (fix both axes and (1,-1)): 327
target-translated words checked 2656 overflow 847 matches 0
total time 483.6
```

### Script `k2searchq.py`

```python
#!/usr/bin/env python3
"""Informative search for a hidden relation in K_2, with RATIONAL shears.

N = <sigma_2^j SL_2(Q) sigma_2^-j, D> (Attempt 5). Generators here:
sigma_2^j x_12(q) sigma_2^-j and sigma_2^j x_21(q) sigma_2^-j, |j| <= J, q in QSET, plus W and D.
Same two tests as k2search.py (left-linear key; r-translated key). Planted calibration:
the target r is replaced by an element PLANTED of the searched subgroup, which must be found
with |det L| = 1; and linear collisions with |det L| = 1 and L != +-I are counted.
Usage: k2searchq.py BUDGET MAXLEN J QSET RLEN MAXELTS [planted]
  QSET: 'two' = {+-1, +-2, +-1/2}, 'twothree' = {+-1, +-2, +-1/2, +-3, +-1/3}
"""
import sys, time, bisect
from fractions import Fraction as Fr

T0 = time.time()
BUDGET = float(sys.argv[1]); MAXLEN = int(sys.argv[2]); J = int(sys.argv[3])
QSET = sys.argv[4]; RLEN = int(sys.argv[5]); MAXELTS = int(sys.argv[6])
PLANT = len(sys.argv) > 7 and sys.argv[7] == 'planted'

LIMIT = 5_000_000
sieve = bytearray([1]) * (LIMIT + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(LIMIT ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(range(i * i, LIMIT + 1, i)))
PR = [i for i in range(LIMIT + 1) if sieve[i]]
del sieve


class Overflow(Exception):
    pass


def idx_to_k(n):
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def k_to_idx(k):
    return 2 * k if k > 0 else 1 - 2 * k


FCACHE = {}


def factor(m):
    if m in FCACHE:
        return FCACHE[m]
    orig, out = m, []
    for p in PR:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            out.append((p, e))
    if m > 1:
        if m > LIMIT:
            raise Overflow()
        out.append((m, 1))
    res = tuple(out)
    if len(FCACHE) < 2_000_000:
        FCACHE[orig] = res
    return res


def sig_int(m, j):
    if m == 0 or j == 0:
        return m
    s, a = (1, m) if m > 0 else (-1, -m)
    r = 1
    for p, e in factor(a):
        n2 = k_to_idx(idx_to_k(bisect.bisect_left(PR, p) + 1) + j)
        if n2 > len(PR):
            raise Overflow()
        r *= PR[n2 - 1] ** e
        if r > 10 ** 15:
            raise Overflow()
    return s * r


def sig(q, j):
    if j == 0:
        return q
    q = Fr(q)
    return Fr(sig_int(q.numerator, j), sig_int(q.denominator, j))


def mat_apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def gen_apply(g, v):
    j, M = g
    if j == 0:
        return mat_apply(M, v)
    w = mat_apply(M, (sig(v[0], -j), sig(v[1], -j)))
    return (sig(w[0], j), sig(w[1], j))


QS = [Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(1, 2), Fr(-1, 2)]
if QSET == 'twothree':
    QS += [Fr(3), Fr(-3), Fr(1, 3), Fr(-1, 3)]
GENS, NAMES = [], []
for j in range(-J, J + 1):
    for q in QS:
        GENS.append((j, ((Fr(1), q), (Fr(0), Fr(1))))); NAMES.append('s%dX(%s)' % (j, q))
        GENS.append((j, ((Fr(1), Fr(0)), (q, Fr(1))))); NAMES.append('s%dY(%s)' % (j, q))
Wm = ((0, 1), (1, 0)); Dm = ((-1, 0), (0, 1))
GENS += [(0, Wm), (0, Dm)]; NAMES += ['W', 'D']
INV = []
for g in GENS:
    j, M = g
    if M in (Wm, Dm):
        INV.append(GENS.index(g))
    else:
        Mi = ((M[0][0], -M[0][1]), (-M[1][0], M[1][1]))
        INV.append(GENS.index((j, Mi)))
NG = len(GENS)
PROBES = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 5), (5, -3), (7, 2), (2, 9)]
PROBES = [(Fr(a), Fr(b)) for a, b in PROBES]


def normkey(imgs):
    (a, c), (b, d) = imgs[0], imgs[1]
    det = a * d - b * c
    if det == 0:
        return None, None, None
    key = tuple(((d * x - b * y) / det, (-c * x + a * y) / det) for (x, y) in imgs[2:])
    return key, abs(det), (a, b, c, d)


def wstr(w):
    return ' '.join(NAMES[i] for i in w)


# ---- target r (Attempt 3) ----
G2 = ((2, 1), (1, 1)); SG2inv = ((Fr(1, 2), Fr(-1, 2)), (Fr(-1, 2), Fr(3, 2)))
Mm = ((1, 0), (-1, -1))
assert sig(2, 1) == 3 and sig(5, 1) == 2


def k_apply(v):
    w = mat_apply(G2, (sig(v[0], -1), sig(v[1], -1)))
    return mat_apply(SG2inv, (sig(w[0], 1), sig(w[1], 1)))


def r_apply(v):
    v = (2 * v[0], 2 * v[1])
    v = mat_apply(Wm, mat_apply(Mm, k_apply(mat_apply(Mm, mat_apply(Wm, v)))))
    v = mat_apply(Mm, k_apply(mat_apply(Mm, v)))
    return k_apply(v)


for v in ((1, 0), (0, 1), (1, -1), (3, -3)):
    assert r_apply((Fr(v[0]), Fr(v[1]))) == (v[0], v[1])

TARGET, TNAME = r_apply, 'r'
if PLANT:
    # planted target inside the searched subgroup: the near miss X(-1) o (sigma_2^-1 X(1) sigma_2)
    PW = [NAMES.index('s-1X(1)'), NAMES.index('s0X(-1)')]

    def planted(v):
        for gi in PW:
            v = gen_apply(GENS[gi], v)
        return v
    TARGET, TNAME = planted, 'planted ' + wstr(PW)
print('generators', NG, 'J', J, 'QSET', QSET, 'MAXLEN', MAXLEN, 'RLEN', RLEN, 'target', TNAME, flush=True)

ident = tuple(PROBES)
seen = {ident: ()}
frontier = [(ident, ())]
k0, d0, _ = normkey(ident)
table = {k0: {d0: ()}}
hits, det1_nontriv, near, overflow = [], 0, 0, 0
stopped = False
for L in range(1, MAXLEN + 1):
    nxt = []
    for imgs, w in frontier:
        if time.time() - T0 > BUDGET or len(seen) > MAXELTS:
            stopped = True
            break
        last = w[-1] if w else None
        for gi in range(NG):
            if last is not None and gi == INV[last]:
                continue
            try:
                new = tuple(gen_apply(GENS[gi], v) for v in imgs)
            except Overflow:
                overflow += 1
                continue
            if new in seen:
                continue
            nw = w + (gi,)
            seen[new] = nw
            nxt.append((new, nw))
            key, dt, ab = normkey(new)
            if key is None:
                continue
            ent = table.setdefault(key, {})
            for d2, w2 in ent.items():
                if d2 != dt:
                    hits.append((nw, w2, dt / d2))
            if key == k0 and dt == 1 and ab not in ((1, 0, 0, 1), (-1, 0, 0, -1)):
                det1_nontriv += 1
            ent.setdefault(dt, nw)
            if new[0] == (1, 0) and new[1] == (0, 1) and new[3] == (1, -1):
                near += 1
    print('level', L, 'new', len(nxt), 'time', round(time.time() - T0, 1), 'overflow', overflow, flush=True)
    frontier = nxt
    if stopped:
        break

rhits, rchecked, rover = [], 0, 0
for imgs, w in list(seen.items()):
    if len(w) > RLEN or time.time() - T0 > BUDGET + 60:
        continue
    try:
        rim = [TARGET(v) for v in imgs]
    except Overflow:
        rover += 1
        continue
    rchecked += 1
    key, dt, _ = normkey(rim)
    if key in table:
        for d2, w2 in table[key].items():
            rhits.append((d2 / dt, w2, w))

print('ball', len(seen), 'overflow', overflow, 'stopped_early', stopped)
print('linear hits |det L| != 1:', len(hits))
for a, b, ratio in hits[:20]:
    print('  HIT |det L| =', ratio, '|', wstr(a), '| = L |', wstr(b))
print('calibration B: words equal to a linear map of |det| 1 other than +-I:', det1_nontriv)
print('near misses (fix both axes and (1,-1)):', near)
print('target-translated words checked', rchecked, 'overflow', rover, 'matches', len(rhits))
informative = [h for h in rhits if h[0] != 2] if not PLANT else rhits
for ratio, w2, w in rhits[:20]:
    tag = ('uninformative' if ratio == 2 else ('E-IN-N' if ratio == 1 else 'NEW')) if not PLANT else 'planted'
    print('  THIT |det L| =', ratio, tag, '|', wstr(w2), '| = L target |', wstr(w))
print('total time', round(time.time() - T0, 1))
```
