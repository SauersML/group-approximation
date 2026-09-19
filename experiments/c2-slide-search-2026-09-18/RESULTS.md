# (C2) lift obstruction and slide search: computation record (2026-09-18, w12-048)

Node: `research/c2-one-relator-lift-presentations-are-obstructed.md`, with proof in `-proof.md`.
Pure Python 3 plus numpy, single-threaded. `verify_unimodular.py` is w11-048's normal form for
`G = F_4 ⋊ Z`, copied so that the imports resolve.

Only `lift.py` is an input to the proof. It checks the four free reductions (`basics()`) and the
explicit class of the basis-word lift for the `c`- and `a`-eliminations (`check_all()`). The
coset invariant of the node (every lift has class `±(Hg − 2H)` in `Z[H\G]`) makes the
`(a,b)`-membership diagnostics of `sl_test.py`, `sl_exact.py` and `stallings.py` unnecessary. They are
kept as a record of the superseded route.

## Reproduce

```sh
python3 lift.py                    # inputs of the proof, class of f0(r), Fox checks (< 1 s)
python3 lift_search.py 4 4 2 1     # exact lift search, 790,608 lifts (a few minutes)
python3 jtest.py c A5 3            # module test in F_p[Q]; loop over A5 PSL27 S5, p = 3 5 7 (jtest_c.out)
# superseded (a,b)-membership diagnostics:
python3 sl_test.py A5 S5 PSL27 A6 PSL211   # T_i membership in finite quotients (~1 min)
python3 sl_exact.py 8 1            # T_2 is not a beta,k-word of length <= 16 (~30 s)
python3 stallings.py 6 1           # Stallings windows |n| <= 6 (~5 s)
```

## Outputs

`lift.py`:
```
u1' = eDDEddAbDBeDDEddad 18
R0 = f0(u1') len 38
predicted [R0] {('R', 1): 1, ('rS', 0): -1, ('QSqqR', -1): -1}
x fox check True
y fox check True
eliminate c relator eDDEddAbDBeDDEddad 18 exp sums {'a': 0, 'b': 0, 'd': 0, 'e': 0} class {('R', 1): 1, ('rS', 0): -1, ('QSqqR', -1): -1} fox check True
eliminate a relator eDDEddbCBeDDEddbDcBd 20 exp sums {'b': 0, 'c': 0, 'd': 0, 'e': 0} class {('R', 1): 1, ('rS', 0): -1, ('rSqPRSrpQ', 0): -1} fox check True
BAS(u0) == w: True
BAS(u1) == g w g^-1: True
e(u0) = [-1, 0, 1, 0, 0] e(u1) = [-2, 0, 2, 0, 0] e(u1) == 2 e(u0): True
```
The keys are normal forms (fibre word in `p,q,r,s`, y-exponent) of `g = Xy`, `P_1 = xyXY` and
`P_2 = XyyxYXXyyxYXYYYxxyXY`.

`sl_test.py` (superseded): the counts are homomorphisms `G → Q` with image of order at least 3 that separate
the element from the image of `S = ⟨bDB, eDDEdd⟩` (after conjugating by `kA`).
```
A5 homs |im|>=3 65 non-member counts {'gP1^-1': 5, 'gP2^-1': 0, 'P1P2^-1': 5}
S5 homs |im|>=3 150 non-member counts {'gP1^-1': 21, 'gP2^-1': 0, 'P1P2^-1': 21}
PSL27 homs |im|>=3 185 non-member counts {'gP1^-1': 9, 'gP2^-1': 0, 'P1P2^-1': 9}
A6 homs |im|>=3 386 non-member counts {'gP1^-1': 22, 'gP2^-1': 0, 'P1P2^-1': 22}
PSL211 homs |im|>=3 690 non-member counts {'gP1^-1': 18, 'gP2^-1': 0, 'P1P2^-1': 18}
```

Image orders of all homomorphisms `G → Q`, as order: count:
- `A5`: 5:34, 3:23, 2:17, 12:6, 4:2, 1:1.
- `S5`: 4:46, 6:33, 2:29, 5:29, 3:23, 20:13, 12:6, 1:1.
- `PSL27`: 7:62, 3:59, 4:52, 2:23, 21:6, 12:6, 1:1.
- `A6`: 5:154, 4:100, 3:86, 2:47, 12:18, 36:16, 9:12, 1:1.
- `PSL211`: 5:274, 11:142, 6:123, 3:113, 2:57, 55:20, 12:12, 4:6, 1:1.

`stallings.py 6 1`: fibre target length 20. Rank `2N+1` for `N = 0..6`, and membership is
`False` for every window. The vertex counts are 4, 33, 82, 181, 418, 957 and 2229.

`sl_exact.py 8 1`: 13121 words per side, `no expression with |s1|,|s2| <= 8`.

`lift_search.py`: see `lift_search.out`. No hits among 790,608 candidates. The minimum cyclic
length over modified candidates is 56.

`jtest_c.out`: `κ + h ∈ J = c'·ZG^4`, tested for `A5`, `PSL27` and `S5` at `p = 3, 5, 7`. There are
0 obstructed homomorphisms in every case.

## Slide route with the b-coordinate (`slide.py`, `homs.py`, `climb.py`)

The counts of `t ≠ 1` homomorphisms for Γ'' built from the unit coordinate `c` and from `b` are
equal:
- A5: 40
- S5: 40
- PSL27: 16
- A6: 52
- PGL27: 16
- PSL211: 68
- S6: 144

`climb.py` hill-climbs over κ-moves in the certificate coset. It can reach states with no `t ≠ 1`
homomorphism to A5 and PSL27, but every state reached still has one in some other group of the
list. The route was abandoned, since finite quotients cannot prove `t = 1`.
