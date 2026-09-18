---
rg: 2
id: fpbs-tree-projected-chain-deficient-slot-second-moment-proof
kind: route
title: Slot second moment with chain-number collision caps and a pointwise generic row for letter sets with many chains
target: fpbs-tree-projected-chain-deficient-slot-second-moment
requires:
  - fpbs-tree-projected-pollard-slot-second-moment
  - fpbs-tree-projected-bidirectional-slot-second-moment
  - fpbs-tree-projected-vertical-slot-second-moment
  - fpbs-tree-projected-oriented-second-moment-thresholds
artifacts:
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/engine_h.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/certify_h.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/pwcheck.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/cert_chain.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/pwcheck.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/engine_w.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/buildw.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/runwpw.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/runwpw.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/exact9.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/exact9.txt
---

Notation and everything not restated here are as in
`fpbs-tree-projected-pollard-slot-second-moment-proof` ("the Pollard proof") and the
bidirectional proof it builds on. `L = {a^±1, b^±1}`, `x = 1/p`, `D_(t^-1) = -D_t`,
`|D_t| = m`, vertical part `{(1, ±c)}` with `c != 0`, `J = 1`, `K = 1`, runs
`R = {-1, 0, 1}`, offset classes `-c, 0, c, G` plus the column `NZ`.

`engine_h.py` is `engine_p.py` of the Pollard claim with three changes:
1. a global `KAP` (default `2`) replacing the constant `2` of the non-AP gain, in the
   descriptor value and in the autocorrelation caps;
2. the flag `PNX` (Lemma 12), active only when `NONAP` is on;
3. in the pointwise row (`PW`) a level-2 gain is parametrised when its cap is
   `m - KAP` (the Pollard file tested `cap == m - 2`, which is the same at `KAP = 2`).

With `KAP = 2` and `PNX` off it is `engine_p.py`. With `KAP = 2` and `PNX` on it gives
the same matrices for `m >= 6`, since `m (m - 2) >= P_neq(m)` there (Lemma 12).

## 1. Chain number

For a finite `D ⊂ Z` and `gamma != 0`, the *`gamma`-chains* of `D` are the components
of the graph on `D` with edges `x -> x + gamma` (both in `D`). Put
`chi_gamma(D)` = number of chains and `chi(D) = min_(gamma != 0) chi_gamma(D)`.

**Lemma 10.** `|D ∩ (D - gamma)| = |D| - chi_gamma(D)`. Hence
`r_D(gamma) := #{(u, w) in D^2 : u - w = gamma} <= |D| - chi(D)` for every `gamma != 0`,
and `chi(-D) = chi(D)`, `chi(D + t) = chi(D)`.

*Proof.* The graph is a disjoint union of paths (Lemma 9 of the Pollard proof), and a
union of `k` paths on `|D|` vertices has `|D| - k` edges. The edges are the pairs
`(x, x + gamma)`, counted by `|D ∩ (D - gamma)| = r_D(gamma)`. Negation maps
`gamma`-chains of `D` to `(-gamma)`-chains of `-D`, which are the `gamma`-chains read
backwards. ∎

So `chi(D) >= 2` says that `D` is not an arithmetic progression (Lemma 9), and
`chi(D) >= k` says that `D` is not a union of fewer than `k` arithmetic progressions
with one common difference. The hypothesis of the claim is `chi(D_a), chi(D_b) >= k`.
Every fibre letter `t, o1, o2` has one of the sets `±D_a`, `±D_b`, so each satisfies
`r(gamma) <= m - k` for `gamma != 0`.

## 2. The gains under `chi >= k` (engine `KAP = k`)

**Lemma 11 (collision gain).** In the forest bound, a single-variable condition
`y = x + gamma` with `dom x = dom y` and `gamma = alpha c + beta h` provably nonzero
(the test `_nonzero` of Lemma 6 of the bidirectional proof, case 4) confines `x` to
`{x in D : x + gamma in D}`, of size `<= m - k` by Lemma 10.

*Proof.* This is Lemma 9's application in the Pollard proof with `m - 2` replaced by the
bound of Lemma 10. ∎

**Lemma 12 (Pollard pair under `chi >= k`, flag `PNX`).** Let `A ⊂ Z` with `|A| = m`,
`chi(A) >= k`, `S` a set of `m` rationals and `e != 0`. Then

```text
#{(u, w) in A x A : u != w, e (u - w) in S}  <=  min( P_neq(m), m (m - k) ).
```

*Proof.* The first bound is Lemma 7 part 2 of the Pollard proof. For the second, the
count is `Σ_(s in S, s != 0) r_A(s / e)`. It has at most `m` terms, each at most
`m - k` by Lemma 10. ∎

Lemma 8 of the Pollard proof (pair families) then holds with `P_neq(m)` replaced by
`min(P_neq(m), m (m - k))`: its proof uses Lemma 7 part 2 only as an upper bound on the
number of choices of the revealed pair. `count_bound_pol` evaluates candidates with this
value at `M_REF = m`. As before, every candidate is a valid bound, so the minimum is too.
The engine's assertion that each NZ-refined term stays above the exact `h' = 0` count
(Lemma 5 of the bidirectional proof) holds in every run below.

Numbers: `P_neq(9) = 56` and `9 · 6 = 54`; `P_neq(8) = 44` and `8 · 4 = 32`;
`P_neq(7) = 34` and `7 · 2 = 14`; `P_neq(6) = 24` and `6 · 1 = 6`.

## 3. The pointwise generic row (flag `PW`)

The Pollard claim recorded `PW` as a float experiment. Here it is part of the
certificate, so its soundness is proved.

Fix a letter context and a generic start offset `h`, i.e. `h not in {-c, 0, c}`. Then
`h + j c != 0` for `|j| <= 1`. For a class `j` let `M_j(h)` be the exact pair mass of one
block from `h` into class `j`: the sum over pairs of block data, with the final offset
`h'` in class `j`, of `p^(#edges of the union)`. Let `M_NZ(h)` be the same sum over all
`h' != 0`. The bidirectional proof bounds each `M_j(h)` by the sum of terms
`mult · p^ne (x-1)^nq · N`, and `N` by a counting bound. Two things change.

**(a) Parametrised gains.** Suppose the counting bound of a term takes a gain on the
tree of a free variable `x` from a condition `y = s x + beta h + alpha c`,
`s, beta in {±1}` (`param_of`). Then the number of admissible values of `x` is
exactly

```text
#{x in D_(dom x) : s x + beta h + alpha c in D_(dom y)}  =  R_kappa(h + j c),
R_kappa(g) = #{(u, w) in D_d1 x D_d2 : s1 u + s2 w = g},
```

with `kappa = ((dom y, beta), (dom x, -beta s))` and `j = beta alpha`. (Put `u = y`,
`w = x`: `beta y - beta s x = beta^2 h + beta alpha c = h + j c`.) The tree of `x`
contributes `(m-1)^(size-1)` times the number of values of its root. So the term's
bound stays valid with the gain factor (`m - 1` for a level-1 gain, `m - k` for a
level-2 gain) replaced by `R_kappa(h + j c)`. `_forest_rig` returns the candidates
whose cap equals the gain factor actually used. `count_bound_pol` removes exactly
that factor from the descriptor and records `kappa, j`. At most one factor per term is
parametrised, and the others keep their worst-case values.

**(b) Exact subtraction.** Take two slots without excursion and `Q = {}`. The pairs of
steps `(ps, Ps) in D_t^2` of the two paths, with runs `r1, r2`, land at
`h' = h + (r2 - r1) c + Ps - ps`. The term with `Q = {}` counts all `m^2` pairs with
coefficient `p^ne`. The number landing at `h' = k c` is exactly
`#{(ps, Ps) : ps - Ps = h + (r2 - r1 - k) c} = R_((t,-1),(t,1))(h + (r2 - r1 - k) c)`.
Only one vertical edge per path occurs, so there are no internal coincidences, and the
count is exact. The engine subtracts it from the generic target, for every `k`, and
from `NZ` for `k = 0`. These are the only negative parametrised coefficients. All
other parametrised terms are upper bounds with positive coefficients, because
`mult > 0` and `x - 1 > 0`.

**(c) Caps.** `R_kappa(g)` has `g = h + j c`. For an autocorrelation (`d1 = d2`,
`s1 = -s2`) with `|j| <= 1`, `g != 0`, so `R <= m - k` by Lemma 10. The other caps
are those of `param_cap`, unchanged from the Pollard file:
* `m - 1` for `D` against `-D` and for distinct directions (rigidity: never
  translates);
* `m - 1` or `m` for distinct labels with the same direction;
* `m` for `|j| > 1`.

`pwcheck.py` asserts every cap on every concrete decoration it tests.

**Lemma 13.** For every generic `h`, the vector `R(h) = (R_kappa(h + j c))_(kappa,j)`
lies in the box `B = Π [0, cap]`, and for `j in {-c, 0, c, G, NZ}`

```text
M_j(h)  <=  C_G[j] + Σ_kappa lin_kappa[j] · R_kappa(h + j c),
```

where `C_G` and `lin` are the constant and linear parts of the generic row built by
`engine_h.pair_terms` with `PW` on (`runpw.matrix_pw`).

*Proof.* Sum the valid term bounds of (a), the exact subtraction of (b) and the
unparametrised terms, which are valid for every `h` by the Pollard and bidirectional
proofs. The caps hold by (c). ∎

**Lemma 14 (criterion with a pointwise generic row).** Let `y > 0` be constant on the
classes, and define

```text
b_j(R)   = C_G[j] + Σ_kappa lin_kappa[j] R_kappa          (j in {-c, 0, c, G, NZ}),
Phi_G(y) = sup_(R in B) max { b_0(R) y_0 + Σ_(j != 0) mu_j y_j :
                              0 <= mu_j <= b_j(R)  (j in {-c, c, G}),
                              Σ_(j != 0) mu_j <= b_NZ(R) } .
```

Here `0` is the class `h' = 0`, and `j != 0` runs over `-c, c, G`.
Let `Phi_s` for `s in {-c, 0, c}` be as in the Pollard proof. If `Phi_s(y) < L y_s`
for all four classes, the criterion of the vertical-slot proof gives `p_c <= p`.

*Proof.* The criterion needs, for every start offset `h` in class `s`,
`Σ_j M_j(h) y_j <= Phi_s(y)`, where the mass into `0` enters at its bound and the
other masses satisfy the class and `NZ` capacities. For the special classes this is
the Pollard proof. For generic `h`, Lemma 13 shows that `mu_j = M_j(h)` (`j != 0`) is
feasible for `R = R(h) in B`, and that `M_0(h)` is at most the class-`0` bound. So
`Σ_j M_j(h) y_j <= Phi_G(y)`. ∎

**Exact evaluation of `Phi_G`.** For any multipliers `u_j >= 0` (`j != 0`) and
`u_NZ >= 0` with `u_j + u_NZ >= y_j`, weak duality applied to the inner LP and then
maximised over the box gives

```text
Phi_G(y) <= Σ_(j != 0) u_j C_G[j] + u_NZ C_G[NZ] + C_G[0] y_0
            + Σ_kappa cap_kappa · max(0, lin_kappa[0] y_0 + Σ_(j != 0) u_j lin_kappa[j] + u_NZ lin_kappa[NZ]) .
```

(For fixed `R` the inner LP value is at most `Σ_(j != 0) u_j b_j(R) + u_NZ b_NZ(R)
+ b_0(R) y_0`. This is affine in `R`, and its supremum
over the box takes each coordinate at `0` or at its cap according to the sign of its
coefficient.) `certify_h.py` takes the float duals of the HiGHS solve, rounds them to
rationals, raises each `u_j` to `max(u_j, y_j - u_NZ, 0)` for feasibility, and
evaluates the bound in exact arithmetic (`dual_bound`).

For the special classes `s in {-c, 0, c}` the rows are those of the Pollard proof,
evaluated with the gains of Lemmas 11 and 12. `E.phi` computes them in exact arithmetic
from the class matrix `C` (the constant part of `runpw.matrix_pw`). There the parameters
are not used: for a start offset `h = s`, every parametrised gain was already bounded by
its worst case.

## 4. The certificates

`certify_h.py m k` builds the terms (`engine_h.pair_terms(1, 1, (-1, 0, 1))` with
`NZREF, RIGID, POL, NONAP, PW, PNX` on, `KAP = k`, `M_REF = m`), all in exact rationals.
It then takes `p = floor(10^6 p*_low) / 10^6` with `p*_low < p*(m, 2)` the rational lower
bound `certify_p.pstar_low`. It takes `w = wblock` (the one-block weight lower bound of
the vertical-slot proof) and `L = 3 w^2`. A float power iteration of the monotone map
gives `y`, which is rounded to rationals with denominators at most `10^9`. The generic
row is bounded by `dual_bound` with rounded HiGHS duals, as in section 3. The script
checks `y > 0` and `Phi_s(y) < L y_s` for the four classes, exactly.

Results (`cert_chain.txt`, which also lists `y` and the four ratios):

| `m` | `k` | `p` | `m p` | float `rho/L` | exact margin |
|---|---|---|---|---|---|
| 9 | 3 | 7807/250000 | 0.281052 | 0.997624 | 2.376e-3 |
| 8 | 4 | 4377/125000 | 0.280128 | 0.989054 | 1.095e-2 |
| 7 | 4 | 797/20000 | 0.278950 | 0.989897 | 1.010e-2 |
| 6 | 4 | 46233/1000000 | 0.277398 | 0.987440 | 1.256e-2 |
| 6 | 5 | 46233/1000000 | 0.277398 | 0.961816 | 3.818e-2 |
| 5 | 4 | 55051/1000000 | 0.275255 | 0.976884 | 2.312e-2 |

Each run has 1328 terms, 13 parameters and 12 negative coefficients. `m = 6, k = 5` is
implied by `k = 4` and is listed for the margin.

## 5. Consistency check against exact block sums

`pwcheck.py m k` takes the decorations of `blockcheck_p.decos(m)` and six random rigid
decorations in `[0, 3m)`, and keeps those with `max_(gamma != 0) r_D(gamma) <= m - k` for
both letters. For each it runs the C enumerator `pairx.c` of the Pollard claim, which is
independent of the engine. For every letter context, every generic `h` in the enumerated
range and `p in {0.07, 0.28/m}` it compares:
* the exact masses into `-c, 0, c, G` and `NZ`;
* the bound `C_G[j] + Σ lin_kappa[j] R_kappa(h + j c)`, with `R_kappa` computed on the
  actual letter sets.

It asserts `R_kappa <= cap_kappa`. `pwcheck.py` also samples four rigid decorations
directly under the hypothesis, in `[0, W)` with `W = 3m, 4m, m^2, 2m^2`. `pwcheck.txt`
records the largest ratio of exact mass to bound for each decoration. Every cap
assertion holds. The largest ratios are:
* `(m, k) = (5, 4)`: `0.9926` over 4 decorations;
* `(6, 4)`: `0.9912` over 8;
* `(7, 4)`: `0.9908` over 10;
* `(8, 4)`: `0.9909` over 6;
* `(9, 3)`: `0.9896` over 5.

This is a test of the implementation, not part of the proof.

## 6. Conclusion

Let `(m, k)` be a row of the table in section 4, and let the decoration be rigid with
`chi(D_a), chi(D_b) >= k`. Then each fibre letter set `±D_a, ±D_b` has chain number at
least `k` (Lemma 10). So the collision caps (Lemma 11), the pair bound (Lemma 12) and the
parameter caps (section 3 (c)) hold, and the other bounds are those of the Pollard and
bidirectional proofs, which need only rigidity. By Lemma 14 and the certificate,
`p_c(Cay(Gamma, S)) <= p`. Also `p < p*_low < p*(m, 2) <= p_{2->2} <= p_u` by
`fpbs-tree-projected-oriented-second-moment-thresholds`, whose hypotheses (rank 2,
uniform multiplicity `m`, `v = 2`) hold. So `p_c < p_u`. ∎

## 7. Negative results (not part of the proof)

* *Smaller `k`.* The same script with the next smaller `k` fails. Exact ratios
  `max_s Phi_s(y)/(L y_s)` at the same `p` (`cert_chain.txt`): `(9,2)` 1.00535;
  `(8,3)` 1.00272; `(7,3)` 1.00786; `(6,3)` 1.01217; `(5,3)` 1.01325; `(4,3)` 1.00350;
  `(4,2)` 1.05883; `(3,2)` 1.05727. These are ratios of the rounded `y`, which are
  within `10^-6` of the float radius. `(9,2)` is the whole rigid case at `m = 9`.
  `PW` with exact duals gains `0.0012` over the Pollard file's float `1.0065`, and the
  chain caps supply the rest.
* *Pointwise `W(h)` with an `h`-dependent test function* (`engine_w.py`, `buildw.py`,
  `runwpw.py`, `runwpw.txt`, float). The row of the weighted landing mass
  `W(h) = Σ_h' M(h, h') (r_Da + r_Db)(h')` is built with the same parametrised gains.
  The LP over `y(h) = a + b (r_Da + r_Db)(h)` is optimal at `b = 0`, with value `1.00532`
  at `m = 9`. The constant part of `W` is about `2.10 · 3w^2` per letter, and every parameter
  coefficient is at most `0.011 · 3w^2`. The part of `W` that matters is carried by the order-4
  counts `(1_D * 1_(-D) * 1_D * 1_(-D))(h')`, which one gain parameter per term cannot
  represent.
* *Per-decoration truth* (`exact9.py`, `exact9.txt`, float): at `m = 9` the exact
  per-offset transfer is `0.973-0.979` (over `3 w^2`) for the `chi = 2` decoration
  `{0..7, 9}, {0..6, 8, 9}`, and `0.936-0.956` for random rigid ones.
