---
rg: 2
id: fpbs-mal-modp-promotion-certificates-are-fox-annihilators
kind: claim
title: On a free profinite witness, every mod-p homological lower bound for the depth-0 promotion cost Q_0 = relC(R_L; R_K) is exactly the normalized left annihilator of the single element u = 1 - c - cb, so a positive such bound refutes positive-characteristic sofic Lück approximation for u in F_p[F_2]
distinct_from:
  fpbs-fibered-mod-p-certificates-refute-luck-approximation: that is about rank gradient of free-by-cyclic groups through the Fox block tI - J(phi); this is about the relative cost of the fold pair (L, K = <a, b a b^-2>) through the single Fox derivative d(bab^-2)/db, with an exact finite-level identity instead of an inequality.
  fpbs-mal-floor-iff-deep-promotion-floor: that reduces the target to inf_j Q_j > 0; this bounds Q_0 on profinite witnesses and kills the mod-p homological way of proving Q_0 > 0.
  fpbs-mal-bernoulli-single-stage-floor: that is the open target; this decides nothing about it and removes one class of proofs of its necessary part (D0).
artifacts:
  - research/fpbs-mal-modp-promotion-certificates-are-fox-annihilators-proof.md
  - experiments/fpbs-modp-fox-floor-2026-09-17/foxfloor.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/foxfloor_out.txt
  - experiments/fpbs-modp-fox-floor-2026-09-17/census.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_out.txt
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_big_p2.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_big_p2_out.txt
---

**ESTABLISHED (Theorems 1–3 unconditional; item 4 is an equivalence with a named
open conjecture, not a decision of it).** Proofs are in
`research/fpbs-mal-modp-promotion-certificates-are-fox-annihilators-proof.md`.

**Setting.**
- `L = F(a, b)`, `c = b a b^-2`, `K = <a, c> = phi(L)`. Note that `{b, c}` and
  `{c, cb}` are free bases of `L`.
- `u = 1 - c - cb` in `F[L]`, for a field `F`. This is the Fox derivative `dc/db`.
- A *level* is a finite transitive right `L`-set `V`, with permutation module `F[V]`.
- `k_u(V) = dim_F { y in F[V] : y u = 0 }`, and `t(V)` is the number of `K`-orbits.
- A free profinite witness is `X = lim V_m`, an inverse limit of levels with its
  uniform measure. The action is essentially free.
- `Q_0(X) = relC(R_L; R_K)(X)` is the least cost of a graphing `Phi` inside `R_L`
  with `R_K v Phi = R_L`.

**Theorem 1 (exact finite-level identity).** Let `Y` be a finite graph on `V` with
the `a`- and `c`-edges plus `E` extra edges `v -> v.l_i`, with labels in `L`,
whose loop labels generate the stabilizers. Then, for every field `F`,

```text
E  >=  (t - 1) + codim_F [ T H_1(Y_K;F) in H_1(Schreier(V);F) ]  =  k_u(V).
```

`T` sends each `c`-edge to the path `b a b^-1 b^-1`. The equality is the Fox
computation `ker T = { (-y b, y) : y u = 0 }`, which uses `u (b - 1) = c - 1 + b - ba`.
It is checked by brute force on 900 (level, prime) pairs, with 0 mismatches
(`foxfloor_out.txt`).

**Theorem 2 (floor on witnesses).** For every free profinite witness and every
field `F`:

```text
Q_0(X)  >=  kappa_F(X) := limsup_m  k_u(V_m) / |V_m|.
```

Every graphing is approximated by one that is clopen at some level, and each
such graphing is counted at every finer level. With the w10 weak-containment
theorem (`fpbs-mal-promotion-cost-monotone-under-weak-containment`, on the
erol9w branch), `Q_0(rho) >= kappa_F(X)` for the Bernoulli shift `rho` too.

**Theorem 3 (vanishing on p-towers).**
- If every level group (the image of `L` in `Sym(V_m)`) is a `p`-group, then
  `k_u(V_m) = 0` in characteristic `p` at every level.
- The reason: `u` has augmentation `-1`, so it is a unit of the local ring
  `F_p[P]`.
- The same holds at any level whose `L`-image is trivial.

**Item 4 (what the class of mod-p certificates is worth).** Let `p > 0`.
- Levels of an essentially free profinite witness form a sofic approximation of
  `F_2`. By Theorem 3, a residual `p`-tower of `F_2` is a sofic approximation on
  which `rk(u) = 1` exactly.
- Hence `kappa_{F_p}(X) > 0` for any witness contradicts parts (1)–(2) of the
  positive-characteristic sofic Lück approximation conjecture (Jaikin-Zapirain,
  Conjecture 2.4, for `G = F_2`, `K = F_p`) at the 1x1 matrix `u = 1 - x - y`.
  Here `x = c` and `y = cb` are free generators.
- For normal towers it contradicts Conjecture 1.2 (1)–(2).
- That survey records these parts as known in positive characteristic only for
  amenable `G`. So this is open, not refuted.

**Census (evidence, not proof).** Nothing is bounded away from 0.

| Levels | `k_u/n` |
| --- | --- |
| Random Schreier, `n` up to 6400, `p = 2, 3, 5, 7` and char 0 | `O(1/n)`: `≤ .0006` at `n ≥ 1600`, `p = 2` |
| Sanov 3-adic tower `SL_2(Z/3^k)`, `p = 2` | `.29, .069, .027` |
| Sanov 3-adic tower `SL_2(Z/3^k)`, `p = 3` | `.125, .037` |
| `PSL_2(F_q)`, `p = 2` | fluctuating between `.011` and `.064` for `q ≤ 23`; not nested |

**What dies (class kill, criterion 3).**
- *The class.* Every proof of D0 (`Q_0(rho) > 0`, necessary for the target) that
  certifies generation cost by mod-`p` or rational first homology of finite levels
  of a profinite witness. This includes codimension of the `K`-part of
  `H_1(N_m; F)`, with any field, at any level. The rational case is dead
  unconditionally, and consistent with the recorded Linnell dead end.
- *The invariant.* The Sylvester rank `rk_{V_m}(u)` of one element.
- *The step where every member dies.*
  - Such a certificate equals `k_u(V_m)/|V_m|`, by Theorem 1.
  - A positive limsup of that is a counterexample to Conjecture 2.4(2) over
    `F_p` for `F_2`.
- *What survives.*
  - Non-abelian finite-level certificates. The exact finite-level count is
    `t - 1 + d(N_m / <<K ∩ N_m>>^L)` up to the connecting term, which is the
    minimal number of generators rather than its mod-`p` abelianization.
  - Deep-label (D1) arguments. These are untouched.
