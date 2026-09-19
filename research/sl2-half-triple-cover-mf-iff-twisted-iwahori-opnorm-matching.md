---
rg: 2
id: sl2-half-triple-cover-mf-iff-twisted-iwahori-opnorm-matching
kind: claim
title: For SL_2(Z[1/2]), each Deligne cover W_m is MF iff two exact PSL_2(Z) representations admit an asymptotic twisted Iwahori square-root matching, and an integer winding confines these matchings
artifacts:
  - experiments/deligne-sl2-calibration-2026-09-17/lifts.py
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/match.py
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/control_pi.py
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/results.log
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/verify_below_profile.py
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/refine_witness.py
  - experiments/sl2-twisted-iwahori-opnorm-2026-09-17/witness_O3E3E3.npz
distinct_from:
  iwahori-local-global-defect-question: that is the untwisted Hilbert--Schmidt square-root gluing (stability of SL_2(Z[1/2])); this is the operator-norm gluing twisted by the central character gamma = e^{-i theta/6}, whose zero set decides MF of the covers.
  finite-index-double-theorem-misses-iwahori-twist: that shows a finite-index doubling theorem misses the Iwahori twist sigma(u) = u^2; this gives the exact central-character-twisted matching problem that twist produces, and proves it is equivalent to MF.
  far-sector-vertex-handled-edge-is-square-root: that reduces the HS far sector to the edge square root via vertex stability; this does the operator-norm, twisted-sector version, where the vertices are exactified by finite-spectrum functional calculus.
  sl2-half-deligne-monomial-third-floor-calibration: that measures the monomial cellular floor of kappa/3 on finite Schreier complexes; this reformulates MF of W_3 itself, with no monomial restriction.
  central-extension-twisted-sector-criterion: that proves MF of a central extension iff a twisted asymptotic sector exists, in general; this makes the sector explicit for SL_2(Z[1/2]) as a two-representation matching with a closed zero-set group and an integer winding.
  deligne-sep7-norm-parameter-closed-subgroup: that proves the Sp_4(Z) parameter group P_op is closed and contains 1/2; this is the SL_2(Z[1/2]) twin, where the analogous group P is closed and the zero set contains pi exactly (SL_2(F_3)), but 1/2 in P is not decided.
  deligne-triple-cover-exact-mf-radical: that is the Sp_4(Z) flagship; this is the calibration twin in a world without property T, where the same question becomes a finite-dimensional unitary matching.
---

**ESTABLISHED (Theorems A to D).** The numerics further down are evidence only, and they are not part of the claim.

**Setting.**
- `G = SL_2(Z[1/2]) = SL_2(Z) *_(Gamma^0(2)) a SL_2(Z) a^-1`, with `a = diag(sqrt 2, 1/sqrt 2)` (Serre, *Trees*,
  II.1.4).
- `G~` is the preimage of `G` in the universal cover of `SL_2(R)`, and `W_m = G~ / <z^m>`, where `z` generates
  `pi_1`.
- Generators, as in `experiments/deligne-sl2-calibration-2026-09-17/lifts.py`: `x` and `y` lie over `S` and `ST`
  in `SL_2(Z)`, and `X = a~ x a~^-1`, `Y = a~ y a~^-1`.

**Presentation.** Every relator has lift exponent `0`, which `lifts.py` checks exactly. Therefore

```text
G~ = < x, y, X, Y | x^2 = y^3,  X^2 = Y^3,  x^2 = X^2,
                    (T)  x^-1 y x^-1 y = X^-1 Y,
                    (U)  x^-1 y^-1 x^2 = X Y^-1 X Y^-1 >,          z = x^4 (central),
W_m = G~ / < x^(4m) >.                                                              (P)
```

**The matching problem.** Put `PSL_2(Z) = <s, r | s^2, r^3>` and `gamma = gamma(theta) = e^(-i theta/6)`. For exact
unitary representations `(s, r)` and `(S, R)` of `PSL_2(Z)` on `C^n`, define

```text
delta(s,r,S,R; theta) = max( || S R - gamma (s r)^2 || , || s r^-1 - gamma^-1 (S R^-1)^2 || )   (operator norm)
delta_n(theta) = min over all such data on C^n,          Delta(theta) = inf_n delta_n(theta).
```

With `T = sr` and `L = sr^-1` this reads `rho_B(T) ~ gamma rho_A(T)^2` and `rho_A(L) ~ gamma^-1 rho_B(L)^2`. It is
the Iwahori square-root gluing (`sigma(u) = u^2`, `sigma(l^2) = l`), twisted by a central character and measured in
operator norm.

The relabelings `s -> -s` (which sends `gamma -> -gamma`) and `r, R -> w r, w R` with `w = e^(2 pi i/3)` (which sends
`gamma -> gamma w^-1`) preserve `delta`. So `Delta` depends only on `gamma^6 = e^(-i theta)`, and is therefore well
defined on `R / 2 pi Z`.

## Theorems

**Theorem A (MF criterion).** For every `m >= 1`, `W_m` is MF if and only if `Delta(pi/m) = 0`.

**Theorem B (zero-set group).** `Z(Delta) = {theta : Delta(theta) = 0}` is a closed subgroup of `R / 2 pi Z` that
contains `pi`. Since `Z(Delta)` contains `pi`, `P = {t in R/Z : Delta(pi t) = 0} = Z(Delta)/pi` is a well-defined closed
subgroup of `R/Z`. Note that `1/2` in `P` would mean `W_2` is MF, and that is not decided here.

Consequences:
- `{m : W_m is MF}` is the set of divisors of a single `N` in `Z_{>=1} union {infinity}`.
- `W_3` is MF iff `Delta(pi/3) = 0`, iff `Delta(2 pi/3) = 0`.
- If `W_2` and `W_3` are both MF, then so is `W_6`.
- `Delta(theta + pi) = Delta(theta)`.

**Theorem C (determinant winding bound).** Take data with `delta < 2`. Let `A = SR` and `B = gamma (sr)^2`, and let
`tau_T` be the sum of the principal phases of `A B^-1`. Then:
- `tau_T = n theta/6 + (pi/3) w_T` for some `w_T` in `Z`. Likewise `tau_U = -n theta/6 + (pi/3) w_U`.
- `delta >= 2 sin( |tau_T| / (2n) )`. Hence

  ```text
  delta_n(theta) >= 2 sin( dist(n theta/6, (pi/3) Z) / (2n) ).
  ```

- `w_T` and `w_U` are constant on connected families with `delta < 2`.

At `theta = pi/3`:
- `delta_1 = delta_2 = delta_3 = 2 sin(pi/36) = 0.174311...` exactly. For `|theta| <= pi`, `delta_1(theta) =
  2 sin(|theta|/12)`, attained by `s = S = 1`, `r = w`, `R = w^2`.
- `delta_n(pi/3) > 0` unless `6 | n`.
- The sector containing direct sums of scalar solutions (`w_T = 0`) satisfies `delta >= 2 sin(pi/36)`.

**Theorem D (exact controls).** `Delta(0) = 0`, from the trivial representation. `Delta(pi) = 0`, from a
2-dimensional solution factoring through `SL_2(F_3) = 2T` with `-I -> -1` (see `control_pi.py`, where all relator
norms are `0` and `delta = 1.8e-16`). More generally, for odd `p`, the permutation representation of `SL_2(F_p)` on
`F_p^2 \ 0` splits into an even part (an exact `theta = 0` solution) and an odd part (an exact `theta = pi` solution),
each of dimension `(p^2-1)/2`. This is `match.perm_blocks`, and the relators check exactly for `p = 3, 5, 7`.

## Proofs

**Presentation.**
- `G` is the amalgam of `SL_2(Z)` with its `a`-conjugate over `Gamma^0(2)` (Serre, *Trees*, II.1.4).
- The preimage of an amalgam in a central extension is the amalgam of the preimages over the preimage of the edge
  group. `SL_2(Z)~ = B_3 = <x, y | x^2 = y^3>`.
- The edge group `Gamma^0(2)~` is generated by `H = <x^2, T_A, U_A>`, where `T_A = x^-1 y x^-1 y` and
  `U_A = x^-1 y^-1 x^2`. The reason: `H` contains the kernel `<x^2>` of `B_3 -> PSL_2(Z)`, and its image `<T^2, L>`
  has index 3, which equals the index of `Gamma^0(2)`, by a coset check.
- In `G~`, these three generators are equal to `X^2`, `X^-1 Y` and `X Y^-1 X Y^-1`, the lifts of the same edge
  elements written in the other vertex group. For example, `T^2 = a T a^-1`. `lifts.py` checks all three identities
  in the universal cover: every lift exponent is `0`, and `x^4` has exponent `1`.
- This gives (P).

**Block reduction.** Let `x, y, X, Y` be unitaries whose defects in the relators of (P), including `x^(4m) = 1`, are
all at most `eps`. The following steps change each generator by `O_m(eps)`.
1. Spectrally round `x` to the nearest `4m`-th roots of unity and `y` to the nearest `6m`-th roots of unity.
2. `x^2` and `y^3` are now order-`2m` unitaries at distance `O(eps)`. Their spectral projections are therefore
   `O(eps)`-close, so a unitary `u` with `||u - 1|| = O(eps)` conjugates one to the other. Replace `y` by `u y u^*`,
   which makes `y^3 = x^2` exactly.
3. Do the same for `X` and `Y`. Then conjugate the pair `(X, Y)` by one unitary close to `1` so that `X^2 = x^2`
   exactly.

After this, `c = x^2` is exactly central. Decompose the space into the eigenspaces of `c`; `c` acts on one of them as
`e^(i theta)` with `theta` in `(pi/m) Z`. On that eigenspace put
- `x = alpha s` and `X = alpha S`, with `alpha = e^(i theta/2)`, and
- `y = beta r` and `Y = beta R`, with `beta = e^(i theta/3)`.

Then `s^2 = S^2 = 1` and `r^3 = R^3 = 1`. Since `x^-1 = alpha^-1 s`:
- the relator `(T)` reads `alpha^-2 beta^2 (sr)^2 = alpha^-1 beta S R`,
- the relator `(U)` reads `(alpha/beta) s r^-1 = (alpha/beta)^2 (S R^-1)^2`.

Both are exactly the two terms of `delta` with `gamma = beta/alpha = e^(-i theta/6)`. Other choices of the roots
`alpha` and `beta` change `(s, r, S, R)` by the relabelings. On the eigenspace, `z = x^4 = c^2` acts as
`e^(2 i theta)`. Conversely, block data with defect `delta` at `theta` in `(pi/m) Z` give unitaries satisfying the
vertex relations and `x^(4m) = 1` exactly, with defect `delta` in `(T)` and `(U)`.

**Proof of Theorem B.**
- *Zero.* `0` is in `Z(Delta)`: take `s = S = 1` and `r = R = 1`.
- *Negation.* Complex conjugation of the data replaces `gamma` by `gamma-bar = gamma(-theta)` and keeps `delta`.
- *Addition.* Given data at `theta_1` and `theta_2`, form the tensor product `(s (x) s', r (x) r', ...)`. It is data
  at `theta_1 + theta_2`, because `gamma(theta_1) gamma(theta_2) = gamma(theta_1 + theta_2)` and
  `(sr)^2 (x) (s'r')^2 = ((s (x) s')(r (x) r'))^2`. For unitaries,
  `||A (x) A' - g g' B (x) B'|| <= ||A - g B|| + ||A' - g' B'||`, so defects add and
  `Delta(theta_1 + theta_2) <= Delta(theta_1) + Delta(theta_2)`.
- *Closedness.* Changing `theta` moves each defect term by at most `|gamma - gamma'| = 2 sin(|theta - theta'|/12)`,
  so `Delta` is Lipschitz. It is well defined on `R / 2 pi Z` by the relabelings, so its zero set is closed.
- *pi.* `pi` is in `Z(Delta)` by Theorem D.

Consequences:
- By subadditivity, `Delta(theta + pi) <= Delta(theta)`. Applying this twice and using `2 pi`-periodicity gives
  equality.
- A closed subgroup `P` of `R/Z` is either `R/Z` or `(1/N) Z / Z`.
- By Theorem A, `W_m` is MF iff `1/m` is in `P`, which holds iff `m | N`, with `N = infinity` when `P = R/Z`.
- The statements about `W_3` and `W_6` follow, using `-pi/3 = 2 pi/3 - pi`.

**Proof of Theorem A.** MF means that `W_m` embeds in `prod_k U(n_k) / (norm -> 0)`. Since `W_m` is finitely
presented, this is the same as having unitaries `x_k, y_k, X_k, Y_k` with the following two properties:
- the relator defects of (P) go to `0`, and
- for every `g != 1`, `||phi_k(g) - 1||` does not go to `0`.

*(<=)* Suppose `Delta(pi/m) = 0`. Take block data at `theta = pi/m` with `delta_k -> 0`, and build `psi_k` from
them by the converse part of the block reduction. The vertex relations hold exactly, and `z -> e^(2 pi i/m)` as a
scalar, so `||psi_k(z^j) - 1|| = |e^(2 pi i j/m) - 1|` for every `j`.

Let `q : W_m -> G` be the quotient map, with kernel `<z>`. Let `pi_k : G -> SL_2(Z/N_k)` be reduction modulo `N_k`,
the product of the first `k` odd primes, and let `lambda_k` be the regular representation of the finite group. Put
`phi_k = psi_k (+) lambda_k pi_k q`.
- If `g = z^j` with `m` not dividing `j`, then the `psi_k` summand keeps `||phi_k(g) - 1||` bounded below.
- If `g` is not in `<z>`, then `q(g) - I` has a nonzero entry in `Z[1/2]`, so `pi_k q(g) != 1` for `k >> 0`. For any
  `h != 1`, `lambda_k(h)` is a permutation matrix with no fixed point, so `||lambda_k(h) - 1|| >= sqrt 2`.

So `phi_k` is an asymptotically faithful asymptotic homomorphism, and `W_m` is MF.

*(=>)* Take lifted generators and exactify them by the block reduction. The exactified `phi_k` is within `o(1)` of
the original on every fixed word, so it is still asymptotically faithful.
- Let `Theta_k` be the set of `c`-eigenvalue angles that occur. It is a subset of the finite set
  `(pi/m) Z / 2 pi Z`.
- Let `Theta*` be the set of angles that occur for infinitely many `k`. Each of them has block defect at most
  `delta_k -> 0` along those `k`, so `Theta*` is contained in `Z(Delta)`. For `k >> 0`, `Theta_k` is contained in
  `Theta*`.
- Let `H` be the subgroup generated by `Theta*` and `pi`. By Theorem B, `H` is contained in `Z(Delta)`.
- Suppose `2H != (2 pi/m) Z / 2 pi Z`. Then `2H` lies in a proper subgroup `(2 pi d/m) Z / 2 pi Z` with `d | m` and
  `d > 1`. Put `j = m/d`. Then `z^j` acts as `e^(2 i j theta) = 1` on every block for `k >> 0`, so
  `||phi_k(z^j) - 1|| -> 0`, which contradicts faithfulness.
- So some `theta'` in `H` has `2 theta' = 2 pi/m`. Hence `theta'` is `pi/m` or `pi/m + pi`, and since `pi` is in
  `H`, `pi/m` is in `H`, which is contained in `Z(Delta)`.

**Proof of Theorem C.**
- `det S` is in `{±1}`, `det R` and `det r` are in `mu_3`, and `det((sr)^2) = (det s det r)^2`. Therefore
  `det(A B^-1) = gamma^-n mu_6 = e^(i n theta/6) mu_6`.
- `tau_T` is a sum of principal arguments, so `e^(i tau_T) = det`. That gives
  `tau_T in n theta/6 + (pi/3) Z`, with the `2 pi` ambiguity absorbed.
- If `phi_j` are the principal phases of `A B^-1`, then `||A - B|| = ||A B^-1 - 1|| = 2 sin(max |phi_j| / 2)`, and
  `max |phi_j| >= |tau_T| / n`.
- While `delta < 2`, no eigenvalue of `A B^-1` equals `-1`. So `tau_T` varies continuously, and since it lies in a
  discrete set it is locally constant.
- The same argument applies to `U`, using `det(s r^-1 (gamma^-1 (S R^-1)^2)^-1) = gamma^n mu_6`.
- At `theta = pi/3`, `dist(n pi/18, (pi/3) Z)` equals `pi/18`, `pi/9` and `pi/6` for `n = 1, 2, 3`, and in each case
  the bound is `2 sin(pi/36)`. The same distance is `0` iff `6 | n`.
- The scalar datum `s = S = 1`, `r = w`, `R = w^2` has `SR = (sr)^2 = w^2` and `s r^-1 = (S R^-1)^2 = w^2`, so its
  `delta` is `|1 - gamma| = 2 sin(|theta|/12)`. Direct sums attain the upper bound in every dimension.
- Each scalar block has `A B^-1 = gamma^-1`, of phase `theta/6`. So direct sums of scalars have `w_T = 0`, and the
  whole `w_T = 0` sector has `delta >= 2 sin(|tau_T|/(2n)) = 2 sin(|theta|/12)`.

**Proof of Theorem D.**
- `control_pi.py` builds the homomorphism `SL_2(F_3) -> 2T` inside `SU(2)` on the mod-3 images of `x, y, X, Y`, with
  `-I -> -1`. This is exact, since it is a finite-group representation.
- Pulled back along `SL_2(Z[1/2]) -> SL_2(F_3)`, and with `c = x^2 = -1`, it gives an exact datum at `theta = pi`.
- Permutation representations work the same way: `c = -I` acts as the antipode `v -> -v`, and the `±1` parts give
  `theta = 0` and `theta = pi`.

## Numerical evidence (not claimed)

Everything is at `theta = pi/3`, the `W_3` block, and every row is in `results.log`. The optimisers are
`match.solve_exact` (random determinant patterns) and `match.solve_seeded` (conjugation orbits of exact seeds).
Spectra are exact throughout. The reported `delta` is the float64 operator norm of exact data, with relator error
`< 2e-14`.

**Random exact-pattern starts.**

| n | lower bound from Theorem C | best delta found |
|---|---|---|
| 3 | 0.17431 | 0.17431 |
| 4 | 0.08724 | 0.74688 |
| 5 | 0.03490 | 0.81176 |
| 6 | 0 | 0.84600 |

These starts land in poor local minima.

**Seeded winding sectors.** Every seed below starts at `delta = 0.34730`.

| seed | n | `w_T` | Theorem C bound | best delta |
|---|---|---|---|---|
| F3 S S S S | 6 | -1 | 0 | 0.34730 (stuck) |
| O3 E3 S S S S | 12 | -2 | 0 | 0.22135 |
| O3 E3 E3 | 12 | -2 | 0 | **0.13265** |
| O5 E5 E5 | 36 | -6 | 0 | 0.17164 |

The `n = 36` optimisation is harder, and at `n = 36` the optimiser reports a number, not an optimum.

Two further runs:
- Restarting from `witness (+) witness` (`n = 24`) gives `0.1442` with noise `0.1` and `0.1744` with noise
  `0.3`. Both are worse than the direct sum. So this optimiser does not yet exploit extra dimension.
- At `theta = pi/2` (the `W_2` block), the scalar value is `2 sin(pi/24) = 0.26105`. The seed "O3 E3" (`n = 8`,
  ratio 1 : 1, bound 0) reaches `0.24197`, so the scalar profile fails there as well.

**The seed "O3 E3 E3" beats the scalar profile.** This seed has `n = 12`: the `theta = pi` part of the `SL_2(F_3)`
permutation representation, plus two copies of the `theta = 0` part. Its winding is `w_T = -2`, and its Theorem C
bound is `0`. Starting from this seed, the optimiser reaches

```text
delta = 0.132648 < 2 sin(pi/36) = 0.174311
```

This is certified by `verify_below_profile.py`, with the witness saved in `witness_O3E3E3.npz`. Hence:

- **Delta(pi/3) <= 0.13265.** The scalar profile `Delta(theta) = 2 sin(dist(theta, pi Z)/12)` is false.
- Seed accounting explains why. At `theta = pi/3`, each `theta = pi` dimension carries phase `-pi/9` in `tau_T`, and
  each `theta = 0` dimension carries `+pi/18`. The determinant obstruction therefore cancels exactly when the
  dimensions are in the ratio 1 : 2. That puts the winding ratio at `w_T/n = -1/6 = -theta/(2 pi)`, which is exactly
  the ratio that Theorem C forces on any sequence with `delta -> 0`.

## Calibration for the Sp_4 flagship

1. **Twin of the sublinear-windings route.**
   - By Theorem C, any sequence with `delta -> 0` at `theta` has winding ratio `w_T/n -> -theta/(2 pi)`.
   - The exact solutions (`theta = 0` and `theta = pi`) have ratio `0` and `-1/2`.
   - So the SL_2 twin of `deligne-triple-cover-via-sublinear-windings` is the statement: "asymptotic matchings have
     winding ratio asymptotically in `(1/2) Z / Z`", which implies that `W_3` is not MF.
   - The O3 E3 E3 witness shows that this twin can only hold in the limit. Mixing exact `theta = 0` and
     `theta = pi` data in the ratio 2 : 1 already realises ratio `-1/6` exactly, at finite `n`, with `delta = 0.13`.
     This is well below every mixed-sector value the scalar picture predicted.
   - In the SL_2 world, the winding invariant is therefore **not** obstructed by any finite-`n` rigidity. A proof of
     "winding ratio in `(1/2) Z`" would have to be a genuine `n -> infinity` statement.
2. **What is and is not a property T effect.** `SL_2(Z[1/2])` does not have property T, yet the full MF question for
   its covers becomes an explicit finite-dimensional unitary problem, `Delta(pi/3) = 0`. Any argument for the
   flagship that does not use a feature of `Sp_4(Z)` absent from `SL_2(Z[1/2])` also applies here, so it must
   decide `Delta(pi/3)`. Two cases:
   - If `Delta(pi/3) = 0`, then `W_3` is MF, and every such amalgam-agnostic argument for the flagship dies at this
     calibration.
   - If `Delta(pi/3) > 0`, the calibration is consistent with the flagship.
3. **Rational K-theory remark (not proved).** For `G`, `cd_Q = 2` and `H^1(G; Q) = 0`. Rationally the Chern
   character of a matching is its rank plus `c_1`, and `c_1` is exactly the determinant winding of Theorem C. So
   Theorem C plausibly captures the entire rational topological obstruction. If so, a proof that `Delta(pi/3) > 0`
   needs a non-rational (torsion or analytic) invariant.

## Open

- Is `Delta(pi/3) = 0`? Equivalently, is `W_3` MF?
- Does `delta` keep decreasing along the ratio-`1:2` seeds `O_p E_p E_p` as `p` grows?
- Is `Delta(pi/2) = 0` (that is, is `W_2` MF)?
