# The two-root defect gap, and why the nested descent cannot close the gate

Lane `w4-gate-descent`, 2026-09-12, family R4. Supports
`leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`,
`nested-two-root-defect-pieces-decay-geometrically-both-ways`,
`near-minimal-defect-models-have-multiplicative-cylinder-defects`,
`leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, and an Attempts entry on
`rank-models-of-el3-satisfy-the-two-root-identities`. It continues Remark 1.4 and Section 3 of
`research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md`.

## 0. Summary

* **Section 2 (established): a defect gap.** There is a constant `c_0 > 0` such that every
  characteristic-two rank model `sigma` of `R^x` satisfies

  ```text
  c_0 · rk(1-f)  <=  rk((1-f) D_A)  <=  rk(1-f) / 2 ,
  ```

  where `fM = Fix_r(sigma(R^x))` and `D_A` is the two-root product of any proper cylinder pair.
  So on the fixed-point-free quotient model the normalized defect lies in `[c_0, 1/2]`. The lower
  bound comes from compactness, corner locality, perfection and four-generation. Property (T),
  globality and the compressor collision are not used. `c_0` is not explicit.
* **Section 3 (established): the descent is geometric in both directions.** On a fixed-point-free
  model, the ranks `f(k) = rk(D_(A_1) ... D_(A_k))` for pairwise disjoint cylinders satisfy
  `c_* f(k) <= f(k+1) <= f(k)/2`, where `c_* >= c_0` is the infimum of the normalized defect over
  nontrivial fixed-point-free models. This proves the uniform descent bound Remark 1.4 asked for,
  with `c = c_*`. It also kills the payoff attached to it: the nested pieces at least halve at every
  step, so they contain no principal right ideal of positive rank, and there is no limit corner.
* **Section 4 (established): near-minimal models look like tensor products.** If
  `delta = rk(D_A) <= (1+eps) c_*` on a fixed-point-free model, then `|f(k) - delta^k| <= 2 eps delta`
  for every `k`. The range and kernel corner models of a disjoint defect are both exactly borderline,
  so neither restriction lowers the defect.
* **Section 5 (open): where it stops.** Closing the gate along this line needs an operation on
  fixed-point-free models that lowers the normalized defect by a fixed factor. One sufficient input
  is strict submultiplicativity `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1`. Honest
  tensor configurations attain `theta = 1`, so any proof must use the Leavitt relations.
* **Calibration.** In the Toeplitz group `H = EL_3(A_X)` the honest model `EL_3(phi)` is
  fixed-point-free with defect `0`. So the analogue of Section 2 fails there, at corner locality,
  as it must.

## 1. Setting and standard facts

Notation follows the defect-piece artifact.
* `R = L_(F_2)(1,2)`, with `R^x = EL_3(R)` through the code `(0, 10, 11)`.
* `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`.
* `sigma : R^x -> M^x` is a homomorphism into the units of a rank ultraproduct `M` over a field of
  characteristic two. `M` is von Neumann regular with a faithful rank function `rk`, normalized by
  `rk(1) = 1`, and a nonzero corner `eMe` is again a rank ultraproduct after renormalizing.
* For a proper cylinder `A` (a nonempty prefix):
  * `N^A_ab = sigma(iota_A(x_ab(1))) - 1`;
  * `D_A = N^A_23 N^A_12`.
* `fM = Fix_r(sigma(R^x))`, with `sigma(g) f = f` for every `g`.
* `sigma` is *fixed-point-free* when `f = 0`.

**Fact 1.1 (rank calculus).** Let `M` be a regular ring with a faithful rank function.
* (a) If `x = x z x`, then the right annihilator of `x` is `(1 - zx)M`, and its rank is `1 - rk(x)`.
* (b) Principal right ideals form a modular lattice on which `rk` is a dimension function:
  `rk(I cap J) + rk(I + J) = rk(I) + rk(J)`. Hence
  `rk(I_1 cap ... cap I_m) >= rk(I_1) + ... + rk(I_m) - (m - 1)`.
* (c) If `q` is idempotent, `T q = q T q`, and `(qTq)^2 = 0`, then `rk(Tq) <= rk(q)/2`.
* (d) Suppose `x` is an element with right annihilator `K`. For every principal right ideal `J`
  containing `K`, `rk(xJ) = rk(J) - rk(K)`.

*Proof.* (a) and (b) are standard: principal right ideals are direct summands, and the rank is the
dimension function on finitely generated projectives (Goodearl, *Von Neumann Regular Rings*,
Chapter 16). (c) In `qMq`, renormalized, `qTq` is square-zero, so its image lies in its kernel, and
rank-nullity gives `2 rk(qTq) <= rk(q)`. (d) `0 -> K -> J -> xJ -> 0` is exact, and ranks add over
exact sequences of summands. QED

**Fact 1.2 (commuting and transitivity).**
* For disjoint proper cylinders `A` and `B`, `iota_A(R^x)` and `iota_B(R^x)` commute, because
  `S[A] a T[A] · S[B] b T[B] = 0`. So the `N^A`, `N^B`, `D_A`, `D_B` commute.
* Thompson's `V` sits in `R^x` as prefix-replacement units. Take two `k`-tuples `(A_i)` and `(B_i)`
  of pairwise disjoint cylinders, each with proper union. Split both complements into the same
  number of cylinders `C_j` and `C'_j`. Then `u = sum_i S[B_i]T[A_i] + sum_j S[C'_j]T[C_j]` lies in
  `V`, and `u iota_(A_i)(g) u^-1 = iota_(B_i)(g)` for all `g` and `i`.
* Hence the rank of any product of `D_(A_1), ..., D_(A_k)` depends only on `k`, for configurations
  with proper union. For `k = 1` this is one number `delta(sigma) = rk(D_A)`.

**Fact 1.3 (square zero).** In characteristic two `iota_A(x_ab(1))` is an involution, so
`(N^A_ab)^2 = 0`.

## 2. The defect gap

**Lemma 2.1 (the fixed-point-free quotient).** Suppose `f != 1`. Then:
* `sigma_W(g) = (1-f) sigma(g) (1-f)` is a homomorphism `R^x -> ((1-f)M(1-f))^x`;
* `sigma_W` is fixed-point-free, and nontrivial exactly when `sigma` is;
* its defect at a proper cylinder `A` is `(1-f) D_A`.

*Proof.*
* **Homomorphism.** `(1-f) sigma(g) f = 0`, so `sigma_W` is multiplicative, as in Theorem 1.2 of
  the defect-piece artifact.
* **No fixed vectors.** Let `x` in `(1-f)M` satisfy `sigma_W(g) x = x` for every `g`. Put
  `c(g) = sigma(g) x - x = f sigma(g) x`, which lies in `fM`. Since `sigma(g)` fixes `fM`
  pointwise, `c(gh) = c(g) + sigma(g) c(h) = c(g) + c(h)`. So `c` is a homomorphism into the
  additive group `fM`, which is abelian, and `c = 0` because `R^x` is perfect
  (`leavitt-gl-equals-el-and-perfect-unit-group`). Then `x` lies in `fM cap (1-f)M = 0`.
* **Nontrivial.** If `sigma_W` is trivial, then `sigma(g) - 1` lies in `fM(1-f)`, where
  `(1+a)(1+b) = 1+a+b`. So `sigma` lands in an abelian group, and perfection makes it trivial.
* **Defect.** `N^A_ab f = 0`, so `(1-f) N^A_ab (1-f) = (1-f) N^A_ab`, and
  `(1-f)N^A_23 (1-f) N^A_12 = (1-f) D_A`. QED

**Lemma 2.2 (displacement).** Let `g_1, ..., g_4` generate `R^x`
(`binary-leavitt-unit-group-four-generated`). If `sigma` is fixed-point-free, then
`sum_i rk(sigma(g_i) - 1) >= 1`, so `max_i rk(sigma(g_i) - 1) >= 1/4`.

*Proof.* A vector fixed by the generators is fixed by the group, so `Fix_r(sigma(R^x))` is the
intersection of the right annihilators of `sigma(g_i) - 1`. By Fact 1.1(a) and (b) its rank is at
least `1 - sum_i rk(sigma(g_i) - 1)`, and it is `0`. QED

**Lemma 2.3 (compactness).** For every `eta > 0` there is `c(eta) > 0` such that every
characteristic-two rank model with `max_i rk(sigma(g_i) - 1) >= eta` has `rk(D_1000) >= c(eta)`.

*Proof.* Suppose models `sigma_n : R^x -> M_n^x` have `max_i rk(sigma_n(g_i) - 1) >= eta` and
`rk(D_1000^(n)) < 1/n`. Passing to a subsequence, one index `i` attains the maximum for all `n`.
* **Finite stages.** Enumerate `R^x = {h_1, h_2, ...}`, with `g_i`, `x' = iota_1000(x_12(1))` and
  `y' = iota_1000(x_23(1))` among the first terms. Relations and ranks in `M_n` are ultralimits of
  finite-stage values. So for each `n` there are invertible matrices `X_n(h_j)`, `j <= n`, of size
  `k_n`, over a field of characteristic two, such that:
  * every relation `h_a h_b = h_c` with `a, b, c <= n` holds up to normalized rank `1/n`;
  * the normalized ranks of `X_n(g_i) - 1` and of `(X_n(y') - 1)(X_n(x') - 1)` are within `1/n`
    of their values in `M_n`.

  A matrix of normalized rank at least `1 - eps` differs from an invertible matrix by normalized
  rank at most `eps`, so invertibility costs nothing.
* **One field.** Finitely many entries generate a finitely generated field of characteristic two.
  It embeds into `Omega`, the algebraic closure of `F_2(t_1, t_2, ...)`, and rank does not change.
* **The limit model.** Along a nonprincipal ultrafilter, `sigma'(h) = [(X_n(h))]` is a
  homomorphism from `R^x` into the units of a rank ultraproduct over `Omega`.
  * Its corner product on `[1000]` has rank `0`.
  * So it is trivial by `two-root-identity-is-corner-local-for-leavitt-rank-models`, (3) implies (1).
  * But `rk(sigma'(g_i) - 1) >= eta`, a contradiction. QED

**Theorem 2.4 (defect gap).** Put `c_0 = c(1/4)`. For every characteristic-two rank model `sigma`
of `R^x` and every proper cylinder `A`:

```text
c_0 · rk(1-f)  <=  rk((1-f) D_A)  <=  min( rk(D_A), rk(1-f)/2 ) ,        rk(D_A) <= rk(1-f) .
```

In particular:
* a nontrivial fixed-point-free model has normalized defect in `[c_0, 1/2]`;
* so `c_0 <= 1/2` whenever a nontrivial model exists.

*Proof.* If `f = 1` everything vanishes, so suppose not.
* **Lower bound.** `sigma_W` is nontrivial and fixed-point-free (Lemma 2.1). In the renormalized
  corner its displacement is at least `1/4` (Lemma 2.2), so its defect at `[1000]` has normalized
  rank at least `c_0` (Lemma 2.3). By Fact 1.2 the same holds at every proper cylinder. Un-normalizing
  gives `rk((1-f)D_A) >= c_0 rk(1-f)`.
* **Upper bounds.**
  * `(1-f) N^A_12` is square-zero in `(1-f)M(1-f)` (Fact 1.3 and `N^A_12 f = 0`), so
    `rk((1-f) D_A) <= rk((1-f) N^A_12) <= rk(1-f)/2`.
  * `D_A = D_A (1-f)`, so `rk(D_A) <= rk(1-f)`. QED

**Remark 2.5 (what is used).**
* **Used:**
  * corner locality, which is where "R has no rank model" enters;
  * perfection;
  * four-generation;
  * the corner-ring fact.
* **Not used:** property (T) of `Gamma`, globality, and the compressor collision `q sigma(u) q != 0`.
* **Why the constant is inexplicit:** it comes from compactness. A quantitative corner locality
  would make it explicit.

**Remark 2.6 (calibration: the Toeplitz group).** Take `H = EL_3(A_X)` from Section 2 of the
defect-piece artifact, and the honest model `EL_3(phi)`.
* **Fixed-point-free:** a fixed vector `v` has `E_ab phi(1) v = 0` for all `a != b`, so `v = 0`.
* **Defect:** it is `E_23 E_12 = 0`.

So the analogue of Theorem 2.4 fails for `H`, and it fails at Lemma 2.3, because corner locality
fails when the coefficient ring has a rank model. The upper bound `1/2` holds there too.
