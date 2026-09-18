---
rg: 2
id: deligne-multiplier-bernoulli-profinite-survival-proof
kind: route
title: Profinite case by Kazhdan untwisting plus Deligne invisibility, Bernoulli factor removed by Popa product superrigidity for E_3
target: deligne-multiplier-survives-on-bernoulli-times-profinite-actions
requires:
  - kazhdan-profinite-untwisting-is-virtual-splitting
  - deligne-triple-cover-fd-central-invisibility
  - popa-bernoulli-product-cocycles-come-from-cofactor
  - bdhv-central-extension-property-t
---

**Imports.** `Sp_4(Z)` has property (T): Kazhdan 1967 for lattices in higher-rank simple Lie groups, as in
Bekka--de la Harpe--Valette, Chapter 1. This is a statement-level standard fact.

**Step 0. Reduction to `alpha`.**
- `alpha` takes values in `mu_3`, so `alpha^3 = 1`.
- If `c` solves (U) for `alpha^2`, then `c^2` solves it for `alpha^4 = alpha`.
- The same holds for restrictions to subgroups.
- So it suffices to treat `beta = alpha`.

**Step 1. No finite-index splitting.**
- Suppose `alpha|Lambda = delta f` for some finite-index `Lambda`.
- The converse construction (item 2 of `kazhdan-profinite-untwisting-is-virtual-splitting`) then gives
  unitaries `W(g)` on `l^2(Gamma/Lambda)` with `W(g)W(h) = alpha(g,h)W(gh)`.
- With the product `(zeta,g)(zeta',h) = (zeta zeta' alpha(g,h), gh)`, the map `(zeta,g) -> zeta W(g)` is a
  finite-dimensional unitary representation of `E_3`. The central `z = (zeta,1)` with `zeta != 1` acts by
  `zeta != 1`.
- This contradicts (DTC2) of `deligne-triple-cover-fd-central-invisibility`. Hence no restriction of
  `alpha` to a finite-index subgroup is a coboundary.
- Convention check: `alpha` is a cocycle classifying the extension (DTC1). A cohomologous choice
  `alpha delta b` changes `c` to `c b` and `W(g)` to `b(g) W(g)`. The other generator, `alpha^2`, is handled
  by Step 0.

**Step 2. The case `Z = X` profinite, or a point.**
- `Gamma` has (T). Item 3 of `kazhdan-profinite-untwisting-is-virtual-splitting` gives a finite-index
  `Lambda = pi^{-1}(U)` with `alpha|Lambda` a coboundary, which contradicts Step 1.
- A point is the case `K = 1`.

**Step 3. `E_3` has (T).**
- `mu_3` is central, and `E_3/mu_3 = Gamma` has (T).
- `E_3` has finite abelianization: `E_3^ab` modulo the image of `mu_3` is `Gamma^ab`, which is finite because
  Kazhdan groups have finite abelianization.
- So `bdhv-central-extension-property-t` applies.

**Step 4. The case `Z = B x X`.**
- *Base.* The base-`[0,1]` shift `B_1 = [0,1]^Gamma` factors onto `B = Y_0^Gamma` coordinatewise, because
  every standard probability space is a measurable image of `([0,1], Leb)`. Pulling back a solution of (U)
  along `B_1 x X -> B x X` gives a solution on `B_1 x X`. So assume `B = B_1`.
- *The cocycle.* Let `E_3` act on `B x X` through `E_3 -> Gamma`. Given `c` solving (U) for `alpha`, put
  `w((zeta,g), p) = zeta c(g,p)`.
  - Expanding `(zeta,g)(zeta',h) = (zeta zeta' alpha(g,h), gh)` and using (U) gives
    `w(ab, p) = w(a, bp) w(b, p)`. So `w` is a `T`-valued 1-cocycle of `E_3 ~> B x X`.
  - Since `c(1,.) = 1`, we have `w((zeta,1), p) = zeta`.
- *Popa's hypotheses.* Use Theorem 0.1 as quoted verbatim in `popa-bernoulli-product-cocycles-come-from-cofactor-citation`,
  with `Gamma := E_3`, `H := E_3`, `sigma` the `E_3`-action on `B`, `rho` the action on `X`, and
  `𝒱 := T`.
  - As an `E_3`-action, `B = [0,1]^I` is the generalized Bernoulli action over the `E_3`-set
    `I = E_3/mu_3`. The quote's parenthetical makes it s-malleable.
  - `H = E_3` is infinite and has (T) by Step 3, so it is rigid in itself. It is normal, hence w-normal.
  - The `E_3`-set `I` has finite stabilizers, conjugates of `mu_3`. So for finite `F, F'` in `I`, only
    finitely many `a` have `aF ∩ F' != ∅`. Cylinder functions on disjoint coordinate sets are independent, so
    `sigma|H` is mixing, in particular weakly mixing.
  - `T` is separable compact, hence of finite type by the quoted sentence.
- *Popa's conclusion.* `w(a, (b,x)) = phi(a(b,x)) w'(a, x) conj(phi(b,x))` for a measurable `phi` and a cocycle
  `w'` of `E_3 ~> X`. At `a = (zeta,1)`, which acts trivially, this gives `w'((zeta,1), x) = zeta`.
- *Back to `Gamma`.* Put `c'(g,x) = w'((1,g), x)`. Since `(1,g)(1,h) = (alpha(g,h),1)(1,gh)`, the cocycle identity
  for `w'` gives `c'(g,hx) c'(h,x) = alpha(g,h) c'(gh,x)`. So `c'` solves (U) on `X`, contradicting Step 2.

**Trust surface.**
- Popa's generalized Bernoulli form is used through the parenthetical of the verbatim quote. The definitions in
  Section 4.3 of Popa's paper were not reread here, as already recorded on the citation route.
- The graph node `popa-bernoulli-product-cocycles-come-from-cofactor` states only the plain-Bernoulli case. The
  generalized case is read directly from the quote.
- The plain Bernoulli shift of `E_3` would not suffice. Removing the `mu_3`-invariant part leaves an eigenfunction
  equation `phi(zeta b) = zeta phi(b)` that Popa does not exclude. That shift's quotient by `mu_3` is survivor 1
  of the claim.
