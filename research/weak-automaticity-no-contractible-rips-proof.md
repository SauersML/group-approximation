---
rg: 2
id: weak-automaticity-no-contractible-rips-proof
kind: route
title: F is autostackable, F_infinity and quadratic yet infinite-dimensional; T is asynchronously combable yet contains F and all Z/2^k
target: weak-automaticity-does-not-give-contractible-rips-complexes
requires:
  - thompson-f-is-autostackable
  - thompson-f-is-of-type-f-infinity
  - thompson-f-has-quadratic-dehn-function
  - thompson-f-has-no-contractible-rips-complex
  - thompson-f-has-infinite-cohomological-dimension
  - thompson-t-is-asynchronously-combable
  - contractible-rips-conjugates-p-subgroups-into-balls
---

**Step 1 (F).** `F` is autostackable (`thompson-f-is-autostackable`), of type `F_∞`
(`thompson-f-is-of-type-f-infinity`) and has quadratic Dehn function
(`thompson-f-has-quadratic-dehn-function`). No Rips complex of `F` is contractible
(`thompson-f-has-no-contractible-rips-complex`). This proves item 1.

**Step 2 (F inside T).** `T` is the group of piecewise-linear homeomorphisms of the
circle `R/Z` with finitely many breakpoints, all at dyadic rationals, slopes powers
of 2, and mapping the dyadic rationals to themselves. (Cannon–Floyd–Parry,
*Introductory notes on Richard Thompson's groups*, Enseign. Math. 42 (1996); from
memory.)

An element `f ∈ F` is a PL homeomorphism of `[0,1]` fixing `0` and `1`. It descends
to a homeomorphism `f̄` of `R/Z = [0,1]/(0 ~ 1)` with the same breakpoints and
slopes. `f̄` maps dyadic rationals to dyadic rationals because `f` is affine with
dyadic data on each piece. `f ↦ f̄` is a homomorphism, and it is injective because
`f̄` determines `f` on `(0,1)`. So `F <= T`.

**Step 3 (2-torsion in T).** For `k >= 0` let `ρ_k(x) = x + 2^-k mod 1`. It has no
breakpoints, has slope `1 = 2^0`, and maps dyadic rationals to dyadic rationals. So
`ρ_k ∈ T`, and `ρ_k` has order exactly `2^k`, so `⟨ρ_k⟩ ≅ Z/2^k`.

**Step 4 (T has no contractible Rips complex, twice over).** Suppose `R_d(T,S)` were
contractible, and put `N = |B_S(d)|`. By
`contractible-rips-conjugates-p-subgroups-into-balls`:

- (dimension) the torsion-free subgroup `F` (Step 2) would have `cd F <= N - 1`,
  contradicting `thompson-f-has-infinite-cohomological-dimension`;
- (Smith) the 2-subgroup `⟨ρ_k⟩` with `2^k > N` (Step 3) would satisfy
  `2^k = |⟨ρ_k⟩| <= N`, a contradiction.

Either contradiction alone suffices.

**Step 5.** `T` is asynchronously combable (`thompson-t-is-asynchronously-combable`).
This proves item 2.

The obstruction paragraph of the claim is the contrapositive: an implication from
any listed property to contractible Rips complexes would apply to `F` or `T`.
