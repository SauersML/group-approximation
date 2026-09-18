---
rg: 2
id: jz-question-5-for-thompson-t-implies-f-nonamenable-proof
kind: route
title: Split every element of T as an element of F times the dyadic rotation that returns 0, so F acts simply transitively on the cosets of the rotations, then apply the amenable-coupling Liouville criterion
target: jz-question-5-for-thompson-t-implies-f-nonamenable
requires: [amenably-coupled-actions-admit-symmetric-liouville-measures, juschenko-zheng-liouville-actions, thompson-t-is-not-amenable, thompson-t-has-quadratic-dehn-function]
---

Notation is as in the claim. `T` is the group of Cannon–Floyd–Parry, as in `thompson-t-is-not-amenable`:
orientation-preserving PL homeomorphisms of `R/Z` with finitely many dyadic breakpoints, slopes powers of 2,
mapping `D/Z` onto itself. `F` is the subgroup fixing `0`; cutting the circle at `0`, its elements are exactly
the PL homeomorphisms of `[0,1]` with dyadic breakpoints and slopes powers of 2, i.e. Thompson's `F`.

**Step 1 (T = F·R_D, exactly).**
- `R_D ⊆ T`: `ρ_θ` for dyadic `θ` has no breakpoints, slope `1 = 2^0`, and maps `D/Z` onto itself.
- Let `g ∈ T` and `c = g⁻¹(0)`. Then `c ∈ D/Z`, since `g⁻¹ ∈ T` preserves `D/Z`. Put `f = g ρ_c`. Then
  `f(0) = g(c) = 0`, so `f ∈ F`, and `g = f ρ_{−c}`. Hence `T = F·R_D`.
- `F ∩ R_D = 1`: if `ρ_θ(0) = 0` then `θ = 0`. So the factorization `g = fρ` is unique.

**Step 2 (the T-set X = T/R_D).**
- `T` acts transitively on `X` by left multiplication. The stabilizer of `gR_D` is `gR_Dg⁻¹ ≅ Z[1/2]/Z`, which
  is abelian, and locally finite since every finitely generated subgroup of `Z[1/2]/Z` is finite cyclic.
- The map `F → X`, `f ↦ fR_D`, is onto, since `gR_D = fρR_D = fR_D` by Step 1. It is one-to-one, since
  `fR_D = f'R_D` gives `f⁻¹f' ∈ F ∩ R_D = 1`. It is `F`-equivariant for left multiplication. So `F` acts simply
  transitively on `X`, and `X` is the regular `F`-set.

**Step 3 (if F is amenable, the action is LAT and Liouville).** Suppose `F` is amenable. Every finite subset of
`X` lies in the single orbit `F·R_D = X` of the amenable subgroup `F`, so `T ↷ X` is locally amenably
transitive. `T` is countable. Theorem A of `amenably-coupled-actions-admit-symmetric-liouville-measures`
gives, for any generating sequence of `T` (for instance a finite generating set, or an enumeration of `T`),
a symmetric probability `µ` with that sequence in its support and `(X, P_µ)` Liouville. In particular `µ` is
non-degenerate, and the action is `µ`-Liouville in the sense of `juschenko-zheng-liouville-actions` (every
bounded `P_µ`-harmonic function on `X` is constant), as in Step 2 of
`juschenko-zheng-question-5-fails-for-countable-groups-proof`.

**Step 4 (T is finitely presented and nonamenable).** `T` is not amenable (`thompson-t-is-not-amenable`). `T`
is finitely presented: `thompson-t-has-quadratic-dehn-function` imports a Dehn function for `T`, which is
defined only with respect to a finite presentation (and finite presentability of `T` is Cannon–Floyd–Parry's).
So `T` meets Juschenko–Zheng's standing assumption of a finite generating set.
- The action `T ↷ X` is not even amenable. A `T`-invariant mean on `X` would lift to a left invariant mean on
  `T` by averaging over cosets with an invariant mean on the abelian group `R_D`, exactly as in Step 3 of
  `juschenko-zheng-question-5-fails-for-countable-groups-proof`.

**Step 5 (conclusion).** Under the assumption of Step 3, `T ↷ X` is transitive, `µ`-Liouville for a
symmetric non-degenerate `µ`, with abelian (locally finite) stabilizers, and `T` is finitely presented and
nonamenable. This is a negative answer to Question 5 (quoted verbatim in `juschenko-zheng-liouville-actions`)
for a finitely presented group, giving item 3 of the claim. Item 4 is its contrapositive: if every such
action of `T` forces `T` to be amenable, the assumption "`F` is amenable" is false. ∎

**Remark (why this is not the SL_2 argument renamed).** The mechanism is the same (an exact factorization
`G = HK` with `H` amenable and `K` abelian, from `juschenko-zheng-question-5-fails-for-countable-groups`),
but in `T = F·R_D` the factor `H = F` is not known to be amenable. Its amenability is exactly the root, so
the conclusion is an implication between the root and Question 5, not an unconditional answer. The
factorization is used only through the transitive `F`-action; any amenable `H ≤ T` meeting every coset of
`R_D` in a way that puts each finite subset of `X` into one `H`-orbit would do, which is the open node
`thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive`.
