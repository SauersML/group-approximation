---
rg: 2
id: bernoulli-infinite-power-iff-approximate-half-absorption
kind: claim
title: An action is isomorphic to its countable power exactly when it splits into two copies of itself with any finite information approximately inside the first, and for Bernoulli shifts this is total collapse
distinct_from:
  bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square: that proves a failure of classification is a self-square X_h ≅ X_h × X_h; this proves which extra condition on the self-squares turns such a failure into total collapse X_h ≅ X_∞.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that shows collapse onto X_∞ is total and forces zero Rokhlin supremum (item 5); this characterizes when a Bernoulli shift reaches X_∞, through approximately positioned exact splittings.
---

**ESTABLISHED (unreviewed)** by [[bernoulli-infinite-power-iff-approximate-half-absorption-proof]].

Let `Γ` be a countable group and `Γ ↷ (X, μ)` a p.m.p. action on a standard probability space. A
**half-splitting** of `X` is a pair `(A, C)` of `Γ`-invariant sub-σ-algebras that are independent, generate
the Borel σ-algebra mod null sets, and give factor actions `(X, A) ≅ X ≅ (X, C)`. For a finite partition `R`,
write `R ⊂_ε A` when every atom of `R` lies within `μ`-distance `ε` of a set in `A`.

**Theorem.** The following are equivalent:
1. `X ≅ X^N`, the countable power with the diagonal action;
2. for every finite partition `R` and every `ε > 0` there is a half-splitting `(A, C)` with `R ⊂_ε A`;
3. `X` has a half-splitting `(A, C)`, and for every finite `R` and `ε > 0` some automorphism `T` of the action
   satisfies `T(R) ⊂_ε A`.

In 3 the half-splitting can be fixed once and for all. Item 2 contains `X ≅ X × X`.

**Corollary (Bernoulli shifts).** Let `G` be countably infinite and `0 < h < ∞`. Then `X_h^N` is a Bernoulli
shift with base of infinite entropy, so `X_h^N ≅ X_∞`. Hence item 2 for `X_h` is equivalent to `X_h ≅ X_∞`. By
item 5 of `bernoulli-isomorphism-collapse-set-is-a-subgroup` it then gives `D(G) = R`, `X_(h') ≅ X_∞` for every
`h' ≥ h`, and `h^Rok_sup(G) = 0`.

**Reading.**
- A failure of classification is a self-square (`bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square`).
  The gap between a self-square and total collapse is exactly the *position* requirement in item 2: the
  splittings are exact, and only their position relative to a given finite partition is approximate.
- This locates where the "iterated absorption" attempt on `zero-rokhlin-supremum-forces-bernoulli-collapse`
  dies. Iterating one fixed isomorphism `X ≅ X × X` can lose information in the limit, as in the sign example
  there. Choosing each splitting after the partition to be captured is known repairs that.
- Item 3 is an approximate transitivity statement. `A ≅ X`, so the whole process of `R` has an exact copy
  inside `A`: process laws and every invariant of the process are no obstruction. What is asked is that an
  automorphism move `R` close to one such copy.
- The condition parallels the strongly self-absorbing C*-algebras of Toms and Winter, where an isomorphism
  `D → D ⊗ D` approximately equal to `id ⊗ 1` yields `D ≅ D^(⊗∞)`. No source for the measurable statement
  was searched beyond this graph; the argument is elementary.
- Collapse onto `X_∞` also answers two of the open structure questions on
  `bernoulli-isomorphism-collapse-set-is-a-subgroup` for `G`: `D(G) = R`, and `h^Rok_sup(G) = 0`.

**Model tests.**
- `X = X_∞` over any group satisfies 1, hence 2 and 3.
- `X = X_h` with `0 < h < ∞` over a sofic group fails 2: it is not even a self-square, by sofic entropy.
- Over a group with a self-square `X_h`, item 2 is open.
