---
rg: 2
id: fp-bieri-strebel-line-groups-are-deformation-rigid
kind: claim
title: A finitely presented Bieri--Strebel line group G(R;A,P) with P nontrivial is deformation-rigid, so after rescaling A lies in the real number field Q(P)
distinct_from:
  fp-pl-groups-with-f-have-no-transcendental-support-endpoints: that is a criterion for arbitrary finitely generated PL groups of an interval or circle containing a dyadic F, with data in one field Q(λ); this is the Bieri--Strebel line case for arbitrary parameters, with the stronger conclusion that the breakpoint module lies in the field of the slopes.
  complexity-bounded-host-classes-are-not-universal: that concerns word-problem bounds of host families; this is a finite-presentation obstruction for one classical family.
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

**ESTABLISHED** through `bieri-strebel-line-rigidity-proof` (lane proof, elementary given the
Bieri--Strebel presentation, not independently reviewed). No priority is claimed. A bounded check
found no such necessary condition: the Bieri--Strebel monograph (arXiv:1411.2868v3, read at source)
gives Proposition D13.3 (book p. 76) as necessary and Proposition D13.7 (p. 81) as sufficient. Its
Notes N3.3b say only such necessary and "far more demanding" sufficient conditions are known. A web
search on irrational- and transcendental-slope Bieri--Strebel groups (Cleary; Burillo--Nucinkis--Reeves;
Winstone's thesis; Molyneux--Nucinkis--Santos Rego) turned up nothing of this kind.

## Statement

Let `P ≤ R_{>0}` be a nontrivial subgroup and `A ⊂ R` a `Z[P]`-submodule (nonzero). Let
`G = G(R;A,P)`: all PL homeomorphisms of `R` with finitely many breakpoints, all in `A`, slopes in
`P`, mapping `A` onto `A`.

**Deformation space.** Let `D(A,P)` be the set of pairs `(χ, α)`, where `χ: P → R_{>0}` is a
homomorphism and `α: A → R` is additive with `α(p a) = χ(p) α(a)`. It carries the topology of
pointwise convergence on finite generating sets. `R_{>0}` acts on it by `c·(χ,α) = (χ, cα)`. Write
`ι = (incl, incl)`.

**Theorem.** If `G` is finitely presented, then `ι` has a neighborhood `U` in `D(A,P)` with
`U ⊆ R_{>0}·ι`. In other words, every nearby deformation keeps the slopes and rescales the
breakpoints.

**Corollaries.** Suppose `G` is finitely presented and `P ≠ 1`.
1. **Algebraic slopes.** `P` consists of real algebraic numbers, so `K = Q(P)` is a real number field.
2. **Breakpoints in the slope field.** For any nonzero `a ∈ A`, `A ⊆ K·a`. After rescaling `A`
   (which does not change `G` up to isomorphism), `A ⊆ Q(P)`. Equivalently,
   `Hom_{Z[P]}(A, R)` is the line `R·incl`. In particular `A` is directly indecomposable as a
   `Z[P]`-module.
3. **Rational slopes force rational breakpoints.** If `P ⊂ Q`, then `A ⊆ Q·a`.

## The necessary conditions of D13.3 are not sufficient

Let `τ` be **any** irrational number, `P = gp(2)`, `A = Z[1/2] + Z[1/2]τ`.

- `G(R;A,P)` is finitely generated: by Theorem 2 of the monograph's preface (Theorems B7.1 and B8.2),
  since `P` is finitely generated and `A` is a finitely generated `Z[P]`-module.
- `Aff(A,P) ≅ Z[1/2]^2 ⋊_2 Z` is finitely presented. It is the ascending HNN extension
  `⟨a, b, t | [a,b], t a t^{-1} = a^2, t b t^{-1} = b^2⟩` of `Z^2`.
- `A/(IP·A) = A/(2-1)A = 0`.

So the necessary conditions of Proposition D13.3 hold. But `Q(P) = Q` and `A ⊄ Q·1`, so by
Corollary 3 `G(R;A,P)` is **not finitely presented**. The same holds for `A = Z[1/n] + Z[1/n]τ`,
`P = gp(n)`, for every `n ≥ 2`, and for `G(R; Z[λ^{±1}], gp(λ))` with `λ` transcendental
(Corollary 1).

## Scope

- Only the line `I = R`: the proof uses the presentation of 13.3a (book pp. 80--81). The half-line
  and compact-interval versions are not claimed. For compact intervals that contain a dyadic `F`,
  the transcendental part is covered by `fp-pl-groups-with-f-have-no-transcendental-support-endpoints`.
- The converse is not claimed. The condition "`A` lies in the slope field and the slopes are algebraic"
  is still far from D13.7's sufficient condition that `A_{>0}` is a finitely generated semigroup
  with operators.
