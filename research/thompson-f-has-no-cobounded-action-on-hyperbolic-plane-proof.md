---
rg: 2
id: thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof
kind: route
title: Linearity of Isom(H^2), the Tits alternative and simplicity of [F,F] force abelian images
target: thompson-f-has-no-cobounded-action-on-hyperbolic-plane
requires:
  - thompson-f-has-no-free-subgroups
  - abelian-isometry-groups-of-h2-are-not-cobounded
---

Imported facts.
- (P1) `thompson-f-has-no-free-subgroups`: `F` contains no non-abelian free subgroup
  (Brin–Squier, Invent. Math. 79 (1985)) and `F` is not elementary amenable
  (Cannon–Floyd–Parry, Enseign. Math. 42 (1996), §4).
- (P2) `[F,F]` is simple. Dudko–Medynets, arXiv:1212.1230, p. 10, read from the PDF on
  2026-09-12 (quoted in `thompson-f-character-simplex-citation`): "Observe that the
  commutator subgroup of F_(n,r) is a simple group and the abelianization of F_(n,r) is
  isomorphic to Z^n [1, Section 4]", with `F = F_(2,1)`; their reference [1] is
  Cannon–Floyd–Parry.
- (P3) Tits alternative: a finitely generated linear group over a field either contains a
  non-abelian free subgroup or is virtually solvable (J. Tits, *Free subgroups in linear
  groups*, J. Algebra 20 (1972), 250–270; statement checked against a secondary summary
  on 2026-09-13, the paper not re-read).
- (P4) `Isom(H^2) ≅ O^+(2,1) ⊂ GL_3(R)` (hyperboloid model), so it is a linear group.
- (P5) `abelian-isometry-groups-of-h2-are-not-cobounded`.

**Step 1: `[F,F]` is infinite and non-abelian.** If `[F,F]` were abelian, `F` would be
metabelian; if it were finite, `F` would be finite-by-abelian. Either way `F` would be
elementary amenable, contradicting (P1).

**Step 2: an infinite non-abelian simple group `S` is not virtually solvable.** If `H ≤ S`
has finite index and is solvable, its normal core `K` has finite index, so `K ≠ 1` since
`S` is infinite; simplicity gives `K = S`, so `S` is solvable. A solvable simple group is
abelian, contradicting non-abelian. Subgroups of virtually solvable groups are virtually
solvable, so no virtually solvable group contains `[F,F]`.

**Step 3.** Let `ρ: F → Isom(H^2)`, `Γ = ρ(F)`, `N = ker ρ`. By (P4) `Γ` is a finitely
generated linear group. It has no non-abelian free subgroup: if `ρ(a), ρ(b)` generate a
free group of rank 2, then any relation `w(a,b) = 1` in `F` gives `w(ρ(a),ρ(b)) = 1`, so
`a, b` generate a free group of rank 2 in `F`, contradicting (P1). By (P3), `Γ` is
virtually solvable.

**Step 4.** `N ∩ [F,F]` is normal in `[F,F]`, so by (P2) it is `1` or `[F,F]`.
- If `N ∩ [F,F] = 1`, then `ρ` restricted to `[F,F]` is injective and `[F,F]` embeds in the
  virtually solvable group `Γ`, contradicting Step 2.
- So `[F,F] ≤ N`, and `Γ` is a quotient of `F/[F,F]`, hence abelian.

**Step 5.** By (P5) the abelian group `Γ` has no coarsely dense orbit on `H^2`. ∎

Scope. Nothing about `H^2` beyond linearity of its isometry group and (P5) is used, so the
same proof shows: for every `n`, every isometric action of `F` on real hyperbolic space
`H^n` factors through `Z^2` (Isom(H^n) = O^+(n,1) is linear). Coboundedness then needs a
separate check in higher dimension; only `n = 2` is claimed here.
