---
rg: 2
id: finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs
kind: claim
title: In a rational similarity group with finite nucleus, a free abelian group fixing a rational point acts through a germ group of rank at most one, so all but one direction of it is locally trivial there
distinct_from:
  rsg-proper-power-germ-torsion-via-cyclic-germ-groups: that uses the same virtually cyclic germ groups to control a Baumslag--Solitar-type relation f g^k f^-1 = g^l; this applies them to commuting elements, which is the constraint that flats in hierarchically hyperbolic, CAT(0) and automatic groups meet.
  rsg-proper-power-conjugate-germs-torsion-at-finite-orbits: that is about proper-power conjugation at finite orbits; this is about free abelian point stabilizers, with no conjugation relation.
  z2-free-z-embeds-in-a-finite-nucleus-rsg: that is the open host-class question for the free product Z^2 * Z; this is one constraint any positive answer must respect.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed).

**Setting.** `G ≤ R_{Γ,E}` is a rational similarity group (RSG) with finite
nucleus, in the sense of Belk--Bleak--Matucci--Zaremsky (BBMZ),
arXiv:2309.06224v3. A point of `E` is rational if it is eventually periodic.
`[G]_ω = Stab_G(ω)/Fix^0_G(ω)`, where `Fix^0_G(ω)` is the set of elements that
are the identity on a neighbourhood of `ω`.

**Statement.** Let `ω ∈ E` be a rational point and let `A ≤ Stab_G(ω)` be free
abelian of rank `r`.
1. The image of `A` in `[G]_ω` is finite or virtually infinite cyclic.
2. `A_ω := A ∩ Fix^0_G(ω)` has rank at least `r − 1`. So for `r ≥ 2` some
   nontrivial element of `A` is the identity on a neighbourhood of `ω`.
3. **Finite orbits.** If `A ≤ G` is free abelian of rank `r` and `O ⊆ E` is a
   finite `A`-orbit of rational points, then the pointwise stabilizer `A'` of `O`
   has finite index in `A`, and for every `ω ∈ O` the subgroup `A'_ω` has rank at
   least `r − 1`.

**Proof.**
- BBMZ `prop:CyclicStabilizers` (imported verbatim in
  `rsg-proper-power-germ-torsion-via-cyclic-germ-groups`, item 1): `[G]_ω` is
  virtually infinite cyclic for every rational `ω`.
- Every subgroup of a virtually infinite cyclic group is finite or virtually
  infinite cyclic, so it has torsion-free rank at most `1`. This gives item 1.
- The germ map `Stab_G(ω) → [G]_ω` is a homomorphism with kernel
  `Fix^0_G(ω) ∩ Stab_G(ω)`. Restricted to `A` its image has rank at most `1`,
  and ranks add along `0 → A_ω → A → image → 0`. This gives item 2.
- For item 3, `A` permutes the finite set `O`, so `A'` has finite index, hence
  rank `r`. Apply item 2 to `A'` at each point of `O`.

**Consequence for boundary models.** Suppose a group `H` acts faithfully on a
Cantor space `X`, and `φ: X → E` is an `H`-equivariant homeomorphism onto a
clopen `E ⊆ Σ_Γ` whose image of `H` lies in a finite-nucleus RSG. If some
`A ≅ Z^r ≤ H` with `r ≥ 2` fixes `x ∈ X` and no nontrivial element of `A` is the
identity near `x`, then `φ(x)` is not a rational point.

**Where this bites.** Natural boundaries of groups with flats have such points:
- In the horofunction boundary `∂_h Z^2 ≅ \hat Z^2 \ Z^2` of BBMZ `ex:Z2`
  (generating set `{(1,0),(0,1)}`), the corner `(+∞,+∞)` is fixed by `Z^2`. The
  element `(m,n)` sends `(k,+∞) ↦ (k+m,+∞)` and `(+∞,k) ↦ (+∞,k+n)`, and both
  families accumulate at the corner, so `(m,n)` is nontrivial on every
  neighbourhood of it unless `m = n = 0`.
- For a mapping class group acting on `PML`, a pair of Dehn twists about
  disjoint curves `a, b` fixes `[a]` and, heuristically, acts with faithful germs
  there. `PML` is a sphere, so this is only a guide for Cantor models that
  factor through it. It is not a claim.

**Scope.** Nothing here says that a group with flats cannot embed in a
finite-nucleus RSG. `V` is a finite-nucleus RSG and contains every `Z^r` (with
locally trivial directions, as the statement requires). The host-class question
for the first non-hyperbolic test case is `z2-free-z-embeds-in-a-finite-nucleus-rsg`.
