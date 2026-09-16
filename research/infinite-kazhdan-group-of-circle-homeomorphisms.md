---
rg: 2
id: infinite-kazhdan-group-of-circle-homeomorphisms
kind: claim
title: Some infinite group with property (T) acts faithfully on the circle (Navas's Question 2)
distinct_from:
  infinite-left-orderable-kazhdan-group: that asks for an infinite Kazhdan group acting faithfully on the line, equivalently on the interval (Navas's Question 3); this asks for one acting faithfully on the circle (Question 2). A line action gives a circle action with a global fixed point, but a circle witness need not fix a point or lift to the line. The two statements are equivalent only through the lift dichotomy, via the two routes between them.
artifacts:
  - research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md
---

**Statement (OPEN).** Some infinite group with Kazhdan's property (T) embeds in
`Homeo(S^1)`.

A Kazhdan group is finitely generated, so this is Navas's question, verbatim from
*Group actions on 1-manifolds: a list of very concrete open questions*,
arXiv:1712.06462v2, p. 3:

> **Question 2.** Does there exist an infinite, finitely-generated Kazhdan group of
> circle homeomorphisms ?

Orientation does not matter. The orientation-preserving elements of such a group form a
subgroup of index at most 2, which is still infinite and Kazhdan.

**Status check (bounded, 2026-09-16).**

- Duchesne, *A group with Property (T) acting on the circle*, arXiv:2011.12861v3
  (IMRN 2023), p. 1: "The question of the existence of an infinite countable group with
  Property (T) acting faithfully on the circle is still open."
- Lodha--Matte Bon--Triestino, arXiv:1803.08567v4, §1 (p. 3): "It remains a wide open problem
  whether there exists an infinite Kazhdan group of circle homeomorphisms."
- An arXiv API listing for `abs:"property (T)" AND abs:circle` on 2026-09-16 returned
  9 entries, none a resolution.

This check covers only these sources. Web search was unavailable in that session.

On 2026-09-16 the referee re-checked the Navas, Duchesne and LMT quotes against the
arXiv LaTeX sources (v2, v3, v4), including the theorem numbers Duchesne Remark 1.7 and
LMT Corollary 1.5. The arXiv API listings for `abs:Kazhdan AND abs:circle`,
`abs:"property (T)" AND abs:circle` and `abs:"property (T)" AND abs:orderable` showed no
resolution.

**Equivalence with Question 3.** This claim and `infinite-left-orderable-kazhdan-group`
are equivalent:

- `infinite-left-orderable-kazhdan-group-from-circle` passes from the circle to the line,
  through `kazhdan-circle-group-lift-dichotomy`.
- `infinite-kazhdan-group-of-circle-homeomorphisms-from-line` passes from the line to
  the circle, through dynamical realization.

So an obstruction for either one is an obstruction for both, and so is a witness.

## Attempts

**Lift to the line.** The lift does not eliminate the problem; it reduces it to Question
3.

- By `kazhdan-circle-group-lift-dichotomy`, a Kazhdan `G ⊂ Homeo_+(S^1)` has either:
  - (A) a finite-index subgroup acting faithfully on `R`; or
  - (B) a central lift `Ĝ ⊂ Homeo_+(R)` that is Kazhdan.
- A negative answer therefore needs to handle both a zero real Euler class (A) and a
  nonzero one (B). The model for the second is BdlHV Example 1.7.13(iii): lifts of
  `Sp_{2n}(Z)`, for `n ≥ 2`, to the universal cover are Kazhdan with infinite centre.
  They are not groups of line homeomorphisms, because they have torsion. `SU(n)` is
  simply connected, so it lifts isomorphically to the universal cover of `Sp_{2n}(R)`.
  For example, `diag(A, A)` with `A = [[0,-1],[1,0]] ⊕ I_{n-2}` lies in
  `Sp_{2n}(Z) ∩ SU(n)` and has order 4, and its lift in that copy of `SU(n)` also has
  order 4. (Referee addition.)

**Regularity.** Dead, but only in regularity.

- Navas (survey p. 3): "If a finitely-generated group of `C^{3/2}` circle
  diffeomorphisms satisfies property (T), then it is finite."
- Lodha--Matte Bon--Triestino (arXiv:1803.08567v4, Corollary 1.5, p. 3):
  - every homomorphism from a countable Kazhdan group to `PDiff^{3/2}(S^1)` has finite
    image, and this covers PL circle homeomorphisms;
  - every homomorphism to the countably singular group `ΩDiff^{3/2}(S^1)` has a finite
    orbit.
- A witness therefore acts by homeomorphisms that are not piecewise `C^{3/2}`.

**Higher-rank lattices.** Dead for this family.

- Ghys (survey p. 3): such a lattice acting on the circle has a finite orbit.
- Duchesne's account of Deroin--Hurtado (arXiv:2011.12861v3 p. 1): lattices in higher
  rank simple connected Lie groups have finite image in `Homeo_+(S^1)`. The primary
  source was not re-read for this statement.

**Projective and lifted projective actions.** Dead.

- A homomorphism from a Kazhdan group into `PSL(2,R) ⊂ O(2,1)` has relatively compact
  image (BdlHV Theorem 2.12.7). Its closure is compact, so it lies in a conjugate of
  `PSO(2)` and is abelian. The image is then an abelian quotient of a Kazhdan group, so
  it is finite.
- For a homomorphism into the universal cover of `PSL(2,R)`, the image is virtually
  central. If it were infinite, it would have a finite-index subgroup mapping onto `Z`.
  So it is finite.

See artifact §6.1. Convergence-group actions would reduce to this case through the
Tukia / Gabai / Casson--Jungreis theorem that they are conjugate to Fuchsian actions;
that theorem was not re-read here.

**Invariant probability measure.** This is not an obstruction.

- A Kazhdan group preserving a probability measure on `S^1` has a finite-index subgroup
  with a global fixed point. This is the argument of
  `amenable-infinite-simple-circle-groups-fix-a-point-proof`, steps 3-5, with finiteness
  of abelian quotients replacing simplicity.
- Removing the fixed point gives a faithful line action of that subgroup `G_0`.
- The lifts of elements of `G_0` that fix one preimage of the point form a complement
  to `⟨T⟩` in `p^{-1}(G_0)`. So `p^{-1}(G_0)` maps onto `Z`, and since it has finite
  index in `Ĝ`, the group `Ĝ` is not Kazhdan. Hence `G` falls under case (A).

So this case only produces a Question 3 witness and gives no obstruction (artifact
§6.2).

**Uniform unitary obstructions.** Dead. Duchesne, Remark 1.7 (arXiv:2011.12861v3, p. 3), notes
that `Homeo_+(S^1)` itself has property (T) as a topological group. It has no nontrivial
unitary representations, by Glasner--Megrelishvili's WAP-triviality; that source was not
re-read. So no unitary representation defined on all subgroups can detect the failure of
(T).

**Relative property (T).** This is not an obstruction. Navas (survey p. 3) embeds
`SL(2,Z) ⋉ Z^2` in `Homeo(S^1)` by blowing up an orbit of the projective action, and that
group has relative property (T) with respect to `Z^2`.
