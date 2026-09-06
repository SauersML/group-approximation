# cc-projective — `H^*(ℂP^n)`, Leray–Hirsch, mod-2 Chern classes

Owns `GroupApproximation/CharClass/{ProjectiveSpace*,LerayHirsch*,Chern*}.lean`,
namespace `GroupApproximation.CharClass`.  Deliverables: §1.4 items 1–4 of
`notes/LIX_FULL_PROGRAM_2026-09-05.md`.

## Design in one paragraph

The topological inputs enter as **structures in element form** — `MVSequence`,
`GysinSequence`, `LerayHirschGraded` — so every theorem about them is proved now,
about any space carrying one, and instantiating them is the only thing that waits
on peers.  On top of that there are two views of the Chern classes.  The
**degreewise** one (`LerayHirschDegree.lean`) reads them straight off the
Leray–Hirsch coefficients of `ξ^r`, giving `γ_k ∈ H^{2k}(X;F₂)` with the degree
correct by construction and needing no ring at all; it is green and it is what
peers should consume today.  The **ring** one packages `⨁ H^{2n}` so that
`Polynomial` and `PowerBasis` apply and Whitney becomes multiplication of
polynomials; it waits on `cup_comm`, and it is the view cc-wu's `ParityData`
ultimately needs, over the *full* graded ring rather than the even part.

## 1. GREEN

All at the pin, per-lane clone `cc-projective`, `Build completed successfully`.

| module | jobs |
|---|---|
| `ProjectiveSpaceBasic` | 8686 |
| `ProjectiveSpaceChart` | 8686 |
| `ProjectiveSpaceHyperplane` | 8686 |
| `ProjectiveSpacePuncture` | 8686 |
| `ProjectiveSpaceRetract` | 8686 |
| `ProjectiveSpaceTwoCover` | 8683 |
| `ProjectiveSpaceSphere` | 8683 |
| `ProjectiveSpaceCover` | 8683 |
| `ProjectiveSpaceCohomology` | 8686 |
| `ProjectiveSpaceRing` | 8686 |
| `ProjectiveSpaceSymmetry` | 8676 |
| `LerayHirschAlgebra` | 8686 |
| `LerayHirschDegree` | 8683 |
| `ChernRelation` | 8686 |
| `ChernEuler` | 8686 |
| `ChernEvenPiece` | 8686 |
| `ChernEvenRing` | 8683 |
| `ChernEvenRingComm` | 8683 |
| `ChernClasses` | 8676 |
| `ProjectiveSpaceHomogeneous` | 8659 |
| `ProjectiveSpaceInputs` | 8784 |
| `LerayHirschDegree` (with `pull_injective`) | 8783 |
| `ProjectiveSpaceComputation` | 8791 |
| `ChernTotalRing` | 2464 |
| `ChernClasses` (over `TotalH`) | 2466 |

What that amounts to mathematically: the whole point-set chain over the
projection model; the Mayer–Vietoris computation of `H^*(ℂP^n;F₂)` reduced to one
`MVSequence` term and one lemma; the Gysin reduction of the ring to `h^n ≠ 0`;
the mod-2 Euler class of a line bundle; the Grothendieck relation as pure
algebra; the degreewise Chern classes with `γ_k ∈ H^{2k}` correct by
construction, their uniqueness, and injectivity of `π^*` — the half of
Leray–Hirsch the splitting principle runs on; path-connectedness of `ℂP^d`; and
its homogeneity, which is what cc-thom's punctured recursion needed.

`ProjectiveSpaceComputation.lean` carries the induction itself,
`hasCPCohomology_CPtop`, with the Mayer–Vietoris sequence and the degree-zero
surjectivity as explicit hypotheses.  **Item 1 is therefore finished on this
lane's side**: supplying those two arguments turns it into the unconditional
`H^*(ℂP^n;F₂)`, with no further work here.

## 2. AUTHORED, UNVERIFIED

*(nothing)*

## 3. NEEDS

**From `cc-cohom-api`, the one blocking item:** an `MVSequence` term for a
two-open cover,

```lean
def mvSequence (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVSequence X (TopCat.of (U : Set X)) (TopCat.of (V : Set X))
      (TopCat.of ((U : Set X) ∩ (V : Set X)))
```

The three exactness fields come from their three `ShortComplex.Exact`s through
`ShortComplex.moduleCat_exact_iff`; cc-thom established that the biproduct
identification of the middle term is *not* needed, the pair form following from
the four biproduct identities carried through the additive dualizing functor.
and, alongside it,

```lean
theorem one_ne_zero_cohZero (X : TopCat.{0}) [Nonempty X] : one X ≠ (0 : Hmod2 X 0)
```

which is the whole content of the induction's remaining hypothesis: restriction
`H^0(U) → H^0(W)` is onto because both are lines and `1` goes to `1`.  Everything
else downstream of those two is proved.  Later, for Leray–Hirsch and not before:
the `H^*(X)`-linearity of the connecting map, `mvDelta_cup`.

**From `cc-thom`, the two remaining:** `mvResWU_eq_pull`, or just its degree-zero
corollary `mvResWU_one`, which is the last hypothesis of the projective-space
induction; and `mvDelta_cup`, linearity of the connecting map over classes pulled
back from the ambient space, which the Leray–Hirsch ladder and the `CP`-factor
Künneth both need and which cannot be arranged away.

**Superseded, nothing imports them:** `ChernEvenPiece`, `ChernEvenRing`,
`ChernEvenRingComm`.  Green but dead; recommend not wiring them into the root.

**From `cc-bundle`:** the projective bundle `P(p)` with its tautological line,
`P(p) ⊆ P(p ⊕ 1)`, `E(p) = P(p⊕1) ∖ P(p)`, the zero section, a finite
trivializing cover with the local homeomorphisms, the classifying map of a
rank-one projection with the rotation homotopy, and the flag bundle.

**From `cc-relative`:** the vanishing-product lemma — classes vanishing on the
two members of an open cover have zero cup product — for Whitney.

## 4. TRAPS

* **A definition whose result is a class needs `@[reducible]`**, or nothing
  downstream unifies against it.  Hit three times in this lane: `CPtop`, the
  graded ring structure, and the algebra of a projective bundle.
* **The `DirectSum` semiring diamond, and how it was settled.**  With an even
  ring plus a commutativity *hypothesis*, the direct sum acquired a `Semiring` by
  two syntactically different routes, `DirectSum.semiring` from the graded
  structure and `CommRing.toCommSemiring.toSemiring` from the hypothesis.  They
  are definitionally equal but not syntactically so, and every type mentioning
  the ring — `Polynomial`, the `1` of `γ₀ = 1`, the `0` of the rank bound — pins
  one at elaboration.  Nothing local settled it.  Migrating to the full graded
  ring did, because there the graded structure is the only source of the ring and
  the two routes coincide by projection.  General lesson: do not mix a graded-ring
  instance with a separate `CommRing` hypothesis on the same carrier.
* **`GradedMonoid.GMonoid`'s `gnpow` defaults need ambient `GMul` and `GOne`.**
  Lean fills them from `gnpowRec`, whose synthesis has nothing to find if the
  family has no instance yet.  Supply them by `letI` inside the construction;
  they agree with the `mul`/`one` fields on the nose.
* **Duplicate declarations across lanes break the root import.**  This lane and
  `cc-cohom-api` both defined `hasSphereCohomology_sphere`; theirs is the one,
  mine is deleted and `CohomologyShapes` imported.  Everything in this lane sits
  directly in `GroupApproximation.CharClass` rather than a sub-namespace, which is
  what made the collision possible.  New declarations go in a sub-namespace; the
  *published* names are not being renamed, because `MVSequence`,
  `HasCPCohomology`, `HasPointCohomology`, `HasSphereCohomology`, `TotalH`,
  `lineGen`, `toLinearZMod2` and `cupPowE` are already imported by cc-thom,
  cc-cohom-api and cc-lix-odd, and a rename would break three lanes at once.
* **A `git add` chained behind a step that can fail silently drops files.**  It
  cost a dangling import on main: `ChernClasses.lean` landed importing
  `ChernTotalRing.lean`, which was never committed.  The lane that notices is the
  one whose *other* file imports them, not the one that wrote them.
* **`git pull` aborts on a *peer's* uncommitted file** in the shared tree, and
  neither committing nor stashing it is yours to do.  Push and let the peer's own
  push carry your commits, or wait.
* **`RingHom.toAlgebra` wants a `CommSemiring` target**, and `RingHom.toAlgebra'`
  wants the image central.  Both are graded commutativity, so the algebra
  structure of a projective bundle cannot be built before `cup_comm`; taking it
  as an ambient instance variable does not dodge the diamond above.
* **`PowerBasis` asks only `[Ring S]`.**  Asking `[CommRing B]` in the Chern
  algebra was gratuitous and forced commutativity of the total space; it is now
  `[Ring B]` everywhere except `section Split`, where a `Finset.prod` is taken.
* **Mathlib names at this pin**: `Matrix.dotProduct` is `dotProduct`;
  `Polynomial.finset_sum_coeff` is `finsetSum_coeff`; `Polynomial.natDegree_prod`
  needs `NoZeroDivisors`, so use `natDegree_prod_of_monic`;
  `PowerBasis.degree_minpolyGen` needs `[Nontrivial A]` on the *source* ring.
* **`Nat.mul` recurses on its second argument**, so `2 * 0` reduces to `0` and
  `2 * (m+1)` to `2*m + 2`, definitionally.  Cup powers of a degree-2 class need
  no transport at all.  `0 + p` does *not* reduce, which is why left unitality
  does.
* **Over `F₂` every additive map is linear** (`∀ z : ZMod 2, z = 0 ∨ z = 1` by
  `decide`), which sidesteps the `CompatibleSMul _ _ (ZMod 2) ℤ` failure when
  turning a Mayer–Vietoris map into a `LinearEquiv`.  `toLinearZMod2`.
* **An `F₂`-line has a *unique* nonzero element**, so the degree-2 generator of
  `H^*(ℂP^n)` needs no orientation choice.  `lineGen`, with `lineGen_eq`.
* **A section `variable (mv : …)` is not in scope** in a theorem whose statement
  does not mention it, and `mv.foo` then fails with `Unknown identifier`.
* **`rw` on a `def` whose body is a nested `dite`** has no equation lemma; use
  `unfold` or `show`.
* **`ext` on a `ContinuousMap` into a matrix subtype goes too far**, destructuring
  into entries; use `ContinuousMap.ext`.
* **The paused fleet's `AlgTop/ComplexProjective*` is red and unowned** (an
  unused simp argument in `ComplexProjectiveBasic`, fatal under
  `-DwarningAsError=true`).  The chain is re-proved here instead.  Two further
  breakages surfaced in the copy: `rw [normalize]` unfolds only the first of two
  occurrences, and `rw […, sq]` normalises only the numerator of `‖·‖²/r²`.
