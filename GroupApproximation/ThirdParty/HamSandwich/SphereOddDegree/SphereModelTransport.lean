import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereTopHomologyReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.BallBoundaryLES

/-!
# Transport of sphere top-homology between sphere models

The conditional degree API of `Degree.lean` consumes, in each dimension `n ≥ 1`, a
term of the project type `SphereTopHomologyIso n`
(`= Hₙ(Sⁿ; ℤ) ≅ ℤ` over Mathlib's categorical sphere `TopCat.sphere n`).  A
top-homology computation `Hₙ(Sⁿ; ℤ) ≅ ℤ` might, however, be carried out in a
*different* model of the `n`-sphere — Mathlib's `TopCat.sphere n`, the project's
raw subtype model `Sphere n`, or any topological space homeomorphic (indeed merely
homotopy equivalent) to it.

This file supplies the **genuine, build-clean transport API** that converts a
homology identification in *any* such model into the exact project type expected by
the degree layer.  It builds only on existing infrastructure:

* `singularHomologyℤ_isoOfHomeomorph` / `singularHomologyℤ_isoOfHomotopyEquivSpace`
  (`BallBoundaryLES.lean`) — functoriality / homotopy invariance of integral
  singular homology;
* `topCatSphereIso` (`TopCatBridge.lean`) — the bridge `TopCat.sphere n ≅ Sphere n`;
* `sphereModelHomologyIso` and `sphereTopHomologyIso_of_modelIso`
  (`SphereTopHomology.lean`) — the homology-level model bridge.

No new top-homology isomorphism is asserted: every declaration here is a *transport*
that consumes a hypothesised `Hₙ(model; ℤ) ≅ ℤ` and re-expresses it over
`TopCat.sphere n`.  Thus *any* theorem about a Mathlib sphere model's top homology
can be converted into the project type, which is the acceptance criterion for this
step.  The single genuinely missing topological input remains the computation
`Hₙ(Sⁿ; ℤ) ≅ ℤ` itself (excision / suspension), absent from pinned Mathlib.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## Homology iso from a homeomorphism of spaces -/

/-- **Homology iso from a homeomorphism.** A homeomorphism `h : X ≃ₜ Y` induces an
isomorphism on the `k`-th integral singular homology, by functoriality of
`singularHomologyℤ` applied to the categorical isomorphism `TopCat.isoOfHomeo h`. -/
noncomputable def singularHomologyℤ_isoOfHomeomorph (k : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    (singularHomologyℤ k).obj (TopCat.of X) ≅ (singularHomologyℤ k).obj (TopCat.of Y) :=
  (singularHomologyℤ k).mapIso (TopCat.isoOfHomeo h)

/-! ## Transport into the raw `Sphere n` model -/

/-- Transport a top-homology identification `Hₙ(X; ℤ) ≅ ℤ` from a space `X`
homotopy equivalent to the raw model `Sphere n` onto `Hₙ(Sphere n; ℤ) ≅ ℤ`. -/
def modelIso_of_homotopyEquiv {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : ContinuousMap.HomotopyEquiv X (Sphere n))
    (h : (singularHomologyℤ n).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ) :
    (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ :=
  (singularHomologyℤ_isoOfHomotopyEquivSpace n e).symm ≪≫ h

/-- Transport a top-homology identification `Hₙ(X; ℤ) ≅ ℤ` from a space `X`
homeomorphic to the raw model `Sphere n` onto `Hₙ(Sphere n; ℤ) ≅ ℤ`. -/
def modelIso_of_homeomorph {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : X ≃ₜ Sphere n)
    (h : (singularHomologyℤ n).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ) :
    (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ :=
  (singularHomologyℤ_isoOfHomeomorph n e).symm ≪≫ h

/-! ## Transport into the project type `SphereTopHomologyIso n`

The degree layer consumes `SphereTopHomologyIso n`, which is definitionally
`Hₙ(TopCat.sphere n; ℤ) ≅ ℤ`.  These wrappers feed it from any sphere model. -/

/-- A top-homology identification over Mathlib's categorical sphere
`TopCat.sphere n` *is* the project type `SphereTopHomologyIso n` (the two are
definitionally equal); this is the trivial transport recording that fact. -/
def sphereTopHomologyIso_of_topCatSphere {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  e

/-- Transport a top-homology identification `Hₙ(X; ℤ) ≅ ℤ` from a space `X`
homotopy equivalent to `Sphere n` into the project type `SphereTopHomologyIso n`. -/
def sphereTopHomologyIso_of_homotopyEquiv {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : ContinuousMap.HomotopyEquiv X (Sphere n))
    (h : (singularHomologyℤ n).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  sphereTopHomologyIso_of_modelIso (modelIso_of_homotopyEquiv e h)

/-- Transport a top-homology identification `Hₙ(X; ℤ) ≅ ℤ` from a space `X`
homeomorphic to `Sphere n` into the project type `SphereTopHomologyIso n`. -/
def sphereTopHomologyIso_of_homeomorph {n : ℕ} {X : Type} [TopologicalSpace X]
    (e : X ≃ₜ Sphere n)
    (h : (singularHomologyℤ n).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  sphereTopHomologyIso_of_modelIso (modelIso_of_homeomorph e h)

/-! ## Transport of an entire positive family

If a top-homology computation is available for a whole family of sphere models
`X n` (each homotopy equivalent to `Sphere n`) in every dimension `n ≥ 1`, the
transport assembles a genuine (non-vacuous) `SphereOrientationPos`, hence the full
positive-degree integral degree theory. -/

/-- A family of top-homology identifications `Hₙ(X n; ℤ) ≅ ℤ`, where each `X n` is
homotopy equivalent to `Sphere n`, yields a positive sphere orientation. -/
def sphereOrientationPos_of_homotopyEquiv
    (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
    (e : ∀ n, ContinuousMap.HomotopyEquiv (X n) (Sphere n))
    (h : ∀ n, 1 ≤ n → ((singularHomologyℤ n).obj (TopCat.of (X n)) ≅ ModuleCat.of ℤ ℤ)) :
    SphereOrientationPos where
  iso n hn := sphereTopHomologyIso_of_homotopyEquiv (e n) (h n hn)

/-- A family of top-homology identifications `Hₙ(X n; ℤ) ≅ ℤ`, where each `X n` is
homeomorphic to `Sphere n`, yields a positive sphere orientation. -/
def sphereOrientationPos_of_homeomorph
    (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
    (e : ∀ n, X n ≃ₜ Sphere n)
    (h : ∀ n, 1 ≤ n → ((singularHomologyℤ n).obj (TopCat.of (X n)) ≅ ModuleCat.of ℤ ℤ)) :
    SphereOrientationPos where
  iso n hn := sphereTopHomologyIso_of_homeomorph (e n) (h n hn)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

