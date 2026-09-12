import GroupApproximation.CharClass.LemmaTwoParity

/-!
# Lemma 2, assembled from Steps A, C and D

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3).

The manuscript's Lemma 2 says that over `M = S⁵ × Y` the projections `F ⊕ H` and
`𝟏² ⊕ H` are not Murray--von Neumann equivalent.  Both are complements inside the *same*
`V = 𝟏³ ⊕ H`, of the two unit sections

```text
e (x, y) = (e₃, 0)  and  s (x, y) = (x, 0)
```

respectively, so the statement lives in one matrix algebra with one index type
`VIdx = Fin 3 ⊕ HIdx` and needs no rectangular comparison:

```text
F ⊕ H = V − s sᴴ ,      𝟏² ⊕ H = V − e eᴴ .
```

That is the shape `FHmat` and `EHmat` below take, and `FHmat_eq_fromBlocks` records that
`FHmat` really is `(𝟏³ − x xᴴ) ⊕ H`, the repo's `STW59.Fproj` summed with `H`.

## The three inputs, and who owes them

* **Step A** (`cs-clutching`, wired in `CharClass/LemmaTwoUnitary.lean`): an equivalence of
  the two complements yields a continuous unitary `G` of `V` with `G *ᵥ e = s`.  Packaged
  here as `HasStepAUnitary`.
* **Step C** (`cc-thom`, from `LIXSectionManuscript`'s single zero plus the local
  homeomorphism at it): the top mod-2 Chern class of the mapping torus is nonzero.
* **Step D** (`cc-wu`, `LemmaTwoParity.LIXParityInput.gamma_top_eq_zero`): it is zero.

Steps C and D are hypotheses of `false_of_stepC_stepD` about an abstract top class, never
`sorry` and never `axiom`; each is a one-line consequence of its owner's endpoint once the
cohomology layer lands.

## Main results

* `FHmat`, `EHmat` — the two complements, in one ambient.
* `HasStepAUnitary` — Step A's output.
* `false_of_stepC_stepD` — **the contradiction**: Steps A, C and D are inconsistent.
* `not_continuousMvNEquiv` — **Lemma 2** in the continuous-field model.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The two complements -/

/-- `s sᴴ`, the rank-one projection onto the tautological line of `S⁵`, sitting in the
trivial block of `V`. -/
def sProj (m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  Matrix.fromBlocks (rankOneProj (bVec m)) 0 0 0

/-- `e eᴴ`, the rank-one projection onto the constant line `ℂ e₃`. -/
def eProj (_m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  Matrix.fromBlocks (rankOneProj eThree) 0 0 0

/-- `F ⊕ H`, the complement of the section `s` in `V`. -/
def FHmat (m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ := Vmat m - sProj m

/-- `𝟏² ⊕ H`, the complement of the section `e` in `V`. -/
def EHmat (m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ := Vmat m - eProj m

/-- `F ⊕ H` really is `(𝟏³ − x xᴴ) ⊕ H`; the first block is the repo's `STW59.Fproj`
evaluated at the point of `S⁵`. -/
theorem FHmat_eq_fromBlocks (m : baseM dd) :
    FHmat m = Matrix.fromBlocks (1 - rankOneProj (bVec m)) 0 0 (Hmat m) := by
  rw [FHmat, Vmat, sProj]
  ext p q
  cases p <;> cases q <;> simp [Matrix.sub_apply]

/-- `𝟏² ⊕ H` really is `(𝟏³ − e₃ e₃ᴴ) ⊕ H`. -/
theorem EHmat_eq_fromBlocks (m : baseM dd) :
    EHmat m = Matrix.fromBlocks (1 - rankOneProj eThree) 0 0 (Hmat m) := by
  rw [EHmat, Vmat, eProj]
  ext p q
  cases p <;> cases q <;> simp [Matrix.sub_apply]

/-! ## 2. Murray--von Neumann equivalence of continuous fields -/

/-- Murray--von Neumann equivalence in the continuous-field model: a continuous field of
partial isometries with the prescribed initial and final projections.  This is the model
`mappingTorus` and the whole `CharClass` layer work in; the bridge to
`MurrayVonNeumannEquiv` in `Matrix ι ι C(M, ℂ)` is `CharClass/LemmaTwoBridge.lean`. -/
def ContinuousMvNEquiv {ι M : Type*} [Fintype ι] [TopologicalSpace M]
    (P Q : M → Matrix ι ι ℂ) : Prop :=
  ∃ w : M → Matrix ι ι ℂ, Continuous w ∧ (∀ m, (w m)ᴴ * w m = P m) ∧ (∀ m, w m * (w m)ᴴ = Q m)

/-! ## 3. Step A's output -/

/-- **What Step A produces.**  A continuous unitary of the whole matrix algebra which
preserves `V` and carries the section `e` to the section `s`.  `cs-clutching`'s
`STW59.exists_continuous_corner_unitary_apply_eq` produces a corner unitary `g` with
`g *ᵥ e = s`, and `cornerExtend`/`isCornerUnitary_cornerExtend` extend it by `1 − V`;
that wiring is `CharClass/LemmaTwoUnitary.lean`. -/
def HasStepAUnitary (dd : Fin ℓ → ℕ) : Prop :=
  ∃ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G ∧
    (∀ m, IsCornerUnitary (Vmat m) (G m)) ∧
    (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)

/-! ## 4. The contradiction -/

/-- **Steps A, C and D are inconsistent.**

`topClass` stands for the top mod-2 Chern class of a rank-`r` bundle over
`S¹ × S⁵ × Y`, valued in any type with a zero; `stepC` is the odd side and `stepD` the
even side.  Nothing about `topClass` is assumed beyond the two hypotheses, so this is the
whole logical content of Lemma 2, with the topology quarantined in the owners' lanes. -/
theorem false_of_stepC_stepD {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (hA : HasStepAUnitary dd)
    (stepC : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0)
    (stepD : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    False := by
  obtain ⟨G, hGc, hGu, hGe⟩ := hA
  exact stepC G hGc hGu hGe (stepD G hGc hGu)

/-- **Lemma 2**, in the continuous-field model: over `S⁵ × Y` the complements `F ⊕ H` and
`𝟏² ⊕ H` of the two unit sections of `V = 𝟏³ ⊕ H` are not Murray--von Neumann
equivalent.

`stepA` is `cs-clutching`'s theorem in the shape `CharClass/LemmaTwoUnitary.lean` wires,
`stepC` is `cc-thom`'s and `stepD` is `cc-wu`'s. -/
theorem not_continuousMvNEquiv {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (stepA : ContinuousMvNEquiv (FHmat (dd := dd)) EHmat → HasStepAUnitary dd)
    (stepC : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0)
    (stepD : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    ¬ ContinuousMvNEquiv (FHmat (dd := dd)) EHmat :=
  fun h => false_of_stepC_stepD topClass (stepA h) stepC stepD

end GroupApproximation.CharClass
