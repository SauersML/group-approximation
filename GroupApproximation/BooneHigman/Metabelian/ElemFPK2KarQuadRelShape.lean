import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative conjugates: stably short products and relative commutator shapes

Lane `bh-met-93t`, shape module.  `P = k2DilateSt_pullback s`, `gens = k2KarRel_gens s M`
(the conjugates `g x_ij(b) g⁻¹`, `g ∈ St(M, P)` arbitrary, `fst b = 0`).

* `k2KarQuadRel_gens_conj`, `k2KarQuadRel_gens_indexMap`: `gens` is closed under conjugation
  by arbitrary `k ∈ St(M, P)` and under padding `St(M, P) → St(M', P)`.
* **`k2KarQuadRel_stDies_of_short`** (domain `A`, `s ≠ 0`): if `St(snd) y = 1` and SOME padding
  of `y` is a product of at most three elements of `gens` (at the padded level), then `y`
  dies.  Uses `k2KarTri_boundedAt_three` at the padded level; relativity enters through
  `gens` and through `snd` (not only `padMat`).
* **`k2KarQuadRel_stDies_comm`**, **`k2KarQuadRel_stDies_comm'`**: for `w ∈ gens` and
  `g ∈ St(M, P)` ARBITRARY, `⁅g, w⁆` and `⁅w, g⁆` die as soon as their `snd`-image is trivial
  (they are products of two elements of `gens`; `k2KarInd_boundedAt_two`).
* **`k2KarQuadRel_stDies_quad_comm`**: the four-conjugate shape of the LOUD field
  counterexample of lane `bh-met-93q`, `z₁ z₂ (w z₂⁻¹ w⁻¹) (w z₁⁻¹ w⁻¹) = ⁅z₁ z₂, w⁆`, dies
  when the "twist" `w` is a single RELATIVE conjugate (`z₁`, `z₂` arbitrary).

## LOUD: what this does and does not cover

* In the `bh-met-93q` counterexample (over `ℚ`, non-relative) the twist `k̃` lies in a torus,
  so it is not relative; here the twist is relative and the product dies.
* **Matrix-level degeneration (paper argument, checked by `bh-met-93t/truth_check.py`).**  If
  `z₁, z₂` are relative conjugates with `rank (padMat (z₁ z₂) - 1) = 2` and `w` is a relative
  conjugate with trivial `snd ⁅z₁ z₂, w⁆`, then `padMat w` commutes with `G = padMat (z₁ z₂)`,
  so `padMat w = 1 + u vᵀ` with `u`, `v` right/left eigenvectors of `G` for one eigenvalue
  and `v ⬝ᵥ u = 0`.  Every eigenvalue other than `1` is simple (the only other candidate,
  `-1`, would need `tr (a b) = -4` for `a, b ≡ 0 mod X`), so `u ∈ ker (G - 1) = {t, q}⊥` and
  `v ∈ leftker (G - 1) = {r, p}⊥`, where `padMat z₁ = 1 + r tᵀ` and `padMat z₂ = 1 + p qᵀ`.
  Then `padMat w` commutes with `padMat z₂`, so `padMat (z₂ z₃) = 1` and the pair is rank-one.
  **Hence the shape `k2KarQuadRel_stDies_quad_comm` lies (at the matrix level) OUTSIDE the
  domain of `k2KarQuad_GenericAt`.**  It is recorded because it shows relativity of the twist
  is what kills the counterexample shape, not because it shrinks the generic case.
* What does shrink the generic case is `k2KarQuadRel_stDies_of_short`: see
  `ElemFPK2KarQuadRelStatement` (the residual `k2KarQuadRel_LongAt`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadRelGens

variable {A : Type*} [CommRing A] {s : A}

/-- `gens` is closed under conjugation by an arbitrary element of `St(M, P)`. -/
theorem k2KarQuadRel_gens_conj {M : ℕ} (k : SteinbergGroup (Fin M) (k2DilateSt_pullback s))
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)} (hy : y ∈ k2KarRel_gens s M) :
    k * y * k⁻¹ ∈ k2KarRel_gens s M := by
  obtain ⟨g, i, j, hij, b, hb, rfl⟩ := hy
  exact ⟨k * g, i, j, hij, b, hb, by group⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_gens_conj

/-- `gens` is closed under padding. -/
theorem k2KarQuadRel_gens_indexMap {M M' : ℕ} (hM : M ≤ M')
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)} (hy : y ∈ k2KarRel_gens s M) :
    SteinbergGroup.indexMap (Fin.castLEEmb hM) y ∈ k2KarRel_gens s M' := by
  obtain ⟨g, i, j, hij, b, hb, rfl⟩ := hy
  refine ⟨SteinbergGroup.indexMap (Fin.castLEEmb hM) g, Fin.castLEEmb hM i,
    Fin.castLEEmb hM j, (Fin.castLEEmb hM).injective.ne hij, b, hb, ?_⟩
  rw [map_mul, map_mul, map_inv, indexMap_x]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_gens_indexMap

end KarQuadRelGens

section KarQuadRelShape

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **Stably short products die**: if a padding of `y` is a product of at most three
elements of `gens` and `St(snd) y = 1`, then `y` dies. -/
theorem k2KarQuadRel_stDies_of_short (hs : s ≠ 0) {M M' : ℕ} (hM : M ≤ M')
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (l : List (SteinbergGroup (Fin M') (k2DilateSt_pullback s))) (hlen : l.length ≤ 3)
    (hl : ∀ z ∈ l, z ∈ k2KarRel_gens s M')
    (he : l.prod = SteinbergGroup.indexMap (Fin.castLEEmb hM) y)
    (hsnd : ringMap (k2PullRel_snd s) y = 1) : cubeDiagDilate_StDies y := by
  refine cubeDiagDilate_stDies_of_indexMap hM ?_
  rw [← he]
  refine k2KarTri_boundedAt_three hs M' l hlen hl ?_
  rw [he, ← GroupApproximation.Full.LVStableK2.indexMap_ringMap, hsnd, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_stDies_of_short

/-- **Relative commutators die**: `⁅g, w⁆` with `w ∈ gens`, `g` arbitrary. -/
theorem k2KarQuadRel_stDies_comm (hs : s ≠ 0) {M : ℕ}
    (g w : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) (hw : w ∈ k2KarRel_gens s M)
    (hsnd : ringMap (k2PullRel_snd s) ⁅g, w⁆ = 1) : cubeDiagDilate_StDies ⁅g, w⁆ := by
  have e : [g * w * g⁻¹, w⁻¹].prod = ⁅g, w⁆ := by
    rw [commutatorElement_def]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← e] at hsnd ⊢
  refine k2KarInd_boundedAt_two hs M _ (by simp) (fun z hz ↦ ?_) hsnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact k2KarQuadRel_gens_conj g hw
  · exact k2KarRel_gens_inv hw

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_stDies_comm

/-- **Relative commutators die** (other order): `⁅w, g⁆` with `w ∈ gens`, `g` arbitrary. -/
theorem k2KarQuadRel_stDies_comm' (hs : s ≠ 0) {M : ℕ}
    (w g : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) (hw : w ∈ k2KarRel_gens s M)
    (hsnd : ringMap (k2PullRel_snd s) ⁅w, g⁆ = 1) : cubeDiagDilate_StDies ⁅w, g⁆ := by
  have e : [w, g * w⁻¹ * g⁻¹].prod = ⁅w, g⁆ := by
    rw [commutatorElement_def]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← e] at hsnd ⊢
  refine k2KarInd_boundedAt_two hs M _ (by simp) (fun z hz ↦ ?_) hsnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hw
  · exact k2KarQuadRel_gens_conj g (k2KarRel_gens_inv hw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_stDies_comm'

/-- **The counterexample shape with a relative twist dies**:
`z₁ z₂ (w z₂⁻¹ w⁻¹) (w z₁⁻¹ w⁻¹) = ⁅z₁ z₂, w⁆` with `w ∈ gens` (`z₁`, `z₂` arbitrary). -/
theorem k2KarQuadRel_stDies_quad_comm (hs : s ≠ 0) {M : ℕ}
    (z₁ z₂ w : SteinbergGroup (Fin M) (k2DilateSt_pullback s)) (hw : w ∈ k2KarRel_gens s M)
    (hsnd : ringMap (k2PullRel_snd s) (z₁ * z₂ * (w * z₂⁻¹ * w⁻¹) * (w * z₁⁻¹ * w⁻¹)) = 1) :
    cubeDiagDilate_StDies (z₁ * z₂ * (w * z₂⁻¹ * w⁻¹) * (w * z₁⁻¹ * w⁻¹)) := by
  have e : z₁ * z₂ * (w * z₂⁻¹ * w⁻¹) * (w * z₁⁻¹ * w⁻¹) = ⁅z₁ * z₂, w⁆ := by
    rw [commutatorElement_def]
    group
  rw [e] at hsnd ⊢
  exact k2KarQuadRel_stDies_comm hs (z₁ * z₂) w hw hsnd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuadRel_stDies_quad_comm

end KarQuadRelShape

end GroupApproximation.BooneHigman.Metabelian.ElemFP
