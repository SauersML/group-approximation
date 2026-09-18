import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Support
import GroupApproximation.Steinberg.Functoriality

/-!
# Realizing corner transvections by Steinberg elements killed over the Leavitt algebra

For the matrix units `E_{ab} = e_{ij} ⊗ e_{μν}` of `M_N(C₂(𝔽₂))` over the kernel ideal
`(p) ≅ M_∞(𝔽₂)`, every corner transvection `1 + c E_{ab}` is the projection of a Steinberg element
whose image over `L_{𝔽₂}(1,2)` is trivial.  Off the diagonal of `Fin N` this is a single generator
`x_{ij}(c e_{μν})`; on it (`i = j`, `μ ≠ ν`) it is the commutator
`[x_{ik}(c e_{μν}), x_{ki}(e_{νν})]`.  Products of corner transvections are then realized as well.
This is step W1 of `simple_kazhdan_sofic_group.tex` l.733-735 (Ara-Brustenga-Cortiñas 2009,
excision for `(p) ≅ M_∞(𝔽₂)`).
-/

namespace GroupApproximation.Full.LVCohnRelK1

open SteinbergGroup

noncomputable section

/-- The matrix underlying the elementary projection of a Steinberg element
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
def projVal {N : ℕ} (s : SteinbergGroup (Fin N) CohnTwoF2) : Matrix (Fin N) (Fin N) CohnTwoF2 :=
  ((projection s : elementaryGroup (Fin N) CohnTwoF2) : (Matrix (Fin N) (Fin N) CohnTwoF2)ˣ)

theorem projVal_def {N : ℕ} (s : SteinbergGroup (Fin N) CohnTwoF2) :
    projVal s =
      ((projection s : elementaryGroup (Fin N) CohnTwoF2) : (Matrix (Fin N) (Fin N) CohnTwoF2)ˣ) :=
  rfl

theorem projVal_mul {N : ℕ} (s t : SteinbergGroup (Fin N) CohnTwoF2) :
    projVal (s * t) = projVal s * projVal t := by
  have h := congrArg (fun g : elementaryGroup (Fin N) CohnTwoF2 =>
    ((g : (Matrix (Fin N) (Fin N) CohnTwoF2)ˣ) : Matrix (Fin N) (Fin N) CohnTwoF2))
    (map_mul (projection (I := Fin N) (R := CohnTwoF2)) s t)
  exact h

theorem projVal_one {N : ℕ} : projVal (1 : SteinbergGroup (Fin N) CohnTwoF2) = 1 := by
  have h := congrArg (fun g : elementaryGroup (Fin N) CohnTwoF2 =>
    ((g : (Matrix (Fin N) (Fin N) CohnTwoF2)ˣ) : Matrix (Fin N) (Fin N) CohnTwoF2))
    (map_one (projection (I := Fin N) (R := CohnTwoF2)))
  exact h

theorem projVal_x {N : ℕ} (i j : Fin N) (h : i ≠ j) (a : CohnTwoF2) :
    projVal (x i j h a) = 1 + Matrix.single i j a := by
  have h1 := congrArg (fun g : elementaryGroup (Fin N) CohnTwoF2 =>
    ((g : (Matrix (Fin N) (Fin N) CohnTwoF2)ˣ) : Matrix (Fin N) (Fin N) CohnTwoF2))
    (projection_x (R := CohnTwoF2) i j h a)
  exact h1

/-- The commutator of `1 + A` and `1 + B` when `A² = B² = BA = 0`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem commutator_identity {R : Type*} [Ring R] (A B : R) (hAA : A * A = 0) (hBB : B * B = 0)
    (hBA : B * A = 0) : (1 + A) * (1 + B) * (1 + -A) * (1 + -B) = 1 + A * B := by
  have h1 : (1 + A) * (1 + B) * (1 + -A) = 1 + B + A * B - A * A - B * A - A * (B * A) := by
    noncomm_ring
  have h2 : (1 + B + A * B) * (1 + -B) = 1 + A * B - B * B - A * (B * B) := by
    noncomm_ring
  rw [h1, hAA, hBA, mul_zero, sub_zero, sub_zero, sub_zero, h2, hBB, mul_zero, sub_zero, sub_zero]

/-- Every corner transvection `1 + c E_{ab}` is the projection of a Steinberg element that dies
over the Leavitt algebra (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem exists_lift_generator {N : ℕ} [Nontrivial (Fin N)] (W : Finset (List Bool))
    (a b : Fin N × W) (hab : a ≠ b) (c : ZMod 2) :
    ∃ s : SteinbergGroup (Fin N) CohnTwoF2, ringMap toLeavitt s = 1 ∧
      projVal s = 1 + c • cornerE W N a b := by
  rw [cornerE_def, Matrix.smul_single]
  by_cases h1 : a.1 = b.1
  · have h2 : a.2.1 ≠ b.2.1 := fun h => hab (Prod.ext h1 (Subtype.ext h))
    obtain ⟨k, hk⟩ := exists_ne a.1
    rw [← h1]
    have hAA : Matrix.single a.1 k (c • unitE a.2.1 b.2.1) *
        Matrix.single a.1 k (c • unitE a.2.1 b.2.1) = 0 :=
      Matrix.single_mul_single_of_ne (c := c • unitE a.2.1 b.2.1) a.1 k a.1 hk _
    have hBB : Matrix.single k a.1 (unitE b.2.1 b.2.1) *
        Matrix.single k a.1 (unitE b.2.1 b.2.1) = 0 :=
      Matrix.single_mul_single_of_ne (c := unitE b.2.1 b.2.1) k a.1 k hk.symm _
    have hBA : Matrix.single k a.1 (unitE b.2.1 b.2.1) *
        Matrix.single a.1 k (c • unitE a.2.1 b.2.1) = 0 := by
      rw [Matrix.single_mul_single_same, mul_smul_comm, unitE_mul_unitE, if_neg h2.symm,
        smul_zero, Matrix.single_zero]
    have hAB : Matrix.single a.1 k (c • unitE a.2.1 b.2.1) *
        Matrix.single k a.1 (unitE b.2.1 b.2.1) =
          Matrix.single a.1 a.1 (c • unitE a.2.1 b.2.1) := by
      rw [Matrix.single_mul_single_same, smul_mul_assoc, unitE_mul_unitE, if_pos rfl]
    refine ⟨x a.1 k hk.symm (c • unitE a.2.1 b.2.1) * x k a.1 hk (unitE b.2.1 b.2.1) *
      x a.1 k hk.symm (-(c • unitE a.2.1 b.2.1)) * x k a.1 hk (-unitE b.2.1 b.2.1), ?_, ?_⟩
    · simp only [map_mul, ringMap_x, map_neg, toLeavitt_smul_unitE, toLeavitt_unitE, neg_zero,
        x_zero, mul_one]
    · simp only [projVal_mul, projVal_x]
      rw [← Matrix.single_neg, ← Matrix.single_neg, commutator_identity _ _ hAA hBB hBA, hAB]
  · refine ⟨x a.1 b.1 h1 (c • unitE a.2.1 b.2.1), ?_, projVal_x _ _ _ _⟩
    rw [ringMap_x, toLeavitt_smul_unitE, x_zero]

/-- Products of corner transvections are projections of Steinberg elements that die over the
Leavitt algebra (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem exists_lift_prod {N : ℕ} [Nontrivial (Fin N)] (W : Finset (List Bool)) :
    ∀ L : List (Matrix.TransvectionStruct (Fin N × W) (ZMod 2)),
      ∃ s : SteinbergGroup (Fin N) CohnTwoF2, ringMap toLeavitt s = 1 ∧
        projVal s = (L.map fun t => 1 + t.c • cornerE W N t.i t.j).prod
  | [] => ⟨1, map_one _, projVal_one⟩
  | t :: L => by
    obtain ⟨s, hs1, hs2⟩ := exists_lift_generator W t.i t.j t.hij t.c
    obtain ⟨s', hs1', hs2'⟩ := exists_lift_prod W L
    refine ⟨s * s', ?_, ?_⟩
    · rw [map_mul, hs1, hs1', mul_one]
    · rw [projVal_mul, hs2, hs2', List.map_cons, List.prod_cons]

end

end GroupApproximation.Full.LVCohnRelK1
