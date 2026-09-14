import GroupApproximation.Analysis.TwistedGroupVonNeumannFactor

/-!
# The Pauli model of the hyperfinite II₁ factor

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93), where `𝓡` is the hyperfinite II₁ factor.

The model is the twisted group von Neumann algebra of the **Pauli group**
`Γ = Multiplicative (V × V)`, `V = ℕ →₀ ZMod 2`: an element `(x, z)` is the Pauli word
`Π_i X_i^{x_i} Z_i^{z_i}`, and the sign cocycle `σ((x,z),(x',z')) = Σᵢ zᵢ x'ᵢ` records that `Z_i`
and `X_i` anticommute.

* `dot`: the `ZMod 2` dot product on `V`, bi-additive.
* `pauliCocycle`, `pauliCocycle_isSignCocycle`.
* `pauliCocycle_isTwistedICC`: for `(x,z) ≠ 0` a single-site `Z_i` or `X_i` commutes with it with
  differing cocycle values.
* `hyperfiniteFactor`, `isIIOneFactor_hyperfiniteFactor`: `𝓡 := L_σ(Γ)` is a II₁ factor.
* `pauliInterleave`, `pauliCocycle_interleave`: even and odd sites give `Γ × Γ ≃* Γ`, carrying the
  cocycle to the sum of the two cocycles.  This is the spatial identification behind `𝓡 ⊗̄ 𝓡 ≅ 𝓡`.

Hyperfiniteness (the finite Pauli stages `≅ M_{2^j}` are dense in the 2-norm) is
`Analysis/PauliMatrixUnits.lean`.
-/

namespace GroupApproximation
namespace Hyperfinite

open TwistedGroupVonNeumann

noncomputable section

/-! ## The dot product on finitely supported binary sequences -/

/-- The coordinates of one half of a Pauli word. -/
abbrev PauliCoord := ℕ →₀ ZMod 2

/-- The `ZMod 2` dot product `Σᵢ uᵢ vᵢ`. -/
def dot (u v : PauliCoord) : ZMod 2 :=
  u.sum fun i c ↦ c * v i

@[simp]
theorem dot_zero_left (v : PauliCoord) : dot 0 v = 0 :=
  Finsupp.sum_zero_index

@[simp]
theorem dot_zero_right (u : PauliCoord) : dot u 0 = 0 := by
  simp [dot]

theorem dot_add_left (u u' v : PauliCoord) : dot (u + u') v = dot u v + dot u' v :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

theorem dot_add_right (u v v' : PauliCoord) : dot u (v + v') = dot u v + dot u v' := by
  simp only [dot, Finsupp.add_apply, mul_add]
  exact Finsupp.sum_add

theorem dot_single_left (i : ℕ) (c : ZMod 2) (v : PauliCoord) :
    dot (Finsupp.single i c) v = c * v i :=
  Finsupp.sum_single_index (zero_mul _)

theorem dot_single_right (u : PauliCoord) (i : ℕ) :
    dot u (Finsupp.single i 1) = u i := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [dot_add_left, hf, hg, Finsupp.add_apply]
  | single j c =>
    rw [dot_single_left, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji, Ne.symm hji]

/-! ## The Pauli group and its sign cocycle -/

/-- **The Pauli group**: `(x, z)` stands for the Pauli word `Π_i X_i^{x_i} Z_i^{z_i}`. -/
abbrev PauliGroup := Multiplicative (PauliCoord × PauliCoord)

/-- **The Pauli sign cocycle** `σ((x,z),(x',z')) = z · x'`. -/
def pauliCocycle (g k : PauliGroup) : ZMod 2 :=
  dot (Multiplicative.toAdd g).2 (Multiplicative.toAdd k).1

theorem pauliCocycle_isSignCocycle : IsSignCocycle pauliCocycle where
  map_one_left g := by simp [pauliCocycle]
  map_one_right g := by simp [pauliCocycle]
  cocycle g h k := by
    simp only [pauliCocycle, toAdd_mul, Prod.fst_add, Prod.snd_add, dot_add_left,
      dot_add_right]
    ring

theorem zmod_two_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert h
  revert c
  decide

/-- **The Pauli cocycle is twisted-ICC.** -/
theorem pauliCocycle_isTwistedICC : IsTwistedICC pauliCocycle := by
  intro a ha
  right
  rcases hxz : Multiplicative.toAdd a with ⟨x, z⟩
  have hne : ((x, z) : PauliCoord × PauliCoord) ≠ 0 := by
    intro h
    apply ha
    apply Multiplicative.toAdd.injective
    rw [hxz, h, toAdd_one]
  by_cases hx : x = 0
  · have hz : z ≠ 0 := by
      intro hz
      apply hne
      rw [hx, hz, Prod.mk_zero_zero]
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hz
    have hi1 : z i = 1 := zmod_two_eq_one_of_ne_zero hi
    refine ⟨Multiplicative.ofAdd (Finsupp.single i 1, 0), mul_comm _ _, ?_⟩
    have h1 : pauliCocycle (Multiplicative.ofAdd (Finsupp.single i 1, 0)) a = 0 := by
      simp only [pauliCocycle, toAdd_ofAdd, hxz, dot_zero_left]
    have h2 : pauliCocycle a (Multiplicative.ofAdd (Finsupp.single i 1, 0)) = 1 := by
      simp only [pauliCocycle, toAdd_ofAdd, hxz, dot_single_right, hi1]
    rw [h1, h2]
    decide
  · obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hx
    have hi1 : x i = 1 := zmod_two_eq_one_of_ne_zero hi
    refine ⟨Multiplicative.ofAdd (0, Finsupp.single i 1), mul_comm _ _, ?_⟩
    have h1 : pauliCocycle (Multiplicative.ofAdd (0, Finsupp.single i 1)) a = 1 := by
      simp only [pauliCocycle, toAdd_ofAdd, hxz, dot_single_left, hi1, one_mul]
    have h2 : pauliCocycle a (Multiplicative.ofAdd (0, Finsupp.single i 1)) = 0 := by
      simp only [pauliCocycle, toAdd_ofAdd, hxz, dot_zero_right]
    rw [h1, h2]
    decide

instance pauliGroup_infinite : Infinite PauliGroup :=
  Infinite.of_injective
    (fun n : ℕ ↦
      Multiplicative.ofAdd ((Finsupp.single n (1 : ZMod 2), 0) : PauliCoord × PauliCoord))
    (by
      intro n m h
      have h1 := congrArg (fun g : PauliGroup ↦ (Multiplicative.toAdd g).1) h
      simp only [toAdd_ofAdd] at h1
      exact (Finsupp.single_left_inj one_ne_zero).mp h1)

/-! ## The hyperfinite II₁ factor -/

/-- **The hyperfinite II₁ factor** `𝓡`, as the twisted group von Neumann algebra of the Pauli group
on `ℓ²(PauliGroup)`. -/
def hyperfiniteFactor : VonNeumannAlgebra (ReducedGroupCStarTrace.GroupHilbert PauliGroup) :=
  twistedVonNeumannAlgebra pauliCocycle

/-- **`𝓡` is a II₁ factor.** -/
theorem isIIOneFactor_hyperfiniteFactor : IIOneFactor.IsIIOneFactor hyperfiniteFactor :=
  isIIOneFactor_twistedVonNeumannAlgebra pauliCocycle pauliCocycle_isSignCocycle
    pauliCocycle_isTwistedICC

/-! ## Interleaving two Pauli groups -/

/-- Interleave two binary sequences on the even and odd sites. -/
def interleave : PauliCoord × PauliCoord ≃+ PauliCoord :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm.trans (Finsupp.domCongr Equiv.natSumNatEquivNat)

theorem interleave_apply_even (u v : PauliCoord) (i : ℕ) :
    interleave (u, v) (2 * i) = u i := by
  have h : Equiv.natSumNatEquivNat.symm (2 * i) = Sum.inl i := by
    rw [Equiv.symm_apply_eq, Equiv.natSumNatEquivNat_apply, Sum.elim_inl]
  simp only [interleave, AddEquiv.trans_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, h, Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl]

theorem interleave_apply_odd (u v : PauliCoord) (i : ℕ) :
    interleave (u, v) (2 * i + 1) = v i := by
  have h : Equiv.natSumNatEquivNat.symm (2 * i + 1) = Sum.inr i := by
    rw [Equiv.symm_apply_eq, Equiv.natSumNatEquivNat_apply, Sum.elim_inr]
  simp only [interleave, AddEquiv.trans_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, h, Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr]

theorem interleave_single_left (i : ℕ) (c : ZMod 2) :
    interleave (Finsupp.single i c, 0) = Finsupp.single (2 * i) c := by
  apply Finsupp.ext
  intro n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [interleave_apply_even, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · have hne : 2 * i ≠ 2 * k := by omega
      simp [hik, hne]
  · rw [interleave_apply_odd, Finsupp.single_apply]
    have hne : 2 * i ≠ 2 * k + 1 := by omega
    simp [hne]

theorem interleave_single_right (i : ℕ) (c : ZMod 2) :
    interleave (0, Finsupp.single i c) = Finsupp.single (2 * i + 1) c := by
  apply Finsupp.ext
  intro n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [interleave_apply_even, Finsupp.single_apply]
    have hne : 2 * i + 1 ≠ 2 * k := by omega
    simp [hne]
  · rw [interleave_apply_odd, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]

theorem interleave_zero : interleave (0, 0) = 0 := by
  rw [Prod.mk_zero_zero, map_zero]

theorem interleave_left_add (f g : PauliCoord) :
    interleave (f + g, 0) = interleave (f, 0) + interleave (g, 0) := by
  rw [← map_add interleave, Prod.mk_add_mk, add_zero]

theorem interleave_right_add (f g : PauliCoord) :
    interleave (0, f + g) = interleave (0, f) + interleave (0, g) := by
  rw [← map_add interleave, Prod.mk_add_mk, add_zero]

theorem dot_interleave_left_left (u u' : PauliCoord) :
    dot (interleave (u, 0)) (interleave (u', 0)) = dot u u' := by
  induction u using Finsupp.induction_linear with
  | zero => rw [interleave_zero, dot_zero_left, dot_zero_left]
  | add f g hf hg => rw [interleave_left_add, dot_add_left, dot_add_left, hf, hg]
  | single j c =>
    rw [interleave_single_left, dot_single_left, dot_single_left, interleave_apply_even]

theorem dot_interleave_left_right (u v' : PauliCoord) :
    dot (interleave (u, 0)) (interleave (0, v')) = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => rw [interleave_zero, dot_zero_left]
  | add f g hf hg => rw [interleave_left_add, dot_add_left, hf, hg, add_zero]
  | single j c =>
    rw [interleave_single_left, dot_single_left, interleave_apply_even]
    simp

theorem dot_interleave_right_left (v u' : PauliCoord) :
    dot (interleave (0, v)) (interleave (u', 0)) = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => rw [interleave_zero, dot_zero_left]
  | add f g hf hg => rw [interleave_right_add, dot_add_left, hf, hg, add_zero]
  | single j c =>
    rw [interleave_single_right, dot_single_left, interleave_apply_odd]
    simp

theorem dot_interleave_right_right (v v' : PauliCoord) :
    dot (interleave (0, v)) (interleave (0, v')) = dot v v' := by
  induction v using Finsupp.induction_linear with
  | zero => rw [interleave_zero, dot_zero_left, dot_zero_left]
  | add f g hf hg => rw [interleave_right_add, dot_add_left, dot_add_left, hf, hg]
  | single j c =>
    rw [interleave_single_right, dot_single_left, dot_single_left, interleave_apply_odd]

/-- The dot product of interleaved sequences is the sum of the two dot products. -/
theorem dot_interleave (u v u' v' : PauliCoord) :
    dot (interleave (u, v)) (interleave (u', v')) = dot u u' + dot v v' := by
  have hsplit : ∀ p q : PauliCoord,
      interleave (p, q) = interleave (p, 0) + interleave (0, q) := by
    intro p q
    rw [← map_add interleave, Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit u v, hsplit u' v', dot_add_left, dot_add_right, dot_add_right,
    dot_interleave_left_left, dot_interleave_left_right, dot_interleave_right_left,
    dot_interleave_right_right, add_zero, zero_add]

/-- **Interleaving two Pauli groups** on the even and odd sites. -/
def pauliInterleave : PauliGroup × PauliGroup ≃* PauliGroup :=
  (MulEquiv.prodMultiplicative (G := PauliCoord × PauliCoord)
      (H := PauliCoord × PauliCoord)).symm.trans
    (AddEquiv.toMultiplicative
      ((AddEquiv.prodProdProdComm (M := PauliCoord) (N := PauliCoord) (M' := PauliCoord)
          (N' := PauliCoord)).trans
        (AddEquiv.prodCongr interleave interleave)))

theorem pauliInterleave_toAdd (a b : PauliGroup) :
    Multiplicative.toAdd (pauliInterleave (a, b)) =
      (interleave ((Multiplicative.toAdd a).1, (Multiplicative.toAdd b).1),
        interleave ((Multiplicative.toAdd a).2, (Multiplicative.toAdd b).2)) :=
  rfl

/-- **The interleaving carries the Pauli cocycle to the sum of the two cocycles.** -/
theorem pauliCocycle_interleave (a b c d : PauliGroup) :
    pauliCocycle (pauliInterleave (a, b)) (pauliInterleave (c, d)) =
      pauliCocycle a c + pauliCocycle b d := by
  simp only [pauliCocycle, pauliInterleave_toAdd]
  exact dot_interleave _ _ _ _

end

#audit_axioms pauliCocycle_isTwistedICC
#audit_axioms isIIOneFactor_hyperfiniteFactor
#audit_axioms pauliCocycle_interleave

end Hyperfinite
end GroupApproximation
