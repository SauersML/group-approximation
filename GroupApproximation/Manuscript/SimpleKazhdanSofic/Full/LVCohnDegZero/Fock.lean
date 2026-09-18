import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Words

/-!
# The Fock representation of the Cohn algebra `C₂(𝔽₂)`

The Cohn algebra acts on the space of functions `List Bool → 𝔽₂`.  Here `xᵢ` prepends the
letter `i` and `yᵢ` deletes it.  The vacuum `[]` is not in the range of any `xᵢ`, so the
projection `p = 1 - x₀y₀ - x₁y₁` acts nontrivially.  In particular `p ≠ 0` and `1 ≠ 0` in
`C₂(𝔽₂)`.  These are the nondegeneracy facts behind the matrix algebra decomposition of the
degree-zero part (Ara-Brustenga-Cortiñas 2009, Sec. 5; `simple_kazhdan_sofic_group.tex`
l.733-735, `sec:questions`, leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVCohnDegZero

open GroupApproximation.Full.LVCohnRelK1

noncomputable section

/-- The Fock space `List Bool → 𝔽₂` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
abbrev FockSpace : Type := List Bool → ZMod 2

/-- The creation operator `xᵢ`: `(xᵢ f)(i :: w) = f w`, and `xᵢ f` vanishes elsewhere. -/
def fockPrefix (i : Bool) : Module.End (ZMod 2) FockSpace where
  toFun f w := if w.head? = some i then f w.tail else 0
  map_add' _ _ := by
    funext w
    by_cases h : w.head? = some i <;> simp [h]
  map_smul' _ _ := by
    funext w
    by_cases h : w.head? = some i <;> simp [h]

/-- The annihilation operator `yᵢ`: `(yᵢ f)(w) = f (i :: w)`. -/
def fockDelete (i : Bool) : Module.End (ZMod 2) FockSpace where
  toFun f w := f (i :: w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fockDelete_mul_fockPrefix_same (i : Bool) : fockDelete i * fockPrefix i = 1 := by
  ext f w
  simp [fockDelete, fockPrefix]

theorem fockDelete_mul_fockPrefix_ne {i j : Bool} (hij : i ≠ j) :
    fockDelete i * fockPrefix j = 0 := by
  ext f w
  simp [fockDelete, fockPrefix, hij]

/-- The images of the four generators `s₀, s₁, t₀, t₁`. -/
def fockGen : BinaryLeavitt.Generator → Module.End (ZMod 2) FockSpace :=
  ![fockPrefix false, fockPrefix true, fockDelete false, fockDelete true]

/-- The free algebra evaluated in the Fock representation. -/
def fockEval : BinaryLeavitt.Free (ZMod 2) →ₐ[ZMod 2] Module.End (ZMod 2) FockSpace :=
  FreeAlgebra.lift (ZMod 2) fockGen

theorem fockEval_s0 :
    fockEval (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0) = fockPrefix false := by
  rw [fockEval, FreeAlgebra.lift_ι_apply]
  rfl

theorem fockEval_s1 :
    fockEval (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s1) = fockPrefix true := by
  rw [fockEval, FreeAlgebra.lift_ι_apply]
  rfl

theorem fockEval_t0 :
    fockEval (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0) = fockDelete false := by
  rw [fockEval, FreeAlgebra.lift_ι_apply]
  rfl

theorem fockEval_t1 :
    fockEval (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t1) = fockDelete true := by
  rw [fockEval, FreeAlgebra.lift_ι_apply]
  rfl

theorem fockEval_respects :
    ∀ ⦃a b : BinaryLeavitt.Free (ZMod 2)⦄, CohnRel a b → fockEval a = fockEval b := by
  intro a b h
  cases h with
  | t0_s0 =>
    rw [map_mul, map_one, fockEval_t0, fockEval_s0]
    exact fockDelete_mul_fockPrefix_same false
  | t0_s1 =>
    rw [map_mul, map_zero, fockEval_t0, fockEval_s1]
    exact fockDelete_mul_fockPrefix_ne (by decide)
  | t1_s0 =>
    rw [map_mul, map_zero, fockEval_t1, fockEval_s0]
    exact fockDelete_mul_fockPrefix_ne (by decide)
  | t1_s1 =>
    rw [map_mul, map_one, fockEval_t1, fockEval_s1]
    exact fockDelete_mul_fockPrefix_same true

/-- The Fock representation `C₂(𝔽₂) → End(List Bool → 𝔽₂)`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
def fockRep : CohnTwoF2 →ₐ[ZMod 2] Module.End (ZMod 2) FockSpace :=
  RingQuot.liftAlgHom (ZMod 2) ⟨fockEval, fockEval_respects⟩

theorem fockRep_cmk (a : BinaryLeavitt.Free (ZMod 2)) : fockRep (cmk a) = fockEval a :=
  RingQuot.liftAlgHom_mkAlgHom_apply (ZMod 2) fockEval fockEval_respects a

theorem fockRep_cx : ∀ i : Bool, fockRep (cx i) = fockPrefix i
  | false => by
    show fockRep (cmk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0)) = fockPrefix false
    rw [fockRep_cmk, fockEval_s0]
  | true => by
    show fockRep (cmk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s1)) = fockPrefix true
    rw [fockRep_cmk, fockEval_s1]

theorem fockRep_cy : ∀ i : Bool, fockRep (cy i) = fockDelete i
  | false => by
    show fockRep (cmk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0)) = fockDelete false
    rw [fockRep_cmk, fockEval_t0]
  | true => by
    show fockRep (cmk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t1)) = fockDelete true
    rw [fockRep_cmk, fockEval_t1]

/-- `p` fixes the vacuum: `(p f)([]) = f([])`. -/
theorem fockRep_cohnP_vacuum (f : FockSpace) : fockRep cohnP f [] = f [] := by
  rw [cohnP_def, map_sub, map_sub, map_one, map_mul, map_mul, fockRep_cx, fockRep_cx,
    fockRep_cy, fockRep_cy]
  simp [fockPrefix]

/-- `p ≠ 0` in `C₂(𝔽₂)` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem cohnP_ne_zero : cohnP ≠ 0 := by
  intro h
  have h1 := fockRep_cohnP_vacuum (fun _ => (1 : ZMod 2))
  rw [h, map_zero] at h1
  have h2 : (0 : ZMod 2) = 1 := h1
  exact absurd h2 (by decide)

/-- `1 ≠ 0` in `C₂(𝔽₂)`. -/
theorem cohn_one_ne_zero : (1 : CohnTwoF2) ≠ 0 := by
  intro h
  apply cohnP_ne_zero
  rw [← mul_one cohnP, h, mul_zero]

end

end GroupApproximation.Full.LVCohnDegZero
