import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Sofic.AmenableActionSofic
import GroupApproximation.Algebra.Amenable
import GroupApproximation.Algebra.AmenableInt
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.Fintype.EquivFin

/-!
# Elek--Szabó permanence: soficity passes to extensions with amenable quotient

The manuscript `non_mf_groups_exist.tex` invokes the Elek--Szabó
amenable-extension theorem (citation key `ElekSzabo`) at three places.  Line
numbers below are for the 4262-line copy and drift; the quoted strings are the
stable anchors.

*Proof of Theorem `thm:E`* (~3517--3530).  The displayed reassociation

> `W=\ClLamp(X)\rtimes(T\rtimes\mathbb Z) \cong (\ClLamp(X)\rtimes T)\rtimes\mathbb Z`

is followed by "The final group is sofic because a split extension of a sofic
group by `$\Z$` is sofic", a sketch of the `ZMod N` truncation, and then

> "This is the `$\Z$`-extension case of the Elek--Szab\'o amenable-extension
> theorem \cite{ElekSzabo}."

*Paragraph "Extensions by `$\Z$`"* (~3570--3579).  A surjection `W → ℤ` "whose
kernel is `$\ClLamp(X)\rtimes T$`", that kernel being LEF hence sofic, and then

> "Thus `W` is an extension of an LEF group by `$\Z$` and is not MF, while
> soficity is preserved by every extension with amenable quotient
> \cite{ElekSzabo}."

*Introduction* (~1201).  "the remaining `$\Z$`-extension is sofic by
Elek--Szab\'o \cite{ElekSzabo}".

**Direction.**  Both displayed shapes put the sofic group in the kernel and the
amenable group in the quotient: in `(\ClLamp(X)\rtimes T)\rtimes\Z` the sofic
base `\ClLamp(X)\rtimes T` is the kernel and `ℤ` the quotient, and in the
"Extensions by `$\Z$`" paragraph the kernel is `\ClLamp(X)\rtimes T` and the
quotient is `ℤ`.  So the theorem to prove is *sofic-by-amenable is sofic*, i.e.
sofic kernel and amenable quotient.  (The other displayed exact sequence in this
section, `1 → \ClLamp(X) → W → V → 1`, is about failure of *MF* permanence and is
**not** an instance of this theorem: its quotient `V` contains the infinite
Kazhdan group and is nonamenable.)

`Sofic/SoficIntegerExtension.lean` formalizes only the concrete split `ℤ` case.
This file proves the theorem the manuscript names: **every** extension

`1 → N → G → G ⧸ N → 1`

with `N` sofic and `G ⧸ N` amenable has `G` sofic.  No splitting is assumed, the
quotient is an arbitrary amenable group, and there is no countability premise.

## The proof

The argument is the Elek--Szabó one: combine a sofic approximation of the kernel
with a Følner tiling of the quotient.  It runs in the following named steps; the
declarations below carry the same names.

1. `sect` / `mk_sect` -- choose a set-theoretic section `s` of `G → G ⧸ N`.
2. `esCocycle_mem` -- the *displacement cocycle* `c(g,q) = s(ḡq)⁻¹ g s(q)` takes
   values in the kernel `N`.
3. `esCocycle_mul` -- the cocycle identity `c(gh,q) = c(g, h̄q) c(h,q)`, which is
   *exact*: unlike the `ℤ`-model of `SoficIntegerExtension`, no wrap-around
   defect appears here, because the quotient acts on itself honestly.
4. `esCocycle_injective_of_mk_eq` -- elements with the same image in the quotient
   have distinct cocycles at every level.
5. `transportPerm`, `fibrePerm`, `fibrePerm_mul` -- the induced permutations of
   `Y × Λ`, where `Y` is a finite model of `N` and `Λ` is a finite level set.
6. `hammingDistance_fibrePerm_le` -- the Hamming upper estimate: a fibred pair
   disagrees on at most the fibrewise disagreement plus the exceptional levels.
7. `hammingDistance_fibrePerm_ge_fibre` -- the fibrewise lower estimate.
8. `hammingDistance_fibrePerm_ge_level` -- the level lower estimate.
9. `isSofic_of_isSofic_of_isAmenable_quotient` -- the theorem.  The level set is
   a Følner set `A` of `G ⧸ N` for the window `{ḡ, ḡh̄ : g,h ∈ F}`, the level
   permutations are the completed left translations `folnerPerm`, the fibres
   carry a sofic model of `N` on the finite set of cocycle values over `A`, and
   the only defect is the Følner boundary, which the Følner condition makes as
   thin as desired.

The truncation defect of the `ℤ`-model becomes here the Følner boundary defect;
that is exactly the generalization the manuscript's sentence asserts.

Four corollaries package the theorem in the forms the manuscript uses:
`isSofic_of_isSofic_ker_of_isAmenable` (surjection with sofic kernel and
amenable target), `isSofic_semidirectProduct` (the split case),
`isSofic_int_semidirectProduct` (the manuscript's split `ℤ` case, recovering
`Sofic/SoficIntegerExtension.lean` from the general theorem exactly as the
manuscript says it should be recovered), and `isSofic_of_isSofic_of_int_quotient`
(the non-split `ℤ` case actually used in the "Extensions by `ℤ`" paragraph).
Amenability of `ℤ` is the repository's own `Algebra/AmenableInt.lean`.

The Følner sets themselves are *not* assumed: they are produced from the
repository's own invariant-mean definition of amenability by
`AmenableActionSofic.exists_folner`, which routes through the repository's
Tarski--Hall theorem.  There is no literature input anywhere in this file.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation

namespace SoficByAmenablePermanence

open Finset

/-! ## Transport of permutations along a bijection -/

/-- Transport a permutation along a bijection of the underlying types. -/
def transportPerm {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) : Equiv.Perm β :=
  e.symm.trans (σ.trans e)

@[simp] theorem transportPerm_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α)
    (b : β) : transportPerm e σ b = e (σ (e.symm b)) := rfl

/-- Transport is multiplicative. -/
theorem transportPerm_mul {α β : Type*} (e : α ≃ β) (σ τ : Equiv.Perm α) :
    transportPerm e (σ * τ) = transportPerm e σ * transportPerm e τ := by
  apply Equiv.ext
  intro b
  simp only [transportPerm_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

/-! ## Fibred permutations over a finite level set

Step 5 of the ledger.  These are the permutations of the induced model: a
level-indexed permutation of the fibre, followed by a permutation of the levels.
-/

section Fibre

variable {Y Λ : Type*}

/-- The permutation of `Y × Λ` that applies the level-indexed permutation `p` in
the fibre and moves the level by `α`. -/
def fibrePerm (p : Λ → Equiv.Perm Y) (α : Equiv.Perm Λ) : Equiv.Perm (Y × Λ) where
  toFun z := (p z.2 z.1, α z.2)
  invFun z := ((p (α.symm z.2)).symm z.1, α.symm z.2)
  left_inv z := by
    apply Prod.ext <;> simp
  right_inv z := by
    apply Prod.ext <;> simp

@[simp] theorem fibrePerm_apply (p : Λ → Equiv.Perm Y) (α : Equiv.Perm Λ)
    (z : Y × Λ) : fibrePerm p α z = (p z.2 z.1, α z.2) := rfl

/-- Fibred permutations compose to fibred permutations. -/
theorem fibrePerm_mul (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ) :
    fibrePerm p α * fibrePerm q β =
      fibrePerm (fun i ↦ p (β i) * q i) (α * β) := by
  apply Equiv.ext
  intro z
  apply Prod.ext
  · rfl
  · rfl

end Fibre

/-! ## Hamming estimates for fibred permutations

Steps 6--8 of the ledger.  Everything is derived from one identity: the
disagreement set of two fibred permutations splits over the levels, contributing
the fibrewise disagreement at the levels where the two level permutations agree
and the whole fibre where they do not.
-/

/-- The finite model on which the induced permutations act. -/
abbrev fibreModel (Y : FiniteModel) (Λ : Type) [Fintype Λ] [DecidableEq Λ] :
    FiniteModel :=
  ⟨Y × Λ, inferInstance, inferInstance⟩

theorem card_fibreModel (Y : FiniteModel) (Λ : Type) [Fintype Λ]
    [DecidableEq Λ] :
    Fintype.card (fibreModel Y Λ) = Fintype.card Y * Fintype.card Λ := by
  show Fintype.card (Y × Λ) = _
  rw [Fintype.card_prod]

theorem cast_card_fibreModel (Y : FiniteModel) (Λ : Type) [Fintype Λ]
    [DecidableEq Λ] :
    ((Fintype.card (fibreModel Y Λ) : ℕ) : ℝ)
      = (Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ) := by
  rw [card_fibreModel, Nat.cast_mul]

/-- The fibre of the disagreement set over a single level. -/
theorem disagreement_fibrePerm (Y : FiniteModel) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ) (i : Λ) :
    (hammingDisagreement (fibrePerm p α) (fibrePerm q β)).filter
        (fun z ↦ z.2 = i) =
      (if α i = β i then hammingDisagreement (p i) (q i)
        else (Finset.univ : Finset Y)).map
        ⟨fun y ↦ (y, i), fun _ _ e ↦ congrArg Prod.fst e⟩ := by
  by_cases hc : α i = β i
  · rw [if_pos hc]
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, mem_hammingDisagreement,
      fibrePerm_apply, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hz, rfl⟩
      refine ⟨z.1, ?_, rfl⟩
      intro hy
      exact hz (Prod.ext hy hc)
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun hz ↦ hy (congrArg Prod.fst hz), rfl⟩
  · rw [if_neg hc]
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, mem_hammingDisagreement,
      fibrePerm_apply, Function.Embedding.coeFn_mk, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hz, rfl⟩
      exact ⟨z.1, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨?_, rfl⟩
      intro hz
      exact hc (congrArg Prod.snd hz)

/-- The disagreement count of two fibred permutations splits over the levels. -/
theorem card_disagreement_fibrePerm (Y : FiniteModel) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ) :
    (hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card =
      ∑ i : Λ, (if α i = β i then (hammingDisagreement (p i) (q i)).card
        else Fintype.card Y) := by
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (s := hammingDisagreement (fibrePerm p α) (fibrePerm q β))
    (t := (Finset.univ : Finset Λ)) (g := Prod.snd)
  simp only [Finset.mem_univ, Finset.filter_true] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [disagreement_fibrePerm, Finset.card_map]
  by_cases hc : α i = β i
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, Finset.card_univ]

/-- **Step 6 (upper estimate).**  If `D` collects the levels at which the two
level permutations differ, and off `D` the fibres are `b`-close, then the two
fibred permutations are `b + |D|/|Λ|`-close. -/
theorem hammingDistance_fibrePerm_le (Y : FiniteModel) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (hY : 0 < Fintype.card Y) (hΛ : 0 < Fintype.card Λ)
    (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ) (D : Finset Λ)
    (hD : ∀ i, α i ≠ β i → i ∈ D) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ i, i ∉ D → hammingDistance Y (p i) (q i) ≤ b) :
    hammingDistance (fibreModel Y Λ) (fibrePerm p α) (fibrePerm q β) ≤
      b + (D.card : ℝ) / (Fintype.card Λ : ℝ) := by
  have hcY : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hcΛ : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  have hcΛ0 : (Fintype.card Λ : ℝ) ≠ 0 := hcΛ.ne'
  -- the level-by-level bound on the fibre counts
  have hterm : ∀ i : Λ,
      ((if α i = β i then (hammingDisagreement (p i) (q i)).card
        else Fintype.card Y : ℕ) : ℝ) ≤
      (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ)) := by
    intro i
    by_cases hi : i ∈ D
    · rw [if_pos hi]
      by_cases hc : α i = β i
      · rw [if_pos hc]
        have hle : (hammingDisagreement (p i) (q i)).card ≤ Fintype.card Y :=
          Finset.card_le_univ _
        exact_mod_cast hle
      · exact le_of_eq (by rw [if_neg hc])
    · rw [if_neg hi]
      have hc : α i = β i := by
        by_contra hcon
        exact hi (hD i hcon)
      rw [if_pos hc]
      have hdist := hb i hi
      rw [hammingDistance, div_le_iff₀ hcY] at hdist
      exact hdist
  -- summing over the levels
  have hsum : ((hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card : ℝ) ≤
      (D.card : ℝ) * (Fintype.card Y : ℝ) +
        (Fintype.card Λ : ℝ) * (b * (Fintype.card Y : ℝ)) := by
    have h1 : ((hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card : ℝ) =
        ∑ i : Λ, ((if α i = β i then (hammingDisagreement (p i) (q i)).card
          else Fintype.card Y : ℕ) : ℝ) := by
      rw [card_disagreement_fibrePerm, Nat.cast_sum]
    have e1 : ∀ i ∈ D,
        (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ))
          = (Fintype.card Y : ℝ) := fun i hi ↦ if_pos hi
    have e2 : ∀ i ∈ Dᶜ,
        (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ))
          = b * (Fintype.card Y : ℝ) :=
      fun i hi ↦ if_neg (Finset.mem_compl.mp hi)
    have hA : ∑ i ∈ D,
        (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ))
          = (D.card : ℝ) * (Fintype.card Y : ℝ) := by
      rw [Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ i ∈ Dᶜ,
        (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ))
          = (Dᶜ.card : ℝ) * (b * (Fintype.card Y : ℝ)) := by
      rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]
    have hDc : (Dᶜ.card : ℝ) ≤ (Fintype.card Λ : ℝ) := by
      exact_mod_cast Finset.card_le_univ Dᶜ
    have hnn : 0 ≤ b * (Fintype.card Y : ℝ) := mul_nonneg hb0 hcY.le
    rw [h1]
    calc ∑ i : Λ, ((if α i = β i then (hammingDisagreement (p i) (q i)).card
            else Fintype.card Y : ℕ) : ℝ)
        ≤ ∑ i : Λ,
            (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ)) :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ∑ i ∈ D,
            (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ)) +
          ∑ i ∈ Dᶜ,
            (if i ∈ D then (Fintype.card Y : ℝ) else b * (Fintype.card Y : ℝ)) :=
          (Finset.sum_add_sum_compl D _).symm
      _ = (D.card : ℝ) * (Fintype.card Y : ℝ) +
            (Dᶜ.card : ℝ) * (b * (Fintype.card Y : ℝ)) := by rw [hA, hB]
      _ ≤ (D.card : ℝ) * (Fintype.card Y : ℝ) +
            (Fintype.card Λ : ℝ) * (b * (Fintype.card Y : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_right hDc hnn
          linarith
  -- and dividing
  have hL : (D.card : ℝ) / (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ)
      = (D.card : ℝ) := by
    field_simp
  have hexpand : (b + (D.card : ℝ) / (Fintype.card Λ : ℝ)) *
      ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ))
      = (D.card : ℝ) * (Fintype.card Y : ℝ) +
        (Fintype.card Λ : ℝ) * (b * (Fintype.card Y : ℝ)) := by
    calc (b + (D.card : ℝ) / (Fintype.card Λ : ℝ)) *
          ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ))
        = b * ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ)) +
            ((D.card : ℝ) / (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ)) *
              (Fintype.card Y : ℝ) := by ring
      _ = b * ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ)) +
            (D.card : ℝ) * (Fintype.card Y : ℝ) := by rw [hL]
      _ = (D.card : ℝ) * (Fintype.card Y : ℝ) +
            (Fintype.card Λ : ℝ) * (b * (Fintype.card Y : ℝ)) := by ring
  rw [hammingDistance, cast_card_fibreModel, div_le_iff₀ (mul_pos hcY hcΛ),
    hexpand]
  exact hsum

/-- **Step 7 (fibrewise lower estimate).**  If every fibre is at Hamming
distance at least `c`, so are the fibred permutations, whatever the level
permutations do. -/
theorem hammingDistance_fibrePerm_ge_fibre (Y : FiniteModel) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] (hY : 0 < Fintype.card Y)
    (hΛ : 0 < Fintype.card Λ) (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ)
    (c : ℝ) (hc : ∀ i, c ≤ hammingDistance Y (p i) (q i)) :
    c ≤ hammingDistance (fibreModel Y Λ) (fibrePerm p α) (fibrePerm q β) := by
  have hcY : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hcΛ : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  obtain ⟨i₀⟩ : Nonempty Λ := Fintype.card_pos_iff.mp hΛ
  have hc1 : c ≤ 1 := le_trans (hc i₀) (hammingDistance_le_one Y (p i₀) (q i₀))
  have hterm : ∀ i : Λ, c * (Fintype.card Y : ℝ) ≤
      ((if α i = β i then (hammingDisagreement (p i) (q i)).card
        else Fintype.card Y : ℕ) : ℝ) := by
    intro i
    by_cases hci : α i = β i
    · rw [if_pos hci]
      have hd := hc i
      rw [hammingDistance, le_div_iff₀ hcY] at hd
      exact hd
    · rw [if_neg hci]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hcY.le]
  have hsum : (Fintype.card Λ : ℝ) * (c * (Fintype.card Y : ℝ)) ≤
      ((hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card : ℝ) := by
    have h1 : ((hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card : ℝ) =
        ∑ i : Λ, ((if α i = β i then (hammingDisagreement (p i) (q i)).card
          else Fintype.card Y : ℕ) : ℝ) := by
      rw [card_disagreement_fibrePerm, Nat.cast_sum]
    rw [h1]
    calc (Fintype.card Λ : ℝ) * (c * (Fintype.card Y : ℝ))
        = ∑ _i : Λ, c * (Fintype.card Y : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ ∑ i : Λ, ((if α i = β i then (hammingDisagreement (p i) (q i)).card
            else Fintype.card Y : ℕ) : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ hterm i
  rw [hammingDistance, cast_card_fibreModel, le_div_iff₀ (mul_pos hcY hcΛ)]
  calc c * ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ))
      = (Fintype.card Λ : ℝ) * (c * (Fintype.card Y : ℝ)) := by ring
    _ ≤ _ := hsum

/-- **Step 8 (level lower estimate).**  Every level at which the two level
permutations differ contributes its whole fibre to the disagreement. -/
theorem hammingDistance_fibrePerm_ge_level (Y : FiniteModel) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] (hY : 0 < Fintype.card Y)
    (hΛ : 0 < Fintype.card Λ) (p q : Λ → Equiv.Perm Y) (α β : Equiv.Perm Λ)
    (D : Finset Λ) (hD : ∀ i ∈ D, α i ≠ β i) :
    (D.card : ℝ) / (Fintype.card Λ : ℝ) ≤
      hammingDistance (fibreModel Y Λ) (fibrePerm p α) (fibrePerm q β) := by
  have hcY : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hcΛ : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  have hcΛ0 : (Fintype.card Λ : ℝ) ≠ 0 := hcΛ.ne'
  have hnat : D.card * Fintype.card Y ≤
      (hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card := by
    rw [card_disagreement_fibrePerm]
    calc D.card * Fintype.card Y
        = ∑ _i ∈ D, Fintype.card Y := (Finset.sum_const_nat fun _ _ ↦ rfl).symm
      _ = ∑ i ∈ D, (if α i = β i then (hammingDisagreement (p i) (q i)).card
            else Fintype.card Y) :=
          Finset.sum_congr rfl fun i hi ↦ (if_neg (hD i hi)).symm
      _ ≤ ∑ i : Λ, (if α i = β i then (hammingDisagreement (p i) (q i)).card
            else Fintype.card Y) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ D)
  have hL : (D.card : ℝ) / (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ)
      = (D.card : ℝ) := by
    field_simp
  rw [hammingDistance, cast_card_fibreModel, le_div_iff₀ (mul_pos hcY hcΛ)]
  calc (D.card : ℝ) / (Fintype.card Λ : ℝ) *
        ((Fintype.card Y : ℝ) * (Fintype.card Λ : ℝ))
      = ((D.card : ℝ) / (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ)) *
          (Fintype.card Y : ℝ) := by ring
    _ = (D.card : ℝ) * (Fintype.card Y : ℝ) := by rw [hL]
    _ ≤ ((hammingDisagreement (fibrePerm p α) (fibrePerm q β)).card : ℝ) := by
        exact_mod_cast hnat

/-! ## The displacement cocycle of an extension

Steps 1--4 of the ledger.
-/

section Cocycle

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- **Step 1.**  A set-theoretic section of the quotient map, chosen once. -/
noncomputable def sect (q : G ⧸ N) : G :=
  Function.surjInv (QuotientGroup.mk_surjective (s := N)) q

omit [N.Normal] in
@[simp] theorem mk_sect (q : G ⧸ N) :
    (QuotientGroup.mk (sect N q) : G ⧸ N) = q :=
  Function.surjInv_eq (QuotientGroup.mk_surjective (s := N)) q

/-- The Elek--Szabó displacement cocycle `c(g,q) = s(ḡq)⁻¹ g s(q)`. -/
noncomputable def esCocycle (g : G) (q : G ⧸ N) : G :=
  (sect N ((QuotientGroup.mk g : G ⧸ N) * q))⁻¹ * g * sect N q

/-- **Step 2.**  The displacement cocycle takes values in the kernel. -/
theorem esCocycle_mem (g : G) (q : G ⧸ N) : esCocycle N g q ∈ N := by
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have hval : (QuotientGroup.mk (esCocycle N g q) : G ⧸ N)
      = ((QuotientGroup.mk g : G ⧸ N) * q)⁻¹ * (QuotientGroup.mk g : G ⧸ N) * q := by
    simp only [esCocycle, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_sect]
  rw [hval]
  group

/-- **Step 3 (cocycle identity).**  `c(gh,q) = c(g, h̄q) · c(h,q)`, exactly.

This is the point at which the general argument is *cleaner* than the
`ℤ`-truncation of `Sofic/SoficIntegerExtension.lean`: there the analogous
identity failed on a wrap-around boundary, here it holds identically and the
whole defect is pushed into the Følner boundary of the level set. -/
theorem esCocycle_mul (g h : G) (q : G ⧸ N) :
    esCocycle N (g * h) q =
      esCocycle N g ((QuotientGroup.mk h : G ⧸ N) * q) * esCocycle N h q := by
  have hq : ((QuotientGroup.mk (g * h) : G ⧸ N) * q)
      = (QuotientGroup.mk g : G ⧸ N) * ((QuotientGroup.mk h : G ⧸ N) * q) := by
    rw [QuotientGroup.mk_mul, mul_assoc]
  simp only [esCocycle, hq]
  group

/-- **Step 4.**  Two elements with the same image in the quotient have distinct
cocycles at every level. -/
theorem esCocycle_injective_of_mk_eq {g h : G} (q : G ⧸ N)
    (hgh : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h)
    (hc : esCocycle N g q = esCocycle N h q) : g = h := by
  simp only [esCocycle, hgh] at hc
  exact mul_left_cancel (mul_right_cancel hc)

/-- The displacement cocycle, valued in the kernel subgroup. -/
noncomputable def esCocycleN (g : G) (q : G ⧸ N) : N :=
  ⟨esCocycle N g q, esCocycle_mem N g q⟩

theorem esCocycleN_mul (g h : G) (q : G ⧸ N) :
    esCocycleN N (g * h) q =
      esCocycleN N g ((QuotientGroup.mk h : G ⧸ N) * q) * esCocycleN N h q :=
  Subtype.ext (esCocycle_mul N g h q)

theorem esCocycleN_injective_of_mk_eq {g h : G} (q : G ⧸ N)
    (hgh : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h)
    (hc : esCocycleN N g q = esCocycleN N h q) : g = h :=
  esCocycle_injective_of_mk_eq N q hgh (congrArg Subtype.val hc)

end Cocycle

/-! ## The permanence theorem -/

/-- **Step 9 -- Elek--Szabó permanence, the theorem the manuscript names at
"This is the `ℤ`-extension case of the Elek--Szabó amenable-extension theorem"
and applies at "soficity is preserved by every extension with amenable
quotient".**  Soficity is preserved by every extension with amenable quotient:
if `N` is a normal subgroup of `G` which is sofic, and the quotient `G ⧸ N` is
amenable, then `G` is sofic.

The proof is the Elek--Szabó one.  Given a finite window `F ⊆ G` and an accuracy
`ε > 0`:

* a Følner set `A` of `G ⧸ N` is chosen for the finite family of translations
  `{ḡ, ḡh̄ : g,h ∈ F}` and boundary parameter `ε/8`;
* the level set is `A`, transported to a type in `Type` so that it can carry a
  `FiniteModel`, and the level permutations are the completed left translations
  `AmenableActionSofic.folnerPerm`;
* the fibres carry a sofic model of `N` on the finite set of cocycle values
  `{c(g,a) : g ∈ F, a ∈ A}` with accuracy `ε/2`;
* multiplicativity is exact except on the Følner boundary, whose relative size
  is below `ε/2` by the choice of `A`;
* separation splits according to whether the two elements have equal image in
  the quotient: if they do, the fibres separate them through the cocycle; if
  they do not, the levels separate them off the Følner boundary.

No countability premise, no splitting hypothesis, and no literature input. -/
theorem isSofic_of_isSofic_of_isAmenable_quotient {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsSofic N)
    (hQ : Amenability.IsAmenable (G ⧸ N)) : IsSofic G := by
  classical
  intro F ε hε
  -- the finite family of quotient translations that must be tested
  set FQ : Finset (G ⧸ N) := F.image (fun g ↦ (QuotientGroup.mk g : G ⧸ N))
  set TQ : Finset (G ⧸ N) := FQ ∪ (FQ ×ˢ FQ).image (fun p ↦ p.1 * p.2)
  have hmemTQ : ∀ g ∈ F, (QuotientGroup.mk g : G ⧸ N) ∈ TQ := by
    intro g hg
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)
  have hmemTQ2 : ∀ g ∈ F, ∀ h ∈ F,
      (QuotientGroup.mk g : G ⧸ N) * (QuotientGroup.mk h : G ⧸ N) ∈ TQ := by
    intro g hg h hh
    refine Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨((QuotientGroup.mk g : G ⧸ N), (QuotientGroup.mk h : G ⧸ N)), ?_, rfl⟩)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hg, Finset.mem_image_of_mem _ hh⟩
  -- a Følner set for that family
  have hδ : (0 : ℝ) < ε / 8 := by linarith
  obtain ⟨A, hAne, hsmall⟩ := AmenableActionSofic.exists_folner hQ TQ hδ
  have hAcard : 0 < A.card := Finset.card_pos.mpr hAne
  have hAnn : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  -- the level set, transported to a type in `Type`
  obtain ⟨n, ⟨e⟩⟩ : ∃ m : ℕ, Nonempty (↥A ≃ Fin m) :=
    ⟨Fintype.card ↥A, ⟨Fintype.equivFin ↥A⟩⟩
  have hnA : n = A.card := by
    have h1 : Fintype.card ↥A = Fintype.card (Fin n) := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe] at h1
    exact h1.symm
  have hcΛnat : Fintype.card (Fin n) = A.card := by rw [Fintype.card_fin, hnA]
  have hnΛ : 0 < Fintype.card (Fin n) := by rw [hcΛnat]; exact hAcard
  have hcΛR : (0 : ℝ) < ((Fintype.card (Fin n) : ℕ) : ℝ) := by exact_mod_cast hnΛ
  have hcΛA : ((Fintype.card (Fin n) : ℕ) : ℝ) = (A.card : ℝ) := by rw [hcΛnat]
  -- the level embedding and the completed level translations
  set lvl : Fin n → G ⧸ N := fun i ↦ ((e.symm i : ↥A) : G ⧸ N) with hlvl
  have hlvlA : ∀ i : Fin n, lvl i ∈ A := by
    intro i
    simp only [hlvl]
    exact (e.symm i).2
  have hlvlInj : Function.Injective lvl := by
    intro i j hij
    simp only [hlvl] at hij
    exact e.symm.injective (Subtype.ext hij)
  set lp : G → Equiv.Perm (Fin n) :=
    fun g ↦ transportPerm e
      (AmenableActionSofic.folnerPerm A (QuotientGroup.mk g)) with hlp
  have hagree : ∀ (g : G) (i : Fin n),
      (QuotientGroup.mk g : G ⧸ N) * lvl i ∈ A →
      lvl (lp g i) = (QuotientGroup.mk g : G ⧸ N) * lvl i := by
    intro g i hmem
    have hmem' : (QuotientGroup.mk g : G ⧸ N) * ((e.symm i : ↥A) : G ⧸ N) ∈ A := by
      simpa only [hlvl] using hmem
    have hfp := AmenableActionSofic.folnerPerm_agrees A (QuotientGroup.mk g)
      (e.symm i) hmem'
    simp only [hlvl, hlp, transportPerm_apply, Equiv.symm_apply_apply]
    exact hfp
  -- the levels that a translation pushes out of the Følner set
  set esc : (G ⧸ N) → Finset (Fin n) :=
    fun q ↦ Finset.univ.filter (fun i ↦ q * lvl i ∉ A) with hesc
  have hmem_esc : ∀ (q : G ⧸ N) (i : Fin n), i ∈ esc q ↔ q * lvl i ∉ A := by
    intro q i
    simp only [hesc, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbnd : ∀ q ∈ TQ, ((esc q).card : ℝ) < (ε / 8) * (A.card : ℝ) := by
    intro q hq
    refine lt_of_le_of_lt ?_ (hsmall q hq)
    have hle : (esc q).card ≤ (AmenableActionSofic.boundary A q).card := by
      apply Finset.card_le_card_of_injOn lvl
      · intro i hi
        exact AmenableActionSofic.mem_boundary.mpr
          ⟨hlvlA i, (hmem_esc q i).mp hi⟩
      · intro a _ b _ hab
        exact hlvlInj hab
    exact_mod_cast hle
  -- the finite set of cocycle values tested in the kernel
  set T : Finset ↥N := (F ×ˢ A).image (fun p ↦ esCocycleN N p.1 p.2)
  have hmemT : ∀ g ∈ F, ∀ i : Fin n, esCocycleN N g (lvl i) ∈ T := by
    intro g hg i
    refine Finset.mem_image.mpr ⟨(g, lvl i), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hg, hlvlA i⟩
  obtain ⟨M⟩ := hN T (ε / 2) (by linarith)
  -- the induced model
  set P : G → Fin n → Equiv.Perm M.carrier :=
    fun g i ↦ M.map (esCocycleN N g (lvl i)) with hP
  set Θ : G → Equiv.Perm (fibreModel M.carrier (Fin n)) :=
    fun g ↦ fibrePerm (P g) (lp g) with hΘ
  refine ⟨{
    carrier := fibreModel M.carrier (Fin n)
    nonempty := ?_
    map := Θ
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [card_fibreModel]
    exact Nat.mul_pos M.nonempty hnΛ
  · -- multiplicativity: exact off the Følner boundary
    intro g hg h hh
    set BAD : Finset (Fin n) :=
      esc (QuotientGroup.mk h) ∪
        esc ((QuotientGroup.mk g : G ⧸ N) * (QuotientGroup.mk h : G ⧸ N))
      with hBAD
    have hBADcard : (BAD.card : ℝ) < 2 * ((ε / 8) * (A.card : ℝ)) := by
      have hb1 := hbnd _ (hmemTQ h hh)
      have hb2 := hbnd _ (hmemTQ2 g hg h hh)
      have hle : BAD.card ≤ (esc (QuotientGroup.mk h)).card +
          (esc ((QuotientGroup.mk g : G ⧸ N) *
            (QuotientGroup.mk h : G ⧸ N))).card := by
        rw [hBAD]
        exact Finset.card_union_le _ _
      have hleR : (BAD.card : ℝ) ≤ ((esc (QuotientGroup.mk h)).card : ℝ) +
          ((esc ((QuotientGroup.mk g : G ⧸ N) *
            (QuotientGroup.mk h : G ⧸ N))).card : ℝ) := by
        exact_mod_cast hle
      linarith
    have hnotBAD1 : ∀ i : Fin n, i ∉ BAD →
        (QuotientGroup.mk h : G ⧸ N) * lvl i ∈ A := by
      intro i hi
      by_contra hc
      exact hi (by rw [hBAD]; exact Finset.mem_union_left _ ((hmem_esc _ i).mpr hc))
    have hnotBAD2 : ∀ i : Fin n, i ∉ BAD →
        ((QuotientGroup.mk g : G ⧸ N) * (QuotientGroup.mk h : G ⧸ N)) * lvl i
          ∈ A := by
      intro i hi
      by_contra hc
      exact hi (by rw [hBAD]; exact Finset.mem_union_right _ ((hmem_esc _ i).mpr hc))
    -- the level permutations agree off the boundary
    have hDlev : ∀ i : Fin n, lp (g * h) i ≠ (lp g * lp h) i → i ∈ BAD := by
      intro i hlev
      by_contra hi
      apply hlev
      have h1 := hnotBAD1 i hi
      have h2 := hnotBAD2 i hi
      have hmk : (QuotientGroup.mk (g * h) : G ⧸ N)
          = (QuotientGroup.mk g : G ⧸ N) * (QuotientGroup.mk h : G ⧸ N) :=
        QuotientGroup.mk_mul N g h
      have e1 : lvl (lp h i) = (QuotientGroup.mk h : G ⧸ N) * lvl i :=
        hagree h i h1
      have e2 : (QuotientGroup.mk g : G ⧸ N) * lvl (lp h i) ∈ A := by
        rw [e1, ← mul_assoc]
        exact h2
      have e3 : lvl (lp g (lp h i))
          = (QuotientGroup.mk g : G ⧸ N) * lvl (lp h i) := hagree g (lp h i) e2
      have e4 : (QuotientGroup.mk (g * h) : G ⧸ N) * lvl i ∈ A := by
        rw [hmk]; exact h2
      have e5 : lvl (lp (g * h) i)
          = (QuotientGroup.mk (g * h) : G ⧸ N) * lvl i := hagree (g * h) i e4
      apply hlvlInj
      rw [e5, hmk, Equiv.Perm.mul_apply, e3, e1, ← mul_assoc]
    -- the fibres are `ε/2`-multiplicative off the boundary
    have hbfib : ∀ i : Fin n, i ∉ BAD →
        hammingDistance M.carrier (P (g * h) i) (P g (lp h i) * P h i)
          ≤ ε / 2 := by
      intro i hi
      have h1 := hnotBAD1 i hi
      have e1 : lvl (lp h i) = (QuotientGroup.mk h : G ⧸ N) * lvl i :=
        hagree h i h1
      have hcoc : esCocycleN N (g * h) (lvl i)
          = esCocycleN N g (lvl (lp h i)) * esCocycleN N h (lvl i) := by
        rw [e1]
        exact esCocycleN_mul N g h (lvl i)
      simp only [hP]
      rw [hcoc]
      exact M.multiplicative _ (hmemT g hg (lp h i)) _ (hmemT h hh i)
    simp only [hΘ]
    rw [fibrePerm_mul]
    refine le_trans (hammingDistance_fibrePerm_le M.carrier M.nonempty hnΛ
      (P (g * h)) (fun i ↦ P g (lp h i) * P h i) (lp (g * h)) (lp g * lp h)
      BAD hDlev (ε / 2) (by linarith) hbfib) ?_
    have hfrac : (BAD.card : ℝ) / ((Fintype.card (Fin n) : ℕ) : ℝ) ≤ ε / 2 := by
      rw [div_le_iff₀ hcΛR, hcΛA]
      nlinarith [hBADcard, mul_nonneg hε.le hAnn]
    linarith
  · -- separation
    intro g hg h hh hne
    by_cases hqeq : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h
    · -- equal images: the fibres separate through the cocycle
      have hfib : ∀ i : Fin n,
          1 - ε / 2 ≤ hammingDistance M.carrier (P g i) (P h i) := by
        intro i
        simp only [hP]
        refine M.separated _ (hmemT g hg i) _ (hmemT h hh i) ?_
        intro heq
        exact hne (esCocycleN_injective_of_mk_eq N (lvl i) hqeq heq)
      simp only [hΘ]
      have hlow := hammingDistance_fibrePerm_ge_fibre M.carrier M.nonempty hnΛ
        (P g) (P h) (lp g) (lp h) (1 - ε / 2) hfib
      linarith
    · -- distinct images: the levels separate off the Følner boundary
      set GOOD : Finset (Fin n) :=
        (esc (QuotientGroup.mk g) ∪ esc (QuotientGroup.mk h))ᶜ with hGOOD
      have hGOODmem : ∀ i : Fin n, i ∈ GOOD →
          (QuotientGroup.mk g : G ⧸ N) * lvl i ∈ A ∧
            (QuotientGroup.mk h : G ⧸ N) * lvl i ∈ A := by
        intro i hi
        rw [hGOOD, Finset.mem_compl, Finset.mem_union] at hi
        constructor
        · by_contra hc
          exact hi (Or.inl ((hmem_esc _ i).mpr hc))
        · by_contra hc
          exact hi (Or.inr ((hmem_esc _ i).mpr hc))
      have hGOODne : ∀ i ∈ GOOD, lp g i ≠ lp h i := by
        intro i hi hEq
        obtain ⟨h1, h2⟩ := hGOODmem i hi
        have e1 : lvl (lp g i) = (QuotientGroup.mk g : G ⧸ N) * lvl i :=
          hagree g i h1
        have e2 : lvl (lp h i) = (QuotientGroup.mk h : G ⧸ N) * lvl i :=
          hagree h i h2
        apply hqeq
        have hmulEq : (QuotientGroup.mk g : G ⧸ N) * lvl i
            = (QuotientGroup.mk h : G ⧸ N) * lvl i := by
          rw [← e1, ← e2, hEq]
        exact mul_right_cancel hmulEq
      have hcov : Fintype.card (Fin n) ≤
          (esc (QuotientGroup.mk g)).card + (esc (QuotientGroup.mk h)).card +
            GOOD.card := by
        have h1 := Finset.card_add_card_compl
          (esc (QuotientGroup.mk g) ∪ esc (QuotientGroup.mk h))
        have h2 := Finset.card_union_le (esc (QuotientGroup.mk g))
          (esc (QuotientGroup.mk h))
        rw [hGOOD]
        omega
      have hGOODcard : (1 - ε) * ((Fintype.card (Fin n) : ℕ) : ℝ)
          ≤ (GOOD.card : ℝ) := by
        have hb1 := hbnd _ (hmemTQ g hg)
        have hb2 := hbnd _ (hmemTQ h hh)
        have hcovR : ((Fintype.card (Fin n) : ℕ) : ℝ) ≤
            ((esc (QuotientGroup.mk g)).card : ℝ) +
              ((esc (QuotientGroup.mk h)).card : ℝ) + (GOOD.card : ℝ) := by
          exact_mod_cast hcov
        rw [hcΛA] at hcovR ⊢
        nlinarith [hb1, hb2, hcovR, mul_nonneg hε.le hAnn]
      simp only [hΘ]
      have hlow := hammingDistance_fibrePerm_ge_level M.carrier M.nonempty hnΛ
        (P g) (P h) (lp g) (lp h) GOOD hGOODne
      refine le_trans ?_ hlow
      rw [le_div_iff₀ hcΛR]
      exact hGOODcard

/-! ## Packaged forms -/

/-- Amenability transports along a group isomorphism. -/
theorem isAmenable_of_mulEquiv {H K : Type*} [Group H] [Group K] (φ : H ≃* K)
    (hK : Amenability.IsAmenable K) : Amenability.IsAmenable H := by
  obtain ⟨m⟩ := hK
  refine ⟨{ measure := fun A ↦ m.measure (φ '' A)
            nonneg := fun A ↦ m.nonneg _
            measure_univ := ?_
            additive := ?_
            invariant := ?_ }⟩
  · have himg : (φ '' (Set.univ : Set H)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      obtain ⟨x, hx⟩ := φ.surjective y
      exact ⟨x, Set.mem_univ x, hx⟩
    rw [himg, m.measure_univ]
  · intro A B hAB
    rw [Set.image_union]
    refine m.additive _ _ ?_
    rw [Set.disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hb'⟩
    have hab : b = a := φ.injective hb'
    exact (Set.disjoint_left.mp hAB) ha (hab ▸ hb)
  · intro g A
    have himg : (φ : H → K) '' ((fun x ↦ g * x) '' A)
        = (fun y ↦ φ g * y) '' ((φ : H → K) '' A) := by
      ext y
      constructor
      · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨φ a, ⟨a, ha, rfl⟩, by simp [map_mul]⟩
      · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [map_mul]⟩
    rw [himg, m.invariant]

/-- **Elek--Szabó permanence, homomorphism form.**  A group with a sofic kernel
mapping onto an amenable group is sofic. -/
theorem isSofic_of_isSofic_ker_of_isAmenable {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (hker : IsSofic f.ker)
    (hQ : Amenability.IsAmenable Q) : IsSofic G :=
  isSofic_of_isSofic_of_isAmenable_quotient f.ker hker
    (isAmenable_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf) hQ)

/-- **Closed-header form.**  Both groups, the surjection and its two
hypotheses are quantified inside the proposition, so the printed header states
on its own face what a caller supplies.  The manuscript cites this form. -/
theorem manuscriptSoficOfSoficKerOfAmenableQuotient :
    ∀ {G Q : Type} [Group G] [Group Q] (f : G →* Q),
      Function.Surjective f → IsSofic f.ker →
      Amenability.IsAmenable Q → IsSofic G := by
  intro G Q _ _ f hf hker hQ
  exact isSofic_of_isSofic_ker_of_isAmenable f hf hker hQ


/-- **Elek--Szabó permanence, split form.**  A semidirect product of a sofic
group by an amenable group is sofic.  This is the generality that the
manuscript's sentence "a split extension of a sofic group by `$\Z$` is sofic"
sits inside. -/
theorem isSofic_semidirectProduct {K L : Type*} [Group K] [Group L]
    (φ : L →* MulAut K) (hK : IsSofic K) (hL : Amenability.IsAmenable L) :
    IsSofic (K ⋊[φ] L) := by
  have e : K ≃* (SemidirectProduct.rightHom (φ := φ)).ker :=
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).trans
      (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)
  have hker : IsSofic (SemidirectProduct.rightHom (φ := φ)).ker :=
    (isSofic_mulEquiv_iff e).mp hK
  exact isSofic_of_isSofic_ker_of_isAmenable SemidirectProduct.rightHom
    SemidirectProduct.rightHom_surjective hker hL

/-- `ℤ` is amenable, in the measure sense used by `exists_folner`.  This is the
repository's own Cesàro-average mean of `Algebra/AmenableInt.lean`, not a
literature input. -/
theorem isAmenable_int : Amenability.IsAmenable (Multiplicative ℤ) :=
  Amenability.isAmenable_of_hasInvariantMean Amenability.hasInvariantMean_int

/-- **The manuscript's `ℤ`-extension sentence as a special case.**  A split
extension of a sofic group by `ℤ` is sofic; this is the shape of the displayed
reassociation `W ≅ (\ClLamp(X) ⋊ T) ⋊ ℤ` in the proof of Theorem `thm:E`.

`Sofic/SoficIntegerExtension.lean` proves this directly, by truncating the level
set `ℤ` to `ZMod L` and controlling the wrap-around boundary.  The manuscript
says that this "is the `$\Z$`-extension case of the Elek--Szabó
amenable-extension theorem"; this declaration is that derivation. -/
theorem isSofic_int_semidirectProduct {K : Type*} [Group K]
    (φ : Multiplicative ℤ →* MulAut K) (hK : IsSofic K) :
    IsSofic (K ⋊[φ] Multiplicative ℤ) :=
  isSofic_semidirectProduct φ hK isAmenable_int

/-- **The manuscript's non-split `ℤ`-extension shape.**  A group with a sofic
normal subgroup and quotient isomorphic to `ℤ` is sofic.  This is the form used
in the paragraph "Extensions by `$\Z$`" -- the surjection `W → ℤ` "whose kernel
is `\ClLamp(X) ⋊ T`" -- where the extension is not presented as a split one. -/
theorem isSofic_of_isSofic_of_int_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hN : IsSofic N) (h : G ⧸ N ≃* Multiplicative ℤ) : IsSofic G :=
  isSofic_of_isSofic_of_isAmenable_quotient N hN
    (isAmenable_of_mulEquiv h isAmenable_int)

end SoficByAmenablePermanence

end GroupApproximation
