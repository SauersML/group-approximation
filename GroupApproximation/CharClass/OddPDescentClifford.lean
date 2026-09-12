import GroupApproximation.CharClass.OddPDescentWord

/-!
# The two relations that generate the descent

Everything the degree-one descent needs about `E^{⊗p}` follows from two identities
between the elementary operators of `OddPDescentWord.lean`:

```text
    eWedge a ∘ eWedge b  +  eWedge b ∘ eWedge a  =  0            (anticommutation)
    ePart  a ∘ eWedge b  +  eWedge b ∘ ePart  a  =  δ_{a b}      (the CAR relation)
```

In the exterior reading these are `ξ_a ∧ ξ_b = − ξ_b ∧ ξ_a` and `∂_a(ξ_b ∧ x) =
δ_{ab}·x − ξ_b ∧ ∂_a x`, the derivation property of a partial derivative.  From the first,
`eD ∘ eD = 0`; from the second with `b` summed, `eD ∘ eH + eH ∘ eD = 1` **on the nose, with
no `ηε` term**, which is `sp-design`'s observation that `E` is exact so the one-slot
contraction is a full one.

## Where the work is

Both proofs are a three-way split on the order of `a` and `b` inside three cases on the
letters in those slots, and in every branch the two words agree by `Function.update_comm`
while the two signs differ by exactly one, because the prefix at the *later* slot has moved
by one and the prefix at the *earlier* slot has not.  That asymmetry is the whole
cancellation and it is `OddPDescentWord.ePre_update_of_le` against
`ePre_update_of_lt`.  At `p = 2` the same statement is invisible — `CartanFreeCx`'s
corresponding step cancels because two is zero, a different mechanism reaching the same
conclusion — so a port of the mod-2 proof by changing the coefficient ring gives a false
theorem (`OddPTupleSign.lean` records the same trap for the tuple differential).
-/

namespace GroupApproximation.CharClass

variable {p : ℕ} (K : Type) [CommRing K]

/-! ## 1. Squares -/

/-- Inserting `g` twice in the same slot is `0`. -/
theorem eWedge_eWedge_self (a : Fin p) :
    (eWedge K a).comp (eWedge K a) = 0 := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, eWedge_single]
  by_cases h : w a = true
  · rw [eWedgeGen_of_true K h, map_zero]
  · rw [eWedgeGen_of_false K (Bool.eq_false_of_not_eq_true h), eWedge_smul_single,
      eWedgeGen_of_true K (by simp), smul_zero]

/-- Deleting the `g` of one slot twice is `0`. -/
theorem ePart_ePart_self (a : Fin p) :
    (ePart K a).comp (ePart K a) = 0 := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ePart_single]
  by_cases h : w a = true
  · rw [ePartGen_of_true K h, ePart_smul_single, ePartGen_of_false K (by simp), smul_zero]
  · rw [ePartGen_of_false K (Bool.eq_false_of_not_eq_true h), map_zero]

/-! ## 2. Anticommutation -/

/-- The one-sided computation for `a < b`, both slots holding `f`. -/
private theorem eWedge_comp_lt (a b : Fin p) (hab : a < b) (w : EWord p)
    (hwa : w a = false) (hwb : w b = false) :
    eWedge K a (eWedgeGen K b w)
      = ((-1 : K) ^ (ePre w b + ePre w a)) •
          Finsupp.single (Function.update (Function.update w b true) a true) (1 : K) := by
  have hne : a ≠ b := ne_of_lt hab
  have hpre : ePre (Function.update w b true) a = ePre w a :=
    ePre_update_of_le w b true a (le_of_lt hab)
  rw [eWedgeGen_of_false K hwb, eWedge_smul_single,
    eWedgeGen_of_false K (by rw [Function.update_of_ne hne]; exact hwa), hpre,
    eSign_smul_smul]

/-- **Anticommutation.** -/
theorem eWedge_anticomm (a b : Fin p) :
    (eWedge K a).comp (eWedge K b) + (eWedge K b).comp (eWedge K a) = 0 := by
  -- the statement is symmetric in `a` and `b`, so one strict order is enough
  have key : ∀ a b : Fin p, a < b →
      (eWedge K a).comp (eWedge K b) + (eWedge K b).comp (eWedge K a) = 0 := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    refine eMod_ext K fun w => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, eWedge_single]
    by_cases hwa : w a = true
    · rw [eWedgeGen_of_true K hwa, map_zero, add_zero]
      by_cases hwb : w b = true
      · rw [eWedgeGen_of_true K hwb, map_zero]
      · rw [eWedgeGen_of_false K (Bool.eq_false_of_not_eq_true hwb), eWedge_smul_single,
          eWedgeGen_of_true K (by rw [Function.update_of_ne hne]; exact hwa), smul_zero]
    by_cases hwb : w b = true
    · rw [eWedgeGen_of_true K hwb, map_zero, zero_add,
        eWedgeGen_of_false K (Bool.eq_false_of_not_eq_true hwa), eWedge_smul_single,
        eWedgeGen_of_true K (by rw [Function.update_of_ne hne.symm]; exact hwb), smul_zero]
    have hwa' : w a = false := Bool.eq_false_of_not_eq_true hwa
    have hwb' : w b = false := Bool.eq_false_of_not_eq_true hwb
    -- the second composite, computed the same way but with the *later* prefix moved
    have hpre2 : ePre (Function.update w a true) b = ePre w b + 1 := by
      have := ePre_update_of_lt w a true b hab
      rw [hwa'] at this
      simpa using this
    have hsnd : eWedge K b (eWedgeGen K a w)
        = ((-1 : K) ^ (ePre w a + ePre w b + 1)) •
            Finsupp.single (Function.update (Function.update w b true) a true) (1 : K) := by
      rw [eWedgeGen_of_false K hwa', eWedge_smul_single,
        eWedgeGen_of_false K (by rw [Function.update_of_ne hne.symm]; exact hwb'), hpre2,
        eSign_smul_smul, Function.update_comm hne true true w]
      ring_nf
    rw [eWedge_comp_lt K a b hab w hwa' hwb', hsnd, add_comm (ePre w b) (ePre w a),
      pow_succ]
    rw [← add_smul]
    simp
  rcases lt_trichotomy a b with h | h | h
  · exact key a b h
  · subst h
    rw [eWedge_eWedge_self K a, add_zero]
  · rw [add_comm]; exact key b a h

/-! ## 3. The CAR relation -/

/-- Deleting and inserting in the **same** slot is the identity, however the slot is
filled: exactly one of the two composites is nonzero and its two signs are equal. -/
theorem ePart_eWedge_self (a : Fin p) :
    (ePart K a).comp (eWedge K a) + (eWedge K a).comp (ePart K a)
      = LinearMap.id := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    eWedge_single, ePart_single]
  by_cases h : w a = true
  · rw [eWedgeGen_of_true K h, map_zero, zero_add, ePartGen_of_true K h,
      eWedge_smul_single, eWedgeGen_of_false K (by simp),
      ePre_update_of_le w a false a le_rfl, eSign_smul_smul,
      Function.update_idem, Function.update_eq_self_iff.2 h.symm]
    rw [← two_mul, pow_mul]
    simp
  · have h' : w a = false := Bool.eq_false_of_not_eq_true h
    rw [ePartGen_of_false K h', map_zero, add_zero, eWedgeGen_of_false K h',
      ePart_smul_single, ePartGen_of_true K (by simp),
      ePre_update_of_le w a true a le_rfl, eSign_smul_smul,
      Function.update_idem, Function.update_eq_self_iff.2 h'.symm]
    rw [← two_mul, pow_mul]
    simp

/-- Deleting in one slot and inserting in a **different** one anticommute. -/
theorem ePart_eWedge_of_ne (a b : Fin p) (hab : a ≠ b) :
    (ePart K a).comp (eWedge K b) + (eWedge K b).comp (ePart K a) = 0 := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    eWedge_single, ePart_single]
  by_cases hwa : w a = true
  · by_cases hwb : w b = true
    · rw [eWedgeGen_of_true K hwb, map_zero, zero_add, ePartGen_of_true K hwa,
        eWedge_smul_single,
        eWedgeGen_of_true K (by rw [Function.update_of_ne hab.symm]; exact hwb), smul_zero]
    have hwb' : w b = false := Bool.eq_false_of_not_eq_true hwb
    -- both composites are nonzero here; they differ by one in the exponent
    have hfst : ePart K a (eWedgeGen K b w)
        = ((-1 : K) ^ (ePre w b + ePre (Function.update w b true) a)) •
            Finsupp.single (Function.update (Function.update w b true) a false) (1 : K) := by
      rw [eWedgeGen_of_false K hwb', ePart_smul_single,
        ePartGen_of_true K (by rw [Function.update_of_ne hab]; exact hwa), eSign_smul_smul]
    have hsnd : eWedge K b (ePartGen K a w)
        = ((-1 : K) ^ (ePre w a + ePre (Function.update w a false) b)) •
            Finsupp.single (Function.update (Function.update w b true) a false) (1 : K) := by
      rw [ePartGen_of_true K hwa, eWedge_smul_single,
        eWedgeGen_of_false K (by rw [Function.update_of_ne hab.symm]; exact hwb'),
        eSign_smul_smul, Function.update_comm hab.symm true false w]
    -- The two exponents differ by exactly one, whichever of `a`, `b` comes first: the
    -- prefix at the LATER slot moves by one and the prefix at the earlier one does not.
    have hodd : ePre w a + ePre (Function.update w a false) b + 1
        = ePre w b + ePre (Function.update w b true) a := by
      rcases lt_or_gt_of_ne hab with h | h
      · have h1 : ePre (Function.update w b true) a = ePre w a :=
          ePre_update_of_le w b true a (le_of_lt h)
        have h2 := ePre_update_of_lt w a false b h
        rw [hwa] at h2
        simp only [eLetterDeg_true, eLetterDeg_false, add_zero] at h2
        omega
      · have h1 : ePre (Function.update w a false) b = ePre w b :=
          ePre_update_of_le w a false b (le_of_lt h)
        have h2 := ePre_update_of_lt w b true a h
        rw [hwb'] at h2
        simp only [eLetterDeg_true, eLetterDeg_false, add_zero] at h2
        omega
    rw [hfst, hsnd, ← hodd, pow_succ, ← add_smul]
    simp
  · have hwa' : w a = false := Bool.eq_false_of_not_eq_true hwa
    rw [ePartGen_of_false K hwa', map_zero, add_zero]
    by_cases hwb : w b = true
    · rw [eWedgeGen_of_true K hwb, map_zero]
    · rw [eWedgeGen_of_false K (Bool.eq_false_of_not_eq_true hwb), ePart_smul_single,
        ePartGen_of_false K (by rw [Function.update_of_ne hab]; exact hwa'), smul_zero]

end GroupApproximation.CharClass
