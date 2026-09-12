import GroupApproximation.CharClass.ParityPHomogConverse

/-!
# L4a, step seven: `eCoeff` is the linear coefficient of the `e`-expansion

`eCoeff` is defined through the dual numbers, and the crux
(`ParityPHomogConverse.eExpand_isWeightedHomogeneous`) is a statement about `eExpand`.
Nothing so far connects them.  This file supplies the connection:

```text
  eCoeff a f  =  coeff (single a 1) (eExpand f).
```

That identification is a genuine lemma and not bookkeeping.  It is proved by linearity plus
a three-way split on the exponent vector of a monomial: the constant term contributes to
`fst` and not to `snd`; the monomial `X_a` contributes `ε`; and everything else contributes
`0`, either because some variable other than `a` occurs — and those are sent to `0` — or
because `X_a` occurs to a power at least two and `ε² = 0`.

**The trap this construction avoids** (flagged by `sp-design`): the identification would be
FALSE in a ring of *independent* dual numbers `ε_i` with only `ε_i² = 0`, because the cross
terms `ε_i ε_j` with `i ≠ j` survive and a length-two monomial would not die — while the
lemma would still hold on every monomial one would test first.  The construction here is
the safe one and for a reason worth stating: there is a **single** `ε`, and every variable
other than `X_a` is sent to `0`, so a cross term dies because one of its factors is
literally `0` rather than because a square vanishes.  Only the `X_a^{≥2}` case uses
`ε² = 0`.

## Main results

* `GroupApproximation.CharClass.ParityP.eLin_snd_eq_coeff` — the identification, on raw
  polynomials.
* `ParityP.eCoeff_eq_coeff_eExpand` — the same, as a statement about `eCoeff`.
* `ParityP.eCoeff_eq_zero_of_degree_ne` — the consequence the assembly wants: `eCoeff a`
  annihilates a symmetric polynomial homogeneous of degree other than `a + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section Bridge

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The substitution used by `eLin`: `X_a ↦ ε`, every other variable to `0`. -/
noncomputable def epsSub (a : Fin n) : Fin n → DualNumber R :=
  fun k => if k = a then (DualNumber.eps : DualNumber R) else 0

@[simp] theorem epsSub_self (a : Fin n) :
    (epsSub a : Fin n → DualNumber R) a = DualNumber.eps := by
  simp [epsSub]

theorem epsSub_of_ne {a k : Fin n} (h : k ≠ a) :
    (epsSub a : Fin n → DualNumber R) k = 0 := by
  simp [epsSub, h]

/-- On a monomial whose exponent vector is not `single a 1`, the substitution has vanishing
`snd`. -/
theorem snd_prod_eq_zero_of_ne {a : Fin n} {d : Fin n →₀ ℕ} (hd : d ≠ Finsupp.single a 1)
    (r : R) :
    (algebraMap R (DualNumber R) r * d.prod fun i k => (epsSub a i : DualNumber R) ^ k).snd
      = 0 := by
  classical
  have hprod : (d.prod fun i k => (epsSub a i : DualNumber R) ^ k).snd = 0 := by
    by_cases hsupp : ∀ i ∈ d.support, i = a
    · -- `d` is concentrated at `a`, so `d = single a (d a)` with `d a ≠ 1`.
      have hda : d = Finsupp.single a (d a) := by
        ext i
        by_cases hi : i = a
        · subst hi; simp
        · have hi' : i ∉ d.support := fun hmem => hi (hsupp i hmem)
          rw [Finsupp.notMem_support_iff] at hi'
          rw [hi', Finsupp.single_apply, if_neg (Ne.symm hi)]
      have hne1 : d a ≠ 1 := by
        intro h
        exact hd (by rw [hda, h])
      rw [hda, Finsupp.prod_single_index (by simp), epsSub_self]
      rcases Nat.lt_or_ge (d a) 1 with hlt | hge
      · have h0 : d a = 0 := by omega
        rw [h0, pow_zero, TrivSqZeroExt.snd_one]
      · have hge2 : 2 ≤ d a := by omega
        obtain ⟨c, hc⟩ : ∃ c, d a = 2 + c := ⟨d a - 2, by omega⟩
        rw [hc, pow_add, pow_two, DualNumber.eps_mul_eps, zero_mul, TrivSqZeroExt.snd_zero]
    · -- some variable other than `a` occurs, and it is sent to `0`
      obtain ⟨i, hi, hia⟩ : ∃ i ∈ d.support, i ≠ a := by
        by_contra hcon
        exact hsupp fun i hi => by
          by_contra hne
          exact hcon ⟨i, hi, hne⟩
      have hzero : (epsSub a i : DualNumber R) ^ d i = 0 := by
        rw [epsSub_of_ne hia]
        exact zero_pow (Finsupp.mem_support_iff.mp hi)
      rw [Finsupp.prod, Finset.prod_eq_zero hi hzero, TrivSqZeroExt.snd_zero]
  rw [TrivSqZeroExt.snd_mul, hprod]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- **The identification, on raw polynomials.** -/
theorem eLin_snd_eq_coeff (a : Fin n) (G : MvPolynomial (Fin n) R) :
    (aeval (epsSub a : Fin n → DualNumber R) G).snd = coeff (Finsupp.single a 1) G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [aeval_monomial, MvPolynomial.coeff_monomial]
    by_cases hd : d = Finsupp.single a 1
    · subst hd
      rw [if_pos rfl, Finsupp.prod_single_index (by simp), epsSub_self, pow_one,
        TrivSqZeroExt.algebraMap_eq_inl, DualNumber.eps, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr]
      simp
    · rw [if_neg hd]
      exact snd_prod_eq_zero_of_ne hd r
  | add p q hp hq =>
    rw [map_add, TrivSqZeroExt.snd_add, coeff_add, hp, hq]

/-- **The identification, for `eCoeff`.** -/
theorem eCoeff_eq_coeff_eExpand (a : Fin n) (f : symmetricSubalgebra (Fin n) R) :
    eCoeff a f = coeff (Finsupp.single a 1) (eExpand f) :=
  eLin_snd_eq_coeff a (eExpand f)

/-- **The consequence the assembly wants.**  `eCoeff a` annihilates a symmetric polynomial
homogeneous of a degree other than `a + 1`: the monomial `X_a` has weight `a + 1`, and by
the crux the `e`-expansion is weighted-homogeneous of the polynomial's degree, so it has no
coefficient at a monomial of the wrong weight. -/
theorem eCoeff_eq_zero_of_degree_ne {w : ℕ} (a : Fin n) (f : symmetricSubalgebra (Fin n) R)
    (hf : MvPolynomial.IsHomogeneous (f : MvPolynomial (Fin n) R) w)
    (hne : (a : ℕ) + 1 ≠ w) : eCoeff a f = 0 := by
  rw [eCoeff_eq_coeff_eExpand]
  by_contra hc
  refine hne ?_
  have hwt := eExpand_isWeightedHomogeneous f hf (d := Finsupp.single a 1) hc
  simpa [Finsupp.weight_single, eWeight] using hwt

end Bridge

end ParityP

end GroupApproximation.CharClass
