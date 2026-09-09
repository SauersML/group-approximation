import GroupApproximation.Algebra.PeirceUnitFactorization
import GroupApproximation.Algebra.PurelyInfiniteSimpleRingIdempotents

/-!
# Shape (a): every unit factors as `u = gvh`, at any item-(a) decomposition

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a):

> … and every unit `u` of `R` factors as `u = gvh` with `g` and `h` products of
> elementary matrices `e_{ij}(x)` of this matrix ring and
> `v = e_1 + (1-e_1)v(1-e_1)`.

`PrintedItemAShape` below is that clause, quantified over **every** family of
idempotents meeting item (a)'s printed hypotheses, and `printedItemAShape`
proves it.

## Why the frame reduction does not reach this

`Algebra/PeirceUnitFactorization.lean` reduces a unit using a `Frame`, that is
two orthogonal idempotents each equivalent to `1`, so its matrix coefficients
lie in `R` itself.  At an arbitrary item-(a) decomposition the blocks are
equivalent to one another but **not** to `1`, so that machinery does not apply.

The fix is to run the same three steps with the coefficients in the Hom-sets
`e_i R e_j`, and to take the sandwich inside the corner `e_k R e_k` rather than
in `R`.  That corner is purely infinite simple by
`isPurelyInfiniteSimpleRing_corner`, so it has the sandwich property, which is
all the pivot and the identity-planting steps need.

## The three steps

Write `P = e_k` for an auxiliary block and `Q = e_{i₀}` for the printed `e_1`,
with `α ∈ PRQ` and `β ∈ QRP` a normalised equivalence, `αβ = P`, `βα = Q`.

1. **Pivot** (`exists_blockPivot`): make `P v P ≠ 0`.  The argument uses only
   that `P` is a nonzero idempotent and that `R` has the ambient sandwich
   property; it never uses `P ~ 1`.
2. **Plant the identity** (`exists_blockIdentityCorner`): with `A = P v P ≠ 0`,
   sandwich it inside `PRP` as `p A q = P`.  Right-multiplying by `1 + x`,
   `x = q(α - pB) ∈ PRQ` and `B = P v Q`, gives `p (P v₁ Q) = α`.  Then
   left-multiplying by `1 + y`, `y = (Q - D)βp ∈ QRP` and `D = Q v₁ Q`, gives
   `Q v₂ Q = Q`, because `βα = Q`.
3. **Clear** (`exists_clearing_factorization`, already proved): the transvections
   it needs lie in `Q R (1-Q)` and `(1-Q) R Q`, which
   `peirceOneAdd_of_left` and `peirceOneAdd_of_right` place in the elementary
   subgroup.

## The blocks are nonzero for free

Item (a) does not say the blocks are nonzero, and the proof needs it.  It
follows: if `e_k = 0` then `e_{i₀} ~ e_k` forces `e_{i₀} = 0`, so every non-last
block vanishes and `1 = e_last`; but `e_last ~ f` with `f ≤ e_{i₀} = 0` forces
`f = 0` and hence `e_last = 0`, contradicting nontriviality.  So the printed
clauses about `f` are load-bearing, not decoration.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type} [Ring R]

/-! ### The corner sandwich, in ambient notation -/

/-- `exists_corner_sandwich` with the corner's elements named in `R`. -/
theorem exists_corner_sandwich_val (hR : IsPurelyInfiniteSimpleRing R) {P : R}
    (hP : IsIdempotentElem P) {A : R} (hPA : P * A = A) (hAP : A * P = A)
    (hA : A ≠ 0) :
    ∃ p q : R, P * p = p ∧ p * P = p ∧ P * q = q ∧ q * P = q ∧
      p * A * q = P := by
  have hmem : A ∈ cornerNonUnitalSubring P hP := ⟨hPA, hAP⟩
  have hne : (⟨A, hmem⟩ : Corner R P hP) ≠ 0 := fun h =>
    hA (by simpa using congrArg (fun z : Corner R P hP => (z : R)) h)
  obtain ⟨s, t, hst⟩ := exists_corner_sandwich hR hP hne
  refine ⟨(t : R), (s : R), t.2.1, t.2.2, s.2.1, s.2.2, ?_⟩
  have h := congrArg (fun z : Corner R P hP => (z : R)) hst
  simpa using h

/-! ### Step 1: the pivot -/

/-- **Pivot at a block.**  One column transvection along `P` makes the
`P`-corner of the unit nonzero. -/
theorem exists_blockPivot (hR : IsPurelyInfiniteSimpleRing R)
    {N : Subgroup Rˣ} {P : R} (hP : IsIdempotentElem P) (hPne : P ≠ 0)
    (hlowerP : ∀ {x : R}, P * x = 0 → x * P = x → ∃ w ∈ N, (w : R) = 1 + x)
    (u : Rˣ) : ∃ v : Rˣ, FactorsThrough N u v ∧ P * (v : R) * P ≠ 0 := by
  have huinv : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 :=
    congrArg (Units.val : Rˣ → R) (mul_inv_cancel u)
  have heu : P * (u : R) ≠ 0 := by
    intro hz
    apply hPne
    calc P = (P * (u : R)) * ((u⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, huinv, mul_one]
      _ = 0 := by rw [hz, zero_mul]
  by_cases hz : P * (u : R) * P = 0
  · obtain ⟨p, q, hpq⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR heu
    have hl : P * ((1 - P) * q * P) = 0 := by
      calc P * ((1 - P) * q * P) = (P - P * P) * q * P := by noncomm_ring
        _ = 0 := by rw [hP, sub_self]; simp
    have hr : ((1 - P) * q * P) * P = (1 - P) * q * P := by rw [mul_assoc, hP]
    obtain ⟨w, hw, hwval⟩ := hlowerP hl hr
    refine ⟨u * w, FactorsThrough.right N u w hw, ?_⟩
    have hval : P * ((u * w : Rˣ) : R) * P = (P * (u : R)) * q * P := by
      rw [Units.val_mul, hwval]
      calc P * ((u : R) * (1 + (1 - P) * q * P)) * P
          = P * (u : R) * P
            + (P * (u : R) - P * (u : R) * P) * q * (P * P) := by noncomm_ring
        _ = (P * (u : R)) * q * P := by rw [hz, hP, sub_zero, zero_add]
    rw [hval]
    intro hz'
    apply hPne
    calc P = (p * (P * (u : R)) * q) * P := by rw [hpq, one_mul]
      _ = p * ((P * (u : R)) * q * P) := by noncomm_ring
      _ = 0 := by rw [hz', mul_zero]
  · exact ⟨u, FactorsThrough.refl _ u, hz⟩

/-! ### Step 2: planting the identity in the `Q`-corner -/

/-- **Planting the identity at a block.**  Two transvections, one in `PRQ` and
one in `QRP`, turn a unit whose `P`-corner is nonzero into one whose `Q`-corner
is the identity `Q` of that corner. -/
theorem exists_blockIdentityCorner (hR : IsPurelyInfiniteSimpleRing R)
    {N : Subgroup Rˣ} {P Q α β : R}
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hba : β * α = Q) (hPa : P * α = α) (haQ : α * Q = α)
    (hPQ : ∀ {x : R}, P * x = x → x * Q = x → ∃ w ∈ N, (w : R) = 1 + x)
    (hQP : ∀ {x : R}, Q * x = x → x * P = x → ∃ w ∈ N, (w : R) = 1 + x)
    (v : Rˣ) (hA : P * (v : R) * P ≠ 0) :
    ∃ v' : Rˣ, FactorsThrough N v v' ∧ Q * (v' : R) * Q = Q := by
  -- the sandwich inside `PRP`
  have hPA : P * (P * (v : R) * P) = P * (v : R) * P := by
    calc P * (P * (v : R) * P) = (P * P) * (v : R) * P := by noncomm_ring
      _ = P * (v : R) * P := by rw [hP]
  have hAP : (P * (v : R) * P) * P = P * (v : R) * P := by
    calc (P * (v : R) * P) * P = P * (v : R) * (P * P) := by noncomm_ring
      _ = P * (v : R) * P := by rw [hP]
  obtain ⟨p, q, hPp, hpP, hPq, hqP, hpq⟩ :=
    exists_corner_sandwich_val hR hP hPA hAP hA
  -- the first transvection, in `P R Q`
  obtain ⟨x, hxdef⟩ : ∃ x : R, x = q * (α - p * (P * (v : R) * Q)) := ⟨_, rfl⟩
  have hBQ : (P * (v : R) * Q) * Q = P * (v : R) * Q := by rw [mul_assoc, hQ]
  have hPx : P * x = x := by
    rw [hxdef]
    calc P * (q * (α - p * (P * (v : R) * Q)))
        = (P * q) * (α - p * (P * (v : R) * Q)) := by noncomm_ring
      _ = q * (α - p * (P * (v : R) * Q)) := by rw [hPq]
  have hxQ : x * Q = x := by
    rw [hxdef]
    calc q * (α - p * (P * (v : R) * Q)) * Q
        = q * (α * Q - p * ((P * (v : R) * Q) * Q)) := by noncomm_ring
      _ = q * (α - p * (P * (v : R) * Q)) := by rw [haQ, hBQ]
  obtain ⟨w, hw, hwval⟩ := hPQ hPx hxQ
  -- after the first transvection, the `(P,Q)` entry is `α` up to `p`
  have hAx : (P * (v : R) * P) * x = P * (v : R) * x := by
    rw [hxdef]
    calc (P * (v : R) * P) * (q * (α - p * (P * (v : R) * Q)))
        = P * (v : R) * (P * q) * (α - p * (P * (v : R) * Q)) := by noncomm_ring
      _ = P * (v : R) * (q * (α - p * (P * (v : R) * Q))) := by
          rw [hPq]; noncomm_ring
  have hv₁Q : P * ((v * w : Rˣ) : R) * Q
      = P * (v : R) * Q + (P * (v : R) * P) * x := by
    rw [Units.val_mul, hwval, hAx]
    calc P * ((v : R) * (1 + x)) * Q
        = P * (v : R) * Q + P * (v : R) * (x * Q) := by noncomm_ring
      _ = P * (v : R) * Q + P * (v : R) * x := by rw [hxQ]
  have hPpB : P * (p * (P * (v : R) * Q)) = p * (P * (v : R) * Q) := by
    calc P * (p * (P * (v : R) * Q))
        = (P * p) * (P * (v : R) * Q) := by noncomm_ring
      _ = p * (P * (v : R) * Q) := by rw [hPp]
  have hkey : p * (P * ((v * w : Rˣ) : R) * Q) = α := by
    rw [hv₁Q, hxdef]
    calc p * (P * (v : R) * Q
          + (P * (v : R) * P) * (q * (α - p * (P * (v : R) * Q))))
        = p * (P * (v : R) * Q)
          + (p * (P * (v : R) * P) * q) * (α - p * (P * (v : R) * Q)) := by
          noncomm_ring
      _ = p * (P * (v : R) * Q) + P * (α - p * (P * (v : R) * Q)) := by rw [hpq]
      _ = p * (P * (v : R) * Q) + (α - p * (P * (v : R) * Q)) := by
          rw [mul_sub, hPa, hPpB]
      _ = α := by abel
  -- the second transvection, in `Q R P`
  obtain ⟨y, hydef⟩ : ∃ y : R,
      y = (Q - Q * ((v * w : Rˣ) : R) * Q) * β * p := ⟨_, rfl⟩
  have hDQ : (Q * ((v * w : Rˣ) : R) * Q) * Q = Q * ((v * w : Rˣ) : R) * Q := by
    rw [mul_assoc, hQ]
  have hQD : Q * (Q * ((v * w : Rˣ) : R) * Q) = Q * ((v * w : Rˣ) : R) * Q := by
    calc Q * (Q * ((v * w : Rˣ) : R) * Q)
        = (Q * Q) * ((v * w : Rˣ) : R) * Q := by noncomm_ring
      _ = Q * ((v * w : Rˣ) : R) * Q := by rw [hQ]
  have hQy : Q * y = y := by
    rw [hydef]
    calc Q * ((Q - Q * ((v * w : Rˣ) : R) * Q) * β * p)
        = (Q * Q - Q * (Q * ((v * w : Rˣ) : R) * Q)) * β * p := by noncomm_ring
      _ = (Q - Q * ((v * w : Rˣ) : R) * Q) * β * p := by rw [hQ, hQD]
  have hyP : y * P = y := by
    rw [hydef]
    calc (Q - Q * ((v * w : Rˣ) : R) * Q) * β * p * P
        = (Q - Q * ((v * w : Rˣ) : R) * Q) * β * (p * P) := by noncomm_ring
      _ = (Q - Q * ((v * w : Rˣ) : R) * Q) * β * p := by rw [hpP]
  obtain ⟨z, hz, hzval⟩ := hQP hQy hyP
  refine ⟨z * (v * w), (FactorsThrough.right N v w hw).trans
    (FactorsThrough.left N (v * w) z hz), ?_⟩
  -- the `Q`-corner is now the identity of that corner
  have hexpand : Q * ((z * (v * w) : Rˣ) : R) * Q
      = Q * ((v * w : Rˣ) : R) * Q + y * (P * ((v * w : Rˣ) : R) * Q) := by
    rw [Units.val_mul, hzval]
    calc Q * ((1 + y) * ((v * w : Rˣ) : R)) * Q
        = Q * ((v * w : Rˣ) : R) * Q
          + (Q * y) * ((v * w : Rˣ) : R) * Q := by noncomm_ring
      _ = Q * ((v * w : Rˣ) : R) * Q
          + (y * P) * ((v * w : Rˣ) : R) * Q := by rw [hQy, hyP]
      _ = Q * ((v * w : Rˣ) : R) * Q
          + y * (P * ((v * w : Rˣ) : R) * Q) := by noncomm_ring
  rw [hexpand, hydef]
  calc Q * ((v * w : Rˣ) : R) * Q
        + (Q - Q * ((v * w : Rˣ) : R) * Q) * β * p *
          (P * ((v * w : Rˣ) : R) * Q)
      = Q * ((v * w : Rˣ) : R) * Q
        + (Q - Q * ((v * w : Rˣ) : R) * Q) * β *
          (p * (P * ((v * w : Rˣ) : R) * Q)) := by noncomm_ring
    _ = Q * ((v * w : Rˣ) : R) * Q
        + (Q - Q * ((v * w : Rˣ) : R) * Q) * (β * α) := by
        rw [hkey]; noncomm_ring
    _ = Q * ((v * w : Rˣ) : R) * Q
        + (Q * Q - (Q * ((v * w : Rˣ) : R) * Q) * Q) := by
        rw [hba]; noncomm_ring
    _ = Q := by rw [hQ, hDQ]; abel

/-! ### The printed clause -/

/-- **Shape (a), as a closed proposition.**

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a):

> … and every unit `u` of `R` factors as `u = gvh` with `g` and `h` products of
> elementary matrices `e_{ij}(x)` of this matrix ring and
> `v = e_1 + (1-e_1)v(1-e_1)`.

The hypotheses are item (a)'s, verbatim, and the conclusion is quantified over
every decomposition meeting them. -/
def PrintedItemAShape : Prop :=
  ∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ), 4 ≤ m → ∀ (e : Fin m → R),
      (∀ i, IsIdempotentElem (e i)) →
      (∀ i j : Fin m, i ≠ j → e i * e j = 0) →
      (∑ i, e i = 1) →
      ∀ i₀ last : Fin m, i₀ ≠ last →
        (∀ i j : Fin m, i ≠ last → j ≠ last →
          IsEquivalentIdempotent R (e i) (e j)) →
        ∀ (f : R), IsIdempotentElem f → IdempotentLE f (e i₀) →
          IsEquivalentIdempotent R (e last) f →
          ∀ u : Rˣ, ∃ v : Rˣ,
            FactorsThrough (peirceElementarySubgroup e) u v ∧
            (v : R) = e i₀ + (1 - e i₀) * (v : R) * (1 - e i₀)

/-- **The printed clause, proved.** -/
theorem printedItemAShape : PrintedItemAShape := by
  intro R _ hR m hm e hidem horth hsum i₀ last hne hpair f hfi hfle hlast u
  haveI := hR.isSimpleRing
  -- the blocks off the last index are nonzero
  have hi₀ne : e i₀ ≠ 0 := by
    intro hz
    have hnl : ∀ i, i ≠ last → e i = 0 := by
      intro i hil
      by_contra hne0
      exact ne_zero_of_isEquivalentIdempotent (hidem i) hne0
        (hpair i i₀ hil hne) hz
    have hf0 : f = 0 := by
      have hmul := hfle.1
      rw [hz, zero_mul] at hmul
      exact hmul.symm
    have hlast0 : e last = 0 := by
      by_contra hne0
      exact ne_zero_of_isEquivalentIdempotent (hidem last) hne0 hlast hf0
    have hone : (1 : R) = 0 := by
      rw [← hsum]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hil : i = last
      · rw [hil, hlast0]
      · exact hnl i hil
    exact one_ne_zero hone
  -- an auxiliary block, distinct from both distinguished indices
  obtain ⟨k, hki, hkl⟩ : ∃ k : Fin m, k ≠ i₀ ∧ k ≠ last := by
    by_contra hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i₀, last} := by
      intro y _
      by_cases hy : y = i₀
      · simp [hy]
      · have hyl : y = last := by
          by_contra hyl
          exact hcon ⟨y, hy, hyl⟩
        simp [hyl]
    have hle : ({i₀, last} : Finset (Fin m)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    have hcard := (Finset.card_le_card hsub).trans hle
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hkne : e k ≠ 0 :=
    ne_zero_of_isEquivalentIdempotent (hidem i₀) hi₀ne (hpair i₀ k hne hkl)
  -- the normalised equivalence between the two blocks
  obtain ⟨α, β, -, hba, hPa, haQ, -, -⟩ :=
    exists_normalized_equivalence (hidem k) (hidem i₀) (hpair k i₀ hkl hne)
  -- the transvection families
  have hPQ : ∀ {x : R}, e k * x = x → x * e i₀ = x →
      ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x := fun hx hxx =>
    peirceOneAdd_of_block e hki (horth i₀ k (Ne.symm hki)) hx hxx
  have hQP : ∀ {x : R}, e i₀ * x = x → x * e k = x →
      ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x := fun hx hxx =>
    peirceOneAdd_of_block e (Ne.symm hki) (horth k i₀ hki) hx hxx
  have hlowerP : ∀ {x : R}, e k * x = 0 → x * e k = x →
      ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x := fun hx hxx =>
    peirceOneAdd_of_right e hidem horth hsum k hxx hx
  have hupperQ : ∀ {x : R}, e i₀ * x = x → x * e i₀ = 0 →
      ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x := fun hx hxx =>
    peirceOneAdd_of_left e hidem horth hsum i₀ hx hxx
  have hlowerQ : ∀ {x : R}, e i₀ * x = 0 → x * e i₀ = x →
      ∃ w ∈ peirceElementarySubgroup e, (w : R) = 1 + x := fun hx hxx =>
    peirceOneAdd_of_right e hidem horth hsum i₀ hxx hx
  -- the three steps
  obtain ⟨v₁, h₁, hpivot⟩ :=
    exists_blockPivot hR (hidem k) hkne hlowerP u
  obtain ⟨v₂, h₂, hcorner⟩ :=
    exists_blockIdentityCorner hR (hidem k) (hidem i₀) hba hPa haQ
      hPQ hQP v₁ hpivot
  obtain ⟨v₃, h₃, hsupp⟩ :=
    exists_clearing_factorization (hidem i₀) hupperQ hlowerQ v₂ hcorner
  exact ⟨v₃, (h₁.trans h₂).trans h₃, hsupp⟩

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_corner_sandwich_val
#audit_axioms GroupApproximation.MFQuotientUnits.exists_blockPivot
#audit_axioms GroupApproximation.MFQuotientUnits.exists_blockIdentityCorner
#audit_closed_axioms GroupApproximation.MFQuotientUnits.printedItemAShape
