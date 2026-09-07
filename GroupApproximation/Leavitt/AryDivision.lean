import GroupApproximation.Leavitt.AryNormalForm
import GroupApproximation.Leavitt.AryKillWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Single-sandwich division for the universal `d`-ary Leavitt algebra

Stage three of generalising

`LeavittWords → LeavittNormalForm → LeavittSimplicity → division`

from arity `2` to arity `d`.  Stages one and two are `AryWords.lean` and
`AryNormalForm.lean`; the cylinder partition and the annihilating word are in
`AryKillWord.lean`.  What is left is the two theorems of
`Leavitt/LeavittSimplicity.lean`'s second half: every element has a finite
monomial representation, and every nonzero element divides the identity from both
sides.

Closing the second is what
`LeavittPurelyInfinite.isPurelyInfiniteSimpleRing_aryLeavitt_of_division` is
waiting for, and with it `L_k(1,d)` is purely infinite simple in the printed
idempotent form for every field and every `d ≥ 2`.
-/

namespace GroupApproximation
namespace AryLeavitt

open CompleteMatrixFamily

noncomputable section

variable (k : Type*) [Field k] (d : ℕ)

/-- **Every element has a finite monomial representation.**

`span_monomialSet_eq_top` of `AryNormalForm.lean` says the monomials span; this
turns that into an explicit finite indexed sum, by induction over the span. -/
theorem exists_monomial_representation (x : AryLeavittAlgebra k d) :
    ∃ (n : ℕ) (co : Fin n → k) (al be : Fin n → List (Fin d)),
      x = ∑ i, co i •
        ((family k d).wordS (al i) * (family k d).wordT (be i)) := by
  have hx : x ∈ Submodule.span k (monomialSet k d) := by
    rw [span_monomialSet_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, rfl⟩ := hu
      exact ⟨1, fun _ => 1, fun _ => a, fun _ => b, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨n₁, co₁, al₁, be₁, rfl⟩ := hu
      obtain ⟨n₂, co₂, al₂, be₂, rfl⟩ := hv
      refine ⟨n₁ + n₂, Fin.append co₁ co₂, Fin.append al₁ al₂,
        Fin.append be₁ be₂, ?_⟩
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by
          rw [Fin.append_left, Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [Fin.append_right, Fin.append_right, Fin.append_right]
  | smul c u _ hu =>
      obtain ⟨n, co, al, be, rfl⟩ := hu
      refine ⟨n, fun i => c * co i, al, be, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        smul_smul c (co i)
          ((family k d).wordS (al i) * (family k d).wordT (be i))


open Classical in
/-- **Single-sandwich division at arity `d`**: every nonzero element of
`L_k(1,d)` divides the identity from both sides.

The argument is `Leavitt/LeavittSimplicity.lean`'s, with the alphabet `Fin 2`
replaced by `Fin d`.  `2 ≤ d` enters in exactly one place: choosing the two
distinct letters the annihilating word is built from. -/
theorem exists_mul_mul_eq_one (hd : 2 ≤ d) {x : AryLeavittAlgebra k d}
    (hx : x ≠ 0) :
    ∃ a b : AryLeavittAlgebra k d, a * x * b = 1 := by
  have hd0 : 0 < d := by omega
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  have hine : i₁ ≠ i₀ := by
    intro h
    have hv := congrArg Fin.val h
    simp [i₀, i₁] at hv
  set L := family k d with hL
  obtain ⟨n, co, al, be, hrep⟩ := exists_monomial_representation k d x
  set M := Finset.univ.sup (fun i : Fin n ↦ (be i).length) with hM
  have hnonvanish : ∃ f : Fin M → Fin d, x * L.wordS (List.ofFn f) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    rw [eq_sum_mul_wordS_mul_wordT L x M]
    refine Finset.sum_eq_zero fun f _ ↦ ?_
    rw [hall f, zero_mul]
  obtain ⟨f₀, hy0⟩ := hnonvanish
  set δ := List.ofFn f₀ with hδ
  have hδlen : δ.length = M := by rw [hδ, List.length_ofFn]
  set y := x * L.wordS δ with hy
  set T := Finset.univ.filter (fun i : Fin n ↦ be i <+: δ) with hT
  set γfun : Fin n → List (Fin d) :=
    fun i ↦ al i ++ δ.drop (be i).length with hγfun
  have hyrep : y = ∑ i ∈ T, co i • L.wordS (γfun i) := by
    rw [hy, hrep, Finset.sum_mul]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n ↦ be i <+: δ)]
    rw [show (∑ i ∈ Finset.univ.filter
        (fun i : Fin n ↦ ¬ be i <+: δ),
        (co i • (L.wordS (al i) * L.wordT (be i))) * L.wordS δ) =
      0 from Finset.sum_eq_zero fun i hi ↦ by
        rw [Finset.mem_filter] at hi
        have hnotrev : ¬ δ <+: be i := by
          intro hrev
          have hlen : δ.length ≤ (be i).length := hrev.length_le
          have hlen2 : (be i).length ≤ M := by
            rw [hM]
            exact Finset.le_sup (f := fun i : Fin n ↦ (be i).length)
              (Finset.mem_univ i)
          have heq : δ.length = (be i).length := by omega
          have hde : δ = be i := List.IsPrefix.eq_of_length hrev heq
          exact hi.2 (hde ▸ List.prefix_refl δ)
        rw [smul_mul_assoc, mul_assoc,
          L.wordT_mul_wordS_of_incomparable (be i) δ hi.2 hnotrev,
          mul_zero, smul_zero]]
    rw [add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hT, Finset.mem_filter] at hi
    obtain ⟨e, he⟩ := hi.2
    have hdrop : δ.drop (be i).length = e := by rw [← he, List.drop_left]
    have hγ : γfun i = al i ++ e := by
      rw [hγfun]
      beta_reduce
      rw [hdrop]
    have hcollapse : L.wordT (be i) * L.wordS δ = L.wordS e := by
      rw [← he]
      exact L.wordT_mul_wordS_append_left (be i) e
    rw [hγ, smul_mul_assoc, mul_assoc, hcollapse, L.wordS_append]
  set G := T.image γfun with hG
  set gc : List (Fin d) → k :=
    fun γ ↦ ∑ i ∈ T.filter (fun i ↦ γfun i = γ), co i with hgc
  have hydisj : ((G : Set (List (Fin d)))).PairwiseDisjoint
      (fun γ ↦ T.filter (fun i ↦ γfun i = γ)) := by
    intro γ₁ _ γ₂ _ hne
    refine Finset.disjoint_left.2 fun i h1 h2 ↦ ?_
    rw [Finset.mem_filter] at h1 h2
    exact hne (h1.2 ▸ h2.2)
  have hybiunion : G.biUnion
      (fun γ ↦ T.filter (fun i ↦ γfun i = γ)) = T := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, hG, Finset.mem_image]
    constructor
    · rintro ⟨γ, -, hi, -⟩
      exact hi
    · intro hi
      exact ⟨γfun i, ⟨i, hi, rfl⟩, hi, rfl⟩
  have hyreg : y = ∑ γ ∈ G, gc γ • L.wordS γ := by
    rw [hyrep, ← hybiunion, Finset.sum_biUnion hydisj]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [hgc]
    beta_reduce
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  set G' := G.filter (fun γ ↦ gc γ ≠ 0) with hG'
  have hyreg' : y = ∑ γ ∈ G', gc γ • L.wordS γ := by
    rw [hyreg, hG']
    rw [← Finset.sum_filter_add_sum_filter_not G (fun γ ↦ gc γ ≠ 0)]
    rw [show (∑ γ ∈ G.filter (fun γ ↦ ¬ gc γ ≠ 0),
        gc γ • L.wordS γ) = 0 from Finset.sum_eq_zero fun γ hγ ↦ by
      rw [Finset.mem_filter] at hγ
      rw [not_not.mp hγ.2, zero_smul]]
    rw [add_zero]
  have hG'ne : G'.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hy0
    rw [hyreg', hempty, Finset.sum_empty]
  obtain ⟨γ₀, hγ₀G, hγ₀min⟩ :=
    Finset.exists_min_image G' List.length hG'ne
  have hgγ₀ : gc γ₀ ≠ 0 := (Finset.mem_filter.mp hγ₀G).2
  set m := G'.sup List.length with hm
  set w := AryKillWord.killWord i₀ i₁ m with hw
  have hkill : ∀ γ ∈ G'.erase γ₀,
      L.wordT w * (L.wordT γ₀ * L.wordS γ) * L.wordS w = 0 := by
    intro γ hγ
    have hγG' : γ ∈ G' := Finset.mem_of_mem_erase hγ
    have hγne : γ ≠ γ₀ := Finset.ne_of_mem_erase hγ
    have hminle : γ₀.length ≤ γ.length := hγ₀min γ hγG'
    by_cases hpre : γ₀ <+: γ
    · obtain ⟨ε, hε⟩ := hpre
      have hεne : ε ≠ [] := by
        rintro rfl
        rw [List.append_nil] at hε
        exact hγne hε.symm
      have hεlen : ε.length ≤ m := by
        have hγlen : γ.length ≤ m := Finset.le_sup hγG'
        have hcong := congrArg List.length hε
        rw [List.length_append] at hcong
        omega
      rw [← hε, L.wordT_mul_wordS_append_left γ₀ ε]
      rw [show L.wordT w * L.wordS ε * L.wordS w =
        L.wordT w * L.wordS (ε ++ w) from by
        rw [L.wordS_append, mul_assoc]]
      rw [L.wordT_mul_wordS_of_incomparable w (ε ++ w)
        (AryKillWord.killWord_not_prefix i₀ i₁ hine ε m hεne hεlen)
        (by
          intro hrev
          have hlen := hrev.length_le
          rw [List.length_append] at hlen
          have hz : ε.length = 0 := by omega
          exact hεne (List.length_eq_zero_iff.mp hz))]
    · have hnotrev : ¬ γ <+: γ₀ := by
        intro hrev
        have hlen : γ.length ≤ γ₀.length := hrev.length_le
        have heq : γ.length = γ₀.length := by omega
        exact hγne (List.IsPrefix.eq_of_length hrev heq)
      rw [L.wordT_mul_wordS_of_incomparable γ₀ γ hpre hnotrev,
        mul_zero, zero_mul]
  have hcollapse : L.wordT w * (L.wordT γ₀ * y) * L.wordS w = gc γ₀ • 1 := by
    calc L.wordT w * (L.wordT γ₀ * y) * L.wordS w
        = ∑ γ ∈ G', L.wordT w * (L.wordT γ₀ * (gc γ • L.wordS γ)) *
            L.wordS w := by
          rw [hyreg', Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      _ = gc γ₀ • 1 := by
          rw [Finset.sum_eq_single_of_mem γ₀ hγ₀G (fun γ hγ hne ↦ by
            rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc,
              hkill γ (Finset.mem_erase.2 ⟨hne, hγ⟩), smul_zero])]
          rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc,
            L.wordT_mul_wordS_self, mul_one, L.wordT_mul_wordS_self]
  refine ⟨(gc γ₀)⁻¹ • (L.wordT w * L.wordT γ₀), L.wordS δ * L.wordS w, ?_⟩
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [show L.wordT w * L.wordT γ₀ * x * (L.wordS δ * L.wordS w) =
    L.wordT w * (L.wordT γ₀ * y) * L.wordS w from by
    rw [hy]
    simp only [mul_assoc]]
  rw [hcollapse, smul_smul, inv_mul_cancel₀ hgγ₀, one_smul]


end

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.exists_monomial_representation
#audit_axioms GroupApproximation.AryLeavitt.exists_mul_mul_eq_one
