import GroupApproximation.GGT.HullSCRelatorSeparation2WindowExact
import GroupApproximation.GGT.HullSCRelatorSeparation2Diff
import GroupApproximation.GGT.HullSCRelatorSeparation2ThroughBase
import GroupApproximation.GGT.HullSCRelatorSeparation2CyclicThroughBase
import GroupApproximation.GGT.HullSCRelatorSeparation2BaseFirst
import GroupApproximation.GGT.HullSCRelatorSeparation2Core

/-!
# The exact exponent design with both missing separation clauses

Hull's §6 does not require a side-exclusion statement for every exponent list.
It chooses the exponents greedily and only uses the exclusions for that chosen
list.  This module combines the two finite-avoidance constructions needed by
that choice:

* `windowBadPow` prevents a bounded alternating tail from closing into the
  other peripheral subgroup;
* `diffBad` makes every positive difference of two chosen exponents miss a
  prescribed finite set.

The returned list has exactly the requested length.  This matters because the
radius used for the isolated-component estimate may depend on that length; a
mere lower bound would make the choice circular.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section WindowDiffExact

variable {G : Type u} [Group G]

/-- **The combined exact exponent design.**

At every greedy step the new powers avoid one finite union: the original depth
set, all bounded tails that would close in the opposite family member, and all
translates that would make a difference of exponents shallow. -/
theorem exists_separated_exponents_window_diff_through_exact
    {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hfam : ∀ s : Bool, a s ∈ D.fam s)
    {K : Set G} (hK : K.Finite) {T : Set G} (hT : T.Finite)
    {B : Set G} (hB : B.Finite) (baseLetter : G) (W L : ℕ) :
    ∃ ms : List ℕ, ms.length = L ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, j < i → ∀ s : Bool, a s ^ (i - j) ∉ B) ∧
      (∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
        ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
          a s ^ n * GGT.RelLetter.listVal
            (blockWord (a false) (a true) t (post.take r))
            ∉ D.fam (!s)) ∧
      CyclicThroughBaseAvoidance D a baseLetter W ms ∧
      BaseFirstAvoidance D a baseLetter W ms := by
  induction L with
  | zero =>
      refine ⟨[], rfl, List.nodup_nil, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · intro m hm
        simp at hm
      · intro i hi
        simp at hi
      · intro i hi
        simp at hi
      · intro pre post n hsplit
        cases pre <;> simp at hsplit
      · intro pre post n hsplit
        cases pre <;> simp at hsplit
  | succ L ih =>
      obtain ⟨ms, hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough, -⟩ := ih
      let C : Set G :=
        K ∪ (windowBadPow D a (a false) (a true) ms W ∪
          (diffBad a B ms ∪
            (throughBaseBadPow D a (a false) (a true) ms W baseLetter ∪
              (cyclicThroughBasePrefixBadPow D a ms W baseLetter ∪
                baseFirstBadPow D a ms W baseLetter))))
      have hC : C.Finite := by
        exact hK.union
          ((finite_windowBadPow hemb hinj hfam (a false) (a true) ms W).union
            ((finite_diffBad a hB ms).union
              ((finite_throughBaseBadPow hemb hinj hfam (a false) (a true) ms W
                  baseLetter).union
                ((finite_cyclicThroughBasePrefixBadPow hemb hinj hfam ms W
                    baseLetter hthrough).union
                  (finite_baseFirstBadPow hemb hinj hfam ms W baseLetter)))))
      obtain ⟨m, hm, hdeepm, hnew⟩ :=
        exists_pow_separated_family hinj hT ms C hC (ms.sum + 1)
      have hgt : ∀ j ∈ ms, j < m := by
        intro j hj
        have hle := le_sum_of_mem_nat hj
        omega
      have hnotmem : m ∉ ms := fun hmem => Nat.lt_irrefl m (hgt m hmem)
      have hwinm : ∀ s : Bool,
          a s ^ m ∉ windowBadPow D a (a false) (a true) ms W := by
        intro s hc
        exact (hdeepm s).1 (Set.mem_union_right _ (Set.mem_union_left _ hc))
      have hdiffm : ∀ s : Bool, a s ^ m ∉ diffBad a B ms := by
        intro s hc
        exact (hdeepm s).1
          (Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_union_left _ hc)))
      have hthroughm : ∀ s : Bool,
          a s ^ m ∉ throughBaseBadPow D a (a false) (a true) ms W
            baseLetter := by
        intro s hc
        exact (hdeepm s).1
          (Set.mem_union_right _ (Set.mem_union_right _
            (Set.mem_union_right _ (Set.mem_union_left _ hc))))
      have hprefixm : ∀ s : Bool,
          a s ^ m ∉ cyclicThroughBasePrefixBadPow D a ms W baseLetter := by
        intro s hc
        exact (hdeepm s).1
          (Set.mem_union_right _ (Set.mem_union_right _
            (Set.mem_union_right _ (Set.mem_union_right _
              (Set.mem_union_left _ hc)))))
      have hbaseFirstm :
          a false ^ m ∉ baseFirstBadPow D a ms W baseLetter := by
        intro hc
        exact (hdeepm false).1
          (Set.mem_union_right _ (Set.mem_union_right _
            (Set.mem_union_right _ (Set.mem_union_right _
              (Set.mem_union_right _ hc)))))
      refine ⟨m :: ms, by simp [hlen], List.nodup_cons.mpr ⟨hnotmem, hnodup⟩,
        ?_, ?_, ?_, ?_, ?_, baseFirstAvoidance_cons_of_notMem hbaseFirstm⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · intro s
          exact ⟨fun hc => (hdeepm s).1 (Set.mem_union_left _ hc),
            fun hc => (hdeepm s).2 (Set.mem_union_left _ hc)⟩
        · exact hdeep i hi'
      · intro i hi j hj hij s x hx x' hx'
        rcases List.mem_cons.mp hi with rfl | hi'
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact absurd rfl hij
          · exact ⟨(hnew j hj' s x hx x' hx').1,
              (hnew j hj' s x hx x' hx').2.2.1⟩
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact ⟨(hnew i hi' s x hx x' hx').2.1,
              (hnew i hi' s x hx x' hx').2.2.2⟩
          · exact hsep i hi' j hj' hij s x hx x' hx'
      · intro i hi j hj hji s
        rcases List.mem_cons.mp hi with rfl | hi'
        · have hjms : j ∈ ms := by
            rcases List.mem_cons.mp hj with rfl | hj'
            · exfalso
              omega
            · exact hj'
          exact notMem_of_notMem_diffBad hdiffm hjms
            (le_of_lt (hgt j hjms)) s
        · have hjms : j ∈ ms := by
            rcases List.mem_cons.mp hj with rfl | hj'
            · exfalso
              have hlt := hgt i hi'
              omega
            · exact hj'
          exact hdiff i hi' j hjms hji s
      · intro pre post n hsplit s t r hr
        cases pre with
        | nil =>
            rw [List.nil_append, List.cons.injEq] at hsplit
            obtain ⟨hmn, hmspost⟩ := hsplit
            subst hmn
            subst hmspost
            exact notMem_windowBad_of_notMem hinj hwinm s hr t
        | cons x pre' =>
            rw [List.cons_append, List.cons.injEq] at hsplit
            exact hwin pre' post n hsplit.2 s t r hr
      · refine cyclicThroughBaseAvoidance_cons hthrough ?_ hprefixm
        intro s b₀ b₁ r₀ hr₀
        exact notMem_throughBaseBad_of_notMem hthroughm s hr₀
          (Nat.zero_le _) b₀ b₁

/-- The combined exact design without reading the through-base clause. -/
theorem exists_separated_exponents_window_diff_exact
    {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hfam : ∀ s : Bool, a s ∈ D.fam s)
    {K : Set G} (hK : K.Finite) {T : Set G} (hT : T.Finite)
    {B : Set G} (hB : B.Finite) (W L : ℕ) :
    ∃ ms : List ℕ, ms.length = L ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, j < i → ∀ s : Bool, a s ^ (i - j) ∉ B) ∧
      ∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
        ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
          a s ^ n * GGT.RelLetter.listVal
            (blockWord (a false) (a true) t (post.take r))
            ∉ D.fam (!s) := by
  obtain ⟨ms, hlen, hnodup, hdeep, hsep, hdiff, hwin, -, -⟩ :=
    exists_separated_exponents_window_diff_through_exact
      hemb hinj hfam hK hT hB 1 W L
  exact ⟨ms, hlen, hnodup, hdeep, hsep, hdiff, hwin⟩

/-! ## The source-facing specialization -/

/-- **The combined exact design at the relative balls of a Hull core.**

Depth and deep differences are retained across both indices, rather than
weakened to the family member containing the power.  This is the form needed
when a same-side span begins with a letter of the opposite index. -/
theorem exists_relator_exponents_window_diff_through_exact
    {A : HullGeneratingSet G} {N : Subgroup G}
    (E : HypEmbeddedCore₂ A N) (rho eps diffRadius : ℕ)
    (baseLetter : G) (W L : ℕ) :
    ∃ ms : List ℕ, ms.length = L ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s t : Bool,
        E.lox s ^ m ∉ E.rel.relBall t rho ∧
          (E.lox s ^ m)⁻¹ ∉ E.rel.relBall t rho) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool,
        ∀ x ∈ E.rel.relBall s eps, ∀ x' ∈ E.rel.relBall s eps,
          x * E.lox s ^ i * x' ≠ E.lox s ^ j ∧
            x * E.lox s ^ i * x' ≠ (E.lox s ^ j)⁻¹) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, j < i → ∀ s t : Bool,
        E.lox s ^ (i - j) ∉ E.rel.relBall t diffRadius) ∧
      (∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
        ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
          E.lox s ^ n * GGT.RelLetter.listVal
              (blockWord (E.lox false) (E.lox true) t (post.take r))
            ∉ E.rel.fam (!s)) ∧
      CyclicThroughBaseAvoidance E.rel E.lox baseLetter W ms ∧
      BaseFirstAvoidance E.rel E.lox baseLetter W ms := by
  have hfam : ∀ s : Bool, E.lox s ∈ E.rel.fam s := by
    intro s
    rw [E.fam_eq]
    exact E.lox_mem s
  obtain ⟨ms, hlen, hnodup, hdeep, hsep, hdiff, hwin, hthrough, hbaseFirst⟩ :=
    exists_separated_exponents_window_diff_through_exact E.embedded
      (injective_pow_lox₂ E) hfam
      ((E.embedded.locallyFinite false rho).union
        (E.embedded.locallyFinite true rho))
      ((E.embedded.locallyFinite false eps).union
        (E.embedded.locallyFinite true eps))
      ((E.embedded.locallyFinite false diffRadius).union
        (E.embedded.locallyFinite true diffRadius))
      baseLetter W L
  refine ⟨ms, hlen, hnodup, ?_, ?_, ?_, hwin, hthrough, hbaseFirst⟩
  · intro m hm s t
    have h := hdeep m hm s
    cases t with
    | false =>
        exact ⟨fun hc => h.1 (Set.mem_union_left _ hc),
          fun hc => h.2 (Set.mem_union_left _ hc)⟩
    | true =>
        exact ⟨fun hc => h.1 (Set.mem_union_right _ hc),
          fun hc => h.2 (Set.mem_union_right _ hc)⟩
  · intro i hi j hj hij s x hx x' hx'
    have hxT : x ∈ E.rel.relBall false eps ∪ E.rel.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx
      | true => exact Set.mem_union_right _ hx
    have hx'T : x' ∈ E.rel.relBall false eps ∪ E.rel.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx'
      | true => exact Set.mem_union_right _ hx'
    exact hsep i hi j hj hij s x hxT x' hx'T
  · intro i hi j hj hji s t
    have h := hdiff i hi j hj hji s
    cases t with
    | false => exact fun hc => h (Set.mem_union_left _ hc)
    | true => exact fun hc => h (Set.mem_union_right _ hc)

end WindowDiffExact

end HullSC
end GroupApproximation
