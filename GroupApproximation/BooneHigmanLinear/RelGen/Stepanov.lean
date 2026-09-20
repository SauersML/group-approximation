import GroupApproximation.BooneHigmanLinear.RelGen.StepanovPair
import GroupApproximation.Meta.AxiomGuard

/-!
# Stepanov's theorem, part 2: L–S Theorem 4.4 in type A

Lane bh-pal-wire, k2-poly H.L3. `thm44 : Thm44Statement`. Let `S` be a parabolic set of roots
(closed, and containing `(i, j)` or `(j, i)` for every pair) whose special part `Σ_S` is
nonempty. Then `St̄(R, J) = 𝒵(Σ_S, R, J) = ⟨x(J), z_α(J, ·) : α ∈ Σ_S⟩`.

The proof follows L–S Remark 4.5. Put `G = 𝒵(Σ_S, R, J)`. By Theorem 4.2 it suffices that every
`z_ab ⊆ G`. The two pair rules of `RelGen.StepanovPair` spread `z ⊆ G` from `Σ_S` to all roots:

* `zIn_of_same`: if `(a, b), (b, a) ∈ S`, then since `Σ_S ≠ ∅` there is an `m` outside the block
  of `a`, and one pair rule applies;
* `zIn_all`: if `(b, a) ∈ Σ_S`, a third index `m` sits above `a`, below `b`, in the block of `a` or
  `b`, or strictly between them. Each position has a pair rule, possibly after `zIn_of_same`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] {J : Ideal R}

/-- **Same block.** If `(a, b), (b, a) ∈ S` and `Σ_S ≠ ∅`, then `z_ab ⊆ G`. -/
theorem zIn_of_same {S : I → I → Prop} (hS : IsParabolicRoots S)
    {G : Subgroup (SteinbergGroup I R)} (hx : xGroup I J ≤ G)
    (hΣ : ∀ a b : I, specialPart S a b → ZIn G J a b)
    (hne : ∃ c d : I, c ≠ d ∧ specialPart S c d) {a b : I} (hab : a ≠ b)
    (h1 : S a b) (h2 : S b a) : ZIn G J a b := by
  have hS' := hS
  obtain ⟨hcl, htot⟩ := hS'
  have hm : ∃ m, m ≠ a ∧ (¬S a m ∨ ¬S m a) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, d, hcd, hSc, hSd⟩ := hne
    by_cases hca : c = a
    · subst hca
      exact hSd (hcon d (fun e => hcd e.symm)).2
    · by_cases hda : d = a
      · subst hda
        exact hSd (hcon c hca).1
      · exact hSd (hcl d a c (fun e => hcd e.symm) (hcon d hda).2 (hcon c hca).1)
  obtain ⟨m, hma, hm'⟩ := hm
  have hmb : m ≠ b := by
    rintro rfl
    rcases hm' with h | h
    · exact h h1
    · exact h h2
  rcases hm' with hnam | hnma
  · -- `m` lies below `a`: `(m, a), (m, b) ∈ Σ_S`.
    have hSma : S m a := (htot m a hma).resolve_right hnam
    have hSmb : S m b := hcl m a b hmb hSma h1
    have hnbm : ¬S b m := fun h => hnam (hcl a b m (fun e => hma e.symm) h1 h)
    exact z_mem_of_row_pair hx (fun e => hma e.symm) (fun e => hmb e.symm)
      (hΣ _ _ (And.intro hSma hnam)) (hΣ _ _ (And.intro hSmb hnbm))
  · -- `m` lies above `a`: `(a, m), (b, m) ∈ Σ_S`.
    have hSam : S a m := (htot a m (fun e => hma e.symm)).resolve_right hnma
    have hSbm : S b m := hcl b a m (fun e => hmb e.symm) h2 hSam
    have hnmb : ¬S m b := fun h => hnma (hcl m b a hma h h2)
    exact z_mem_of_col_pair hx (fun e => hma e.symm) (fun e => hmb e.symm)
      (hΣ _ _ (And.intro hSam hnma)) (hΣ _ _ (And.intro hSbm hnmb))

/-- **Every root.** Given a third index and `Σ_S ≠ ∅`, `z_ab ⊆ G` for every `a ≠ b`. -/
theorem zIn_all {S : I → I → Prop} (hS : IsParabolicRoots S)
    {G : Subgroup (SteinbergGroup I R)} (hx : xGroup I J ≤ G)
    (hΣ : ∀ a b : I, specialPart S a b → ZIn G J a b) (third : ThirdIndex I)
    (hne : ∃ c d : I, c ≠ d ∧ specialPart S c d) {a b : I} (hab : a ≠ b) : ZIn G J a b := by
  have hS' := hS
  obtain ⟨hcl, htot⟩ := hS'
  by_cases h1 : S a b
  · by_cases h2 : S b a
    · exact zIn_of_same hS hx hΣ hne hab h1 h2
    · exact hΣ _ _ (And.intro h1 h2)
  · -- `(b, a) ∈ Σ_S`.
    have hba : S b a := (htot a b hab).resolve_left h1
    obtain ⟨m, ham, hbm⟩ := third a b
    have hma : m ≠ a := fun e => ham e.symm
    have hmb : m ≠ b := fun e => hbm e.symm
    by_cases hA : S a m ∧ ¬S m a
    · -- `m` above `a`.
      have hSbm : S b m := hcl b a m hbm hba hA.1
      have hnmb : ¬S m b := fun h => hA.2 (hcl m b a hma h hba)
      exact z_mem_of_col_pair hx ham hbm (hΣ _ _ (And.intro hA.1 hA.2))
        (hΣ _ _ (And.intro hSbm hnmb))
    · by_cases hB : S m b ∧ ¬S b m
      · -- `m` below `b`.
        have hSma : S m a := hcl m b a hma hB.1 hba
        have hnam : ¬S a m := fun h => h1 (hcl a m b hab h hB.1)
        exact z_mem_of_row_pair hx ham hbm (hΣ _ _ (And.intro hSma hnam))
          (hΣ _ _ (And.intro hB.1 hB.2))
      · by_cases hSam : S a m
        · -- `m` in the block of `a`.
          have hSma : S m a := by
            by_contra h
            exact hA ⟨hSam, h⟩
          have hSbm : S b m := hcl b a m hbm hba hSam
          have hnmb : ¬S m b := fun h => h1 (hcl a m b hab hSam h)
          exact z_mem_of_col_pair hx ham hbm (zIn_of_same hS hx hΣ hne ham hSam hSma)
            (hΣ _ _ (And.intro hSbm hnmb))
        · have hSma : S m a := (htot m a hma).resolve_right hSam
          by_cases hSmb : S m b
          · -- `m` in the block of `b`.
            have hSbm : S b m := by
              by_contra h
              exact hB ⟨hSmb, h⟩
            exact z_mem_of_row_pair hx ham hbm (hΣ _ _ (And.intro hSma hSam))
              (zIn_of_same hS hx hΣ hne hmb hSmb hSbm)
          · -- `m` strictly between `b` and `a`.
            have hSbm : S b m := (htot b m hbm).resolve_right hSmb
            have hzam : ZIn G J a m := z_mem_of_row_pair hx hab hmb
              (hΣ _ _ (And.intro hba h1)) (hΣ _ _ (And.intro hSbm hSmb))
            exact z_mem_of_col_pair hx ham hbm hzam (hΣ _ _ (And.intro hSbm hSmb))

/-- **L–S Theorem 4.4 (Stepanov), type A.** -/
theorem thm44 : Thm44Statement := by
  intro I _ _ third S hS hne R _ J
  have hx : xGroup I J ≤ zGen I J (specialPart S) := xGroup_le_zGen _
  have hΣ : ∀ a b : I, specialPart S a b → ZIn (zGen I J (specialPart S)) J a b :=
    fun a b h hab s ξ hs => z_mem_zGen hab h hs ξ
  obtain ⟨c, d, hcd, hsp⟩ := hne
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_))
  · rw [thm42 I third R J, Subgroup.closure_le]
    rintro _ ⟨a, b, hab, s, ξ, -, hs, rfl⟩
    exact zIn_all hS hx hΣ third ⟨c, d, hcd, hsp⟩ hab hab s ξ hs
  · rintro _ ⟨i, j, hij, s, hs, rfl⟩
    exact mem_relKer_of_x hij hs
  · rintro _ ⟨i, j, hij, s, ξ, -, hs, rfl⟩
    exact mem_relKer_of_z hij hs ξ

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.thm44

end GroupApproximation.BooneHigmanLinear.RelGen
