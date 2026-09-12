import GroupApproximation.GGT.HullSCLemma51FaceRelation
import GroupApproximation.GGT.HullSCLemma51LetterPullbackAtoms

/-!
# Closing one step of the letter pullback in the quotient

One move of the letter pullback turns the lifted quotient-null word into a shorter one.  Either
the move already expresses the unknown lift `h` (the `done` alternative), or the new word has one
*designated* peripheral letter `z`, read at a vertex of the base coset `q(H_λ)` (in the
coordinates of a representative `c`), with value `x · h^{±1} · y` for bounded products `x, y`, and
every other peripheral letter read at that coset has a value in `q '' boundedProducts A N`.

`PullbackOutcome` records the two alternatives, with the word read after `z`.
`mem_image_of_pullbackOutcome` closes the step:

* the word read after `z` has value `q(z)⁻¹ ∈ q(H_λ)`, so the face relation in the quotient
  (`listVal_mem_boundedProducts_of_cosetLettersAt_from`) writes `q(z)⁻¹` as a bounded product
  of images of bounded products and of elements of the quotient relative ball of the word's
  length;
* the ball part is the induction hypothesis `hball`;
* the designated value then isolates `q h`.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **A value with the unknown `h` or its inverse between two bounded products.** -/
def DesignatedValue (A : Set G) (N : ℕ) (h z : G) : Prop :=
  ∃ x y : G, x ∈ boundedProducts A N ∧ y ∈ boundedProducts A N ∧
    (z = x * h * y ∨ z = x * h⁻¹ * y)

/-- **The outcome of one move.**  Either `q h` is already the image of a bounded product, or the
new quotient-null word `u₁ ++ z :: u₂` (with `(u₂ ++ u₁).length ≤ m`) carries a designated
letter `z` read at a vertex of the coset `c · q(H_λ)`, and all other peripheral letters read at
that coset, along the word read after `z`, have values in `q '' boundedProducts A N`. -/
def PullbackOutcome (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    (lam : Lambda) (A : Set G) (N : ℕ) (h : G) (m : ℕ) : Prop :=
  q h ∈ q '' boundedProducts A N ∨
    ∃ (u₁ u₂ : List (GGT.RelLetter G Lambda)) (z : GGT.RelLetter G Lambda) (c : Q),
      (∀ a ∈ u₁ ++ z :: u₂, D.IsLetter a) ∧
      q (GGT.RelLetter.listVal (u₁ ++ z :: u₂)) = 1 ∧
      (u₂ ++ u₁).length ≤ m ∧
      GGT.RelLetter.IsCompOf lam z ∧
      c⁻¹ * q (GGT.RelLetter.listVal u₁) ∈ (D.mapSurjective q hq).fam lam ∧
      DesignatedValue A N h z.val ∧
      CosetLettersAt (D.mapSurjective q hq) lam (q '' boundedProducts A N) c
        (q (GGT.RelLetter.listVal u₁ * z.val)) ((u₂ ++ u₁).map (GGT.RelLetter.mapHom q))

/-- **One step closes in the quotient.**  From an outcome whose word read after the designated
letter has length at most `m`, and the ball bound at radius `m`, the lift `q h` is the image of a
bounded product of `B` with at most `(m + 3) · max N M` factors. -/
theorem mem_image_of_pullbackOutcome (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {lam : Lambda} {A B : Set G} {N M m : ℕ} {h : G}
    (hAB : A ⊆ B) (hBinv : ∀ x ∈ B, x⁻¹ ∈ B)
    (hball : (D.mapSurjective q hq).relBall lam m ⊆ q '' boundedProducts B M)
    (hout : PullbackOutcome D q hq lam A N h m) :
    q h ∈ q '' boundedProducts B ((m + 3) * max N M) := by
  have hNK : N ≤ max N M := le_max_left N M
  have hMK : M ≤ max N M := le_max_right N M
  have hK3 : max N M ≤ (m + 3) * max N M :=
    le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  rcases hout with ⟨t, ht, hqt⟩ |
    ⟨u₁, u₂, z, c, hlet, hnull, hlen, hcomp, hzcoset, hdes, hletters⟩
  · exact ⟨t, boundedProducts_mono hAB (le_trans hNK hK3) ht, hqt⟩
  set K := max N M with hK
  have hzmem : z ∈ u₁ ++ z :: u₂ := List.mem_append_right _ List.mem_cons_self
  have hzH : z.val ∈ D.fam lam := val_mem_fam_of_isCompOf (hlet z hzmem) hcomp
  have hqzH : q z.val ∈ (D.mapSurjective q hq).fam lam := Subgroup.mem_map_of_mem q hzH
  have hx : (q (GGT.RelLetter.listVal u₁ * z.val))⁻¹ * c ∈
      (D.mapSurjective q hq).fam lam := by
    have h1 : c⁻¹ * q (GGT.RelLetter.listVal u₁ * z.val) ∈
        (D.mapSurjective q hq).fam lam := by
      rw [map_mul, ← mul_assoc]
      exact mul_mem hzcoset hqzH
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hletters' := hletters.of_rep hx
  have hrestLetters : ∀ a ∈ (u₂ ++ u₁).map (GGT.RelLetter.mapHom q),
      (D.mapSurjective q hq).IsLetter a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    apply GGT.RelGenSet.isLetter_mapHom_mapSurjective D q hq
    apply hlet
    rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
    · exact List.mem_append_left _ hb
  have hrestVal : GGT.RelLetter.listVal ((u₂ ++ u₁).map (GGT.RelLetter.mapHom q)) =
      (q z.val)⁻¹ := by
    rw [GGT.RelLetter.listVal_map_mapHom, GGT.OsinComponents.listVal_append, map_mul]
    have e := hnull
    rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons, map_mul,
      map_mul] at e
    have e' : q z.val * q (GGT.RelLetter.listVal u₂) = (q (GGT.RelLetter.listVal u₁))⁻¹ :=
      eq_inv_of_mul_eq_one_right e
    calc q (GGT.RelLetter.listVal u₂) * q (GGT.RelLetter.listVal u₁)
        = (q z.val)⁻¹ * (q z.val * q (GGT.RelLetter.listVal u₂)) *
            q (GGT.RelLetter.listVal u₁) := by group
      _ = (q z.val)⁻¹ := by rw [e']; group
  have hrestFam : GGT.RelLetter.listVal ((u₂ ++ u₁).map (GGT.RelLetter.mapHom q)) ∈
      (D.mapSurjective q hq).fam lam := by
    rw [hrestVal]
    exact inv_mem hqzH
  have hprod := listVal_mem_boundedProducts_of_cosetLettersAt_from (D.mapSurjective q hq) lam
    (q '' boundedProducts A N) (q (GGT.RelLetter.listVal u₁ * z.val)) hrestLetters hrestFam
    hletters'
  rw [List.length_map, hrestVal] at hprod
  have hfactor : q '' boundedProducts A N ∪
      (D.mapSurjective q hq).relBall lam (u₂ ++ u₁).length ⊆ q '' boundedProducts B K := by
    rintro y (⟨t, ht, rfl⟩ | hy)
    · exact ⟨t, boundedProducts_mono hAB hNK ht, rfl⟩
    · obtain ⟨t, ht, hqt⟩ := hball (GGT.OsinComponents.relBall_mono_radius _ lam hlen hy)
      exact ⟨t, boundedProducts_mono (fun _ hb => hb) hMK ht, hqt⟩
  have hprod' : (q z.val)⁻¹ ∈ q '' boundedProducts B ((m + 1) * K) := by
    have h1 := boundedProducts_mono hfactor (le_refl _) hprod
    obtain ⟨t, ht, hqt⟩ := image_boundedProducts_subset q (boundedProducts B K) _ h1
    refine ⟨t, ?_, hqt⟩
    exact boundedProducts_mono (fun _ hb => hb) (Nat.mul_le_mul_right K (by omega))
      (boundedProducts_boundedProducts_subset B K _ ht)
  obtain ⟨t, ht, hqt⟩ := hprod'
  obtain ⟨x, y, hx₁, hy₁, hz | hz⟩ := hdes
  · refine ⟨x⁻¹ * t⁻¹ * y⁻¹, ?_, ?_⟩
    · have hxB : x⁻¹ ∈ boundedProducts B K :=
        inv_mem_boundedProducts hBinv (boundedProducts_mono hAB hNK hx₁)
      have hyB : y⁻¹ ∈ boundedProducts B K :=
        inv_mem_boundedProducts hBinv (boundedProducts_mono hAB hNK hy₁)
      have htB : t⁻¹ ∈ boundedProducts B ((m + 1) * K) := inv_mem_boundedProducts hBinv ht
      exact boundedProducts_mono (fun _ hb => hb) (le_of_eq (by ring))
        (mul_mem_boundedProducts (mul_mem_boundedProducts hxB htB) hyB)
    · rw [map_mul, map_mul, map_inv, map_inv, map_inv, hqt, inv_inv, hz, map_mul, map_mul]
      group
  · refine ⟨y * t * x, ?_, ?_⟩
    · have hxB : x ∈ boundedProducts B K := boundedProducts_mono hAB hNK hx₁
      have hyB : y ∈ boundedProducts B K := boundedProducts_mono hAB hNK hy₁
      exact boundedProducts_mono (fun _ hb => hb) (le_of_eq (by ring))
        (mul_mem_boundedProducts (mul_mem_boundedProducts hyB ht) hxB)
    · rw [map_mul, map_mul, hqt, hz, map_mul, map_mul, map_inv]
      group

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.mem_image_of_pullbackOutcome
