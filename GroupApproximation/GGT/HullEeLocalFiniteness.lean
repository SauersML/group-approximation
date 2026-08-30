import GroupApproximation.GGT.DGOCorollary427Full
import GroupApproximation.GGT.DGOIsolatedComponentWitness
import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.HullEeAdjacent
import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.GGT.OsinTheorem54SepSixBound

/-!
# Local finiteness in Hull's Lemma ee

This file discharges `EeLocalFiniteness`.  For a fixed radius `n`, an element of
the enlarged relative ball is represented by a shortest avoiding word.  Read in
the relative Cayley graph for `E`, every letter from `E` is a one-letter isolated
component of the word closed by one final base edge.  The isolated-component
bound therefore puts all such letters in one finite relative ball `F_n` of `E`.

Adjoining `F_n` to the old base is a finite symmetric change, so full DGO
Corollary 4.27 preserves hyperbolic embeddedness.  The shortest word is already
a word over this finite enlargement, giving the required ball inclusion.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-- Adjoin an inversion-stable set to the base. -/
def adjoinSymmetricSet (D : RelGenSet G Λ) (F : Set G)
    (hF : ∀ x ∈ F, x⁻¹ ∈ F) : RelGenSet G Λ where
  base := D.base ∪ F
  fam := D.fam
  symmetricGenerating := by
    constructor
    · rintro x ((hx | hx) | hx)
      · rcases D.symmetricGenerating.inv_mem x (Or.inl hx) with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
      · exact Or.inl (Or.inr (hF x hx))
      · rcases D.symmetricGenerating.inv_mem x (Or.inr hx) with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono fun x hx =>
        hx.elim (fun h => Or.inl (Or.inl h)) Or.inr

@[simp] theorem adjoinSymmetricSet_base (D : RelGenSet G Λ) (F : Set G)
    (hF : ∀ x ∈ F, x⁻¹ ∈ F) :
    (D.adjoinSymmetricSet F hF).base = D.base ∪ F := rfl

@[simp] theorem adjoinSymmetricSet_fam (D : RelGenSet G Λ) (F : Set G)
    (hF : ∀ x ∈ F, x⁻¹ ∈ F) :
    (D.adjoinSymmetricSet F hF).fam = D.fam := rfl

end RelGenSet

namespace OsinComponents

variable {G : Type u} [Group G] {Λ : Type w}

/-- Every `E`-letter in a shortest radius-`n` word lies in the common finite
relative ball supplied by the isolated-component estimate. -/
theorem mem_eBall_of_base_mem_minimal_word
    {D : RelGenSet G Λ} {E : Subgroup G} {DE : RelGenSet G Unit}
    (hbase : DE.base = D.alphabet.carrier) (hfam : DE.fam = fun _ => E)
    {lam : Λ} {n R : ℕ} {h : G} {w : List (RelLetter G Λ)}
    (hhfam : h ∈ D.fam lam)
    (hlet : ∀ a ∈ w, (relGenSetAddSubgroup D E).IsLetter a)
    (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom (relGenSetAddSubgroup D E).fam lam w 1)
    (hlen : w.length ≤ n)
    (hmin : ∀ v : List (RelLetter G Λ),
      (∀ a ∈ v, (relGenSetAddSubgroup D E).IsLetter a) →
        RelLetter.listVal v = h →
          AvoidsFrom (relGenSetAddSubgroup D E).fam lam v 1 →
            w.length ≤ v.length)
    (hbound : ∀ (v : G) (u : List (RelLetter G Unit)),
      IsQuasiGeodesicPolygon DE 1 ((n + 1 : ℕ) : ℝ) 1 v u →
      ∀ (nu : Unit) (i k : ℕ), IsComp nu u i k →
        IsIsolated DE.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ DE.relBall nu R)
    {x : G} (hxE : x ∈ E) (hxw : RelLetter.base x ∈ w) :
    x ∈ DE.relBall () R := by
  let u : List (RelLetter G Unit) := w.map (transferLetter E)
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hxw
  have hju : j < u.length := by simpa [u] using hj
  have hjcomp : (u[j]'hju).IsCompOf () := by
    rw [show u[j] = transferLetter E (w[j]'hj) by
      exact getElem_map_transferLetter w hj hju, hjx]
    exact isCompOf_transferLetter_base_of_mem hxE
  obtain ⟨i, k, hij, hjk, hcomp⟩ :=
    exists_isComp_of_isCompOf () u j hju hjcomp
  have hk : k = i + 1 := by
    exact isComp_transfer_eq_succ hlet hval hav hmin hcomp
  have hji : j = i := by omega
  subst j
  subst k
  have htranslet : ∀ a ∈ u, DE.IsLetter a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isLetter_transferLetter hbase hfam (hlet b hb)
  have hhinv : h⁻¹ ∈ DE.base := by
    rw [hbase]
    exact D.alphabet.symmetricGenerating.inv_mem h
      (D.fam_subset_alphabet lam hhfam)
  let q : List (RelLetter G Unit) := cycleWord u h⁻¹
  have hqlet : ∀ a ∈ q, DE.IsLetter a :=
    isLetter_cycleWord htranslet hhinv
  have huval : RelLetter.listVal u = h := by
    dsimp [u]
    rw [listVal_map_transferLetter, hval]
  have hqclosed : RelLetter.listVal q = 1 := by
    dsimp [q]
    rw [listVal_cycleWord, huval, mul_inv_cancel]
  have hqpoly0 := isQuasiGeodesicPolygon_of_closed DE 1 hqlet hqclosed
  have hqlen : q.length ≤ n + 1 := by
    dsimp [q]
    rw [length_cycleWord]
    dsimp [u]
    rw [length_map_transferLetter]
    omega
  have hqpoly : IsQuasiGeodesicPolygon DE 1 ((n + 1 : ℕ) : ℝ) 1 1 q := by
    refine isQuasiGeodesicPolygon_mono_defect DE ?_ hqpoly0
    exact_mod_cast hqlen
  have hisoOpen : IsIsolated DE.fam () 1 u i := by
    exact isIsolated_transfer_of_minimal hfam hlet hval hav hmin ⟨i + 1, hcomp⟩
  have hcompCycle : IsComp () q i (i + 1) := by
    exact isComp_cycleWord h⁻¹ hcomp
  have hisoCycle : IsIsolated DE.fam () 1 q i := by
    exact isIsolated_cycleWord h⁻¹ hisoOpen
  have hb := hbound 1 q hqpoly () i (i + 1) hcompCycle hisoCycle
  have hiu : i < u.length := hcomp.1.trans_le hcomp.2.1
  have hspan : (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q (i + 1) = x := by
    calc
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q (i + 1) =
          (vertex (1 : G) u i)⁻¹ * vertex (1 : G) u (i + 1) := by
            rw [show q = cycleWord u h⁻¹ by rfl,
              vertex_cycleWord u h⁻¹ 1 (le_of_lt hiu),
              vertex_cycleWord u h⁻¹ 1 (by omega)]
      _ = (u[i]'hiu).val := by
        rw [vertex_succ u 1 i hiu]
        group
      _ = x := by
        rw [show u[i] = transferLetter E (w[i]'hj) by
          exact getElem_map_transferLetter w hj hiu,
          val_transferLetter, hjx]
        rfl
  rwa [hspan] at hb

end OsinComponents

namespace RelGenSet

/-- **Hull's clause (b).**  Moving a hyperbolically embedded subgroup from the
family side of the alphabet into the base preserves local finiteness of every
old peripheral subgroup. -/
theorem eeLocalFiniteness : EeLocalFiniteness.{u, w} := by
  intro G _ Λ D hD E hE lam n
  obtain ⟨DE, hbase, hfam, hDE⟩ := hE
  obtain ⟨δ, hδ⟩ := exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded DE hDE
  have hsymmDE : ∀ x ∈ DE.base, x⁻¹ ∈ DE.base := by
    intro x hx
    rw [hbase] at hx ⊢
    exact D.alphabet.symmetricGenerating.inv_mem x hx
  obtain ⟨R, hR⟩ := OsinComponents.exists_isolatedComponentBound_nGon
    DE hsymmDE (n + 1) hδ 1
  let F : Set G := DE.relBall () R
  have hFfin : F.Finite := hDE.locallyFinite () R
  have hFsymm : ∀ x ∈ F, x⁻¹ ∈ F := by
    intro x hx
    exact OsinComponents.relBall_inv DE () hsymmDE hx
  let Dn : RelGenSet G Λ := D.adjoinSymmetricSet F hFsymm
  have hdiff : ((D.base \ Dn.base) ∪ (Dn.base \ D.base)).Finite := by
    refine (Set.finite_empty.subset ?_).union (hFfin.subset ?_)
    · rintro x ⟨hx, hnot⟩
      apply hnot
      change x ∈ D.base ∪ F
      exact Or.inl hx
    · rintro x ⟨hx, hnot⟩
      change x ∈ D.base ∪ F at hx
      exact hx.resolve_left hnot
  have hDn : Dn.IsHyperbolicallyEmbedded :=
    (dgoCorollary427 G Λ D Dn rfl hdiff).mp hD
  exact (hDn.locallyFinite lam n).subset fun h hh => by
    obtain ⟨w, hlet, hval, hav, hlen, hmin⟩ :=
      exists_minimal_word_of_mem_relBall hh
    have hletDn : ∀ a ∈ w, Dn.IsLetter a := by
      intro a ha
      cases a with
      | base x =>
          rcases hlet (RelLetter.base x) ha with hx | hx
          · change x ∈ D.base ∪ F
            exact Or.inl hx
          · change x ∈ D.base ∪ F
            refine Or.inr ?_
            exact OsinComponents.mem_eBall_of_base_mem_minimal_word hbase hfam
              hh.1 hlet hval hav hlen hmin hR (SetLike.mem_coe.mp hx) ha
      | comp mu x =>
          show x ∈ D.fam mu
          exact hlet (RelLetter.comp mu x) ha
    refine ⟨show h ∈ D.fam lam from hh.1, w, hletDn, hval, ?_, hlen⟩
    simpa [Dn] using hav

/-- **Hull's one-step alphabet enlargement, unconditionally.**  The
hyperbolicity clause is supplied by the alphabet identity in
`eeOneStep_of_localFiniteness`; the local-finiteness clause is the theorem
above. -/
theorem eeOneStep : EeOneStep.{u, w} :=
  eeOneStep_of_localFiniteness eeLocalFiniteness

end RelGenSet

end GGT
end GroupApproximation
