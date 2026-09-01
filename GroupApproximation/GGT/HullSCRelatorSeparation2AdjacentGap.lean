import GroupApproximation.GGT.HullSCRelatorSeparation2PublishedGap

/-! Two adjacent published-gap matches with arbitrary relative short sides. -/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- A prescribed deep, seam-clean source component has a bounded matched pair
on the opposite exact prefix. -/
theorem exists_exact_cleanSource_publishedGap_relativeSides
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
        ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
        RelatorBlockCountAt₂ E [baseLetter] ms 1 → Even ms.length →
        1 + blockConst [baseLetter] 1 ≤ W →
        ∀ {v q tail v' s tail' : List (GGT.RelLetter G Bool)},
          RelWord.Sym
            (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
          v = q ++ tail →
          RelWord.Sym
            (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v' →
          v' = s ++ tail' →
          ∀ (p r : List (GGT.RelLetter G Bool)),
            GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
              GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
            0 < r.length →
            (∀ a ∈ p ++ q ++ r ++ GGT.OsinComponents.revWord s,
              E.rel.IsLetter a) →
            (∀ t : ℕ, t < 4 → ∀ x y : ℕ,
              GGT.OsinComponents.fourGonCut p q r s t ≤ x → x ≤ y →
              y ≤ GGT.OsinComponents.fourGonCut p q r s (t + 1) →
              ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ) ≤
                ((wordDist E.rel.alphabet.carrier
                  (GGT.OsinComponents.vertex (1 : G)
                    (p ++ q ++ r ++ GGT.OsinComponents.revWord s) x)
                  (GGT.OsinComponents.vertex (1 : G)
                    (p ++ q ++ r ++ GGT.OsinComponents.revWord s) y) : ℕ) : ℝ)) →
            C * 4 ≤ rho → C * 4 ≤ eps →
            ∀ (lam : Bool) (i : ℕ), 0 < i → i + 1 < q.length →
              GGT.OsinComponents.IsComp lam q i (i + 1) →
              (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
                  GGT.OsinComponents.vertex (1 : G) q (i + 1) ∉
                    E.rel.relBall lam rho →
              (∀ m, GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
                GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) m →
                ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
                    m = p.length + q.length + b) ∨
                  m = p.length + q.length + r.length + (s.length - 1))) →
              ∃ j : ℕ, 1 < j ∧ j ≤ s.length ∧
                GGT.OsinComponents.IsComp lam s (j - 1) j ∧
                (∃ h : G, h ∈ E.rel.fam lam ∧
                  GGT.RelLetter.listVal p *
                      GGT.OsinComponents.vertex (1 : G) q i * h =
                    GGT.OsinComponents.vertex (1 : G) s j) ∧
                ((GGT.OsinComponents.vertex (1 : G) s (j - 1))⁻¹ *
                    (GGT.RelLetter.listVal p *
                      GGT.OsinComponents.vertex (1 : G) q i)
                      ∈ E.rel.relBall lam eps) ∧
                ((GGT.RelLetter.listVal p *
                      GGT.OsinComponents.vertex (1 : G) q (i + 1))⁻¹ *
                    GGT.OsinComponents.vertex (1 : G) s j
                      ∈ E.rel.relBall lam eps) := by
  obtain ⟨Cf, hCf, hf⟩ :=
    GGT.OsinComponents.exists_other_component_of_deep_fourGon_relativeSides
      E.rel false hsymm hδ
  obtain ⟨Ct, hCt, ht⟩ :=
    GGT.OsinComponents.exists_other_component_of_deep_fourGon_relativeSides
      E.rel true hsymm hδ
  obtain ⟨Cg, hCg, hgap⟩ := exists_publishedGap_pair_relativeSides E.rel hsymm hδ
  let C := max (max Cf Ct) Cg
  refine ⟨C, lt_of_lt_of_le hCf (le_trans (Nat.le_max_left _ _)
    (Nat.le_max_left _ _)), ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign hcount heven hW
    v q tail v' s tail' hv hq hv' hs p r hclose hr0 hlet hqg hrho heps
    lam i hi hiend hicomp hideep hclean
  have hpoly := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon
    p q r s E.rel hlet hclose hqg
  have hR : (if lam then Ct else Cf) * 4 ≤ rho := by
    cases lam <;> dsimp <;> apply le_trans _ hrho
    · exact Nat.mul_le_mul_right 4
        (le_trans (Nat.le_max_left Cf Ct) (Nat.le_max_left _ Cg))
    · exact Nat.mul_le_mul_right 4
        (le_trans (Nat.le_max_right Cf Ct) (Nat.le_max_left _ Cg))
  have hraw : ∃ n : ℕ, n ≠ p.length + i ∧
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) n ∧
      (n < p.length ∨
        (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) ∧
      ∃ h : G, h ∈ E.rel.fam lam ∧
        GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i * h =
          GGT.OsinComponents.vertex (1 : G)
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s) n := by
    cases lam with
    | false => exact hf rho p q r s i (i + 1) hR hi hiend hicomp hpoly hideep
    | true => exact ht rho p q r s i (i + 1) hR hi hiend hicomp hpoly hideep
  obtain ⟨n, hn, hnstart, hnloc, h, hh, heq⟩ := hraw
  have hnconn : GGT.OsinComponents.Connected E.rel.fam lam 1
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i) n := by
    show (GGT.OsinComponents.vertex (1 : G)
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i))⁻¹ *
      GGT.OsinComponents.vertex (1 : G)
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) n ∈ E.rel.fam lam
    rw [GGT.OsinComponents.vertex_fourGon_side p q r s 1 (by omega), one_mul, ← heq]
    have hcancel :
        (GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
          (GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i * h) = h := by
      group
    rw [hcancel]
    exact hh
  rcases hnloc with hp | hqside | hr | hside
  · exact False.elim (hclean n hnstart hnconn (Or.inl (Or.inl hp)))
  · obtain ⟨i', hi', heq'⟩ := hqside
    by_cases hi'len : i' < q.length
    · by_cases hieq : i' = i
      · exact False.elim (hn (by omega))
      · exact False.elim (exactPrefix_not_connected_sameSide_relativeSides
          E hdesign hcount heven hW hv hq p r s lam i hicomp i' hi'len hieq
          (by rw [← heq']; exact hnstart) (by rw [← heq']; exact hnconn))
    · exact False.elim (hclean n hnstart hnconn
        (Or.inl (Or.inr ⟨0, hr0, by omega⟩)))
  · obtain ⟨b, hb, heq'⟩ := hr
    exact False.elim (hclean n hnstart hnconn
      (Or.inl (Or.inr ⟨b, hb, heq'⟩)))
  · obtain ⟨j, hj, heq'⟩ := hside
    have hjne : j ≠ 1 := fun hjeq ↦
      hclean n hnstart hnconn (Or.inr (by rw [heq', hjeq]))
    have hj0 : 0 < j := by
      obtain ⟨k, hk⟩ := hnstart
      have hlt := lt_of_lt_of_le hk.1 hk.2.1
      rw [GGT.OsinComponents.length_fourGon] at hlt
      omega
    have hjstart : GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - j)) := by
      rw [← heq']; exact hnstart
    obtain ⟨j0, x, hx⟩ := exists_comp_letter_of_secondLongSide_start hj hjstart
    have hxv : v'[j - 1]? = some (GGT.RelLetter.comp lam x) := by
      rw [hs, List.getElem?_append_left (by omega : j - 1 < s.length)]
      exact hx
    have hcompV := isComp_of_sym_exactRelator E hv' hxv
    rw [hs] at hcompV
    have hcompS0 := isComp_prefix hcompV (by omega : j - 1 + 1 ≤ s.length)
    have hcompS : GGT.OsinComponents.IsComp lam s (j - 1) j := by
      convert hcompS0 using 1 <;> omega
    have hconnector := GGT.OsinComponents.exists_connector_fourGon E.rel lam
      p q r s hclose (by omega : i ≤ q.length) (by rw [← heq']; exact hnconn)
    have hqexclude : ∀ i' : ℕ, i' < q.length → i' ≠ i →
        GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
        (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q i' ∉ E.rel.fam lam := by
      intro i' hi' hne hstart hmem
      exact exactPrefix_not_connected_sameSide_relativeSides E hdesign hcount
        heven hW hv hq p r s lam i hicomp i' hi' hne hstart
          ((GGT.OsinComponents.connected_fourGon_side_iff E.rel lam p q r s
            (by omega) (by omega)).mpr hmem)
    have hssexclude : ∀ m : ℕ, m ≤ s.length → m ≠ j →
        GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + q.length + r.length + (s.length - m)) →
        (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) s m ∉ E.rel.fam lam := by
      intro m hm hne hstart
      exact exactPrefix_not_connected_oppositeSide_relativeSides E hdesign
        hcount heven hW hv' hs p q r lam j m
          ⟨j - 1, by omega, hcompS⟩ hm hne hstart
    have hCgEps : Cg * 4 ≤ eps := le_trans
      (Nat.mul_le_mul_right 4 (Nat.le_max_right (max Cf Ct) Cg)) heps
    obtain ⟨hc, hcmem, hceq⟩ := hconnector
    have hconn := GGT.OsinComponents.connected_of_connector E.rel lam p q r s
      hclose (by omega) j hcmem hceq
    obtain ⟨hgap0, hgap1⟩ := hgap lam p q r s i j hclose hlet hqg hi
      hiend hicomp (by omega) hj hr0 hcompS hjstart hconn hqexclude hssexclude
      (fun m hmstart hmconn hshort ↦ hclean m hmstart hmconn (Or.inl hshort))
    exact ⟨j, by omega, hj, hcompS, ⟨hc, hcmem, hceq⟩,
      GGT.OsinComponents.relBall_mono_radius E.rel lam hCgEps hgap0,
      GGT.OsinComponents.relBall_mono_radius E.rel lam hCgEps hgap1⟩

/-- Two adjacent bounded matches extracted from the finite exact-prefix grid. -/
def ExactPublishedAdjacentGapOutput
    (E : HypEmbeddedCore₂ A N) (C bn : ℕ) : Prop :=
  ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
    ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
    RelatorBlockCountAt₂ E [baseLetter] ms 1 → Even ms.length →
    1 + blockConst [baseLetter] 1 ≤ W →
    ∀ {v q tail v' s tail' : List (GGT.RelLetter G Bool)},
      RelWord.Sym
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
      v = q ++ tail →
      RelWord.Sym
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v' →
      v' = s ++ tail' →
      ∀ (p r : List (GGT.RelLetter G Bool)),
        GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
          GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
        0 < r.length →
        (∀ a ∈ p ++ q ++ r ++ GGT.OsinComponents.revWord s,
          E.rel.IsLetter a) →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ,
          GGT.OsinComponents.fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ GGT.OsinComponents.fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ) ≤
            ((wordDist E.rel.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G)
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s) x)
              (GGT.OsinComponents.vertex (1 : G)
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s) y) : ℕ) : ℝ)) →
        C * 4 ≤ rho → C * 4 ≤ eps →
        2 * (p.length + r.length + 3) + 2 ≤ q.length →
        ∃ (lam lam' : Bool) (i j j' : ℕ),
          0 < i ∧ i + 2 < q.length ∧
          GGT.OsinComponents.IsComp lam q i (i + 1) ∧
          GGT.OsinComponents.IsComp lam' q (i + 1) (i + 2) ∧
          1 < j ∧ j ≤ s.length ∧
          GGT.OsinComponents.IsComp lam s (j - 1) j ∧
          1 < j' ∧ j' ≤ s.length ∧
          GGT.OsinComponents.IsComp lam' s (j' - 1) j' ∧
          (∃ h : G, h ∈ E.rel.fam lam ∧
            GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i * h =
              GGT.OsinComponents.vertex (1 : G) s j) ∧
          (∃ h : G, h ∈ E.rel.fam lam' ∧
            GGT.RelLetter.listVal p *
                GGT.OsinComponents.vertex (1 : G) q (i + 1) * h =
              GGT.OsinComponents.vertex (1 : G) s j') ∧
          ((GGT.OsinComponents.vertex (1 : G) s (j - 1))⁻¹ *
              (GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i)
                ∈ E.rel.relBall lam eps) ∧
          ((GGT.RelLetter.listVal p *
                GGT.OsinComponents.vertex (1 : G) q (i + 1))⁻¹ *
              GGT.OsinComponents.vertex (1 : G) s j
                ∈ E.rel.relBall lam eps) ∧
          ((GGT.OsinComponents.vertex (1 : G) s (j' - 1))⁻¹ *
              (GGT.RelLetter.listVal p *
                GGT.OsinComponents.vertex (1 : G) q (i + 1))
                ∈ E.rel.relBall lam' eps) ∧
          ((GGT.RelLetter.listVal p *
                GGT.OsinComponents.vertex (1 : G) q (i + 2))⁻¹ *
              GGT.OsinComponents.vertex (1 : G) s j'
                ∈ E.rel.relBall lam' eps)

/-- The source-faithful adjacent-gap package. -/
theorem exists_exactPublishedAdjacentGapOutput
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ ExactPublishedAdjacentGapOutput E C bn := by
  obtain ⟨C, hC, hmatch⟩ :=
    exists_exact_cleanSource_publishedGap_relativeSides E hsymm hδ
  refine ⟨C, hC, ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign hcount heven hW
    v q tail v' s tail' hv hq hv' hs p r hclose hr0 hlet hqg hrho heps hlen
  have hnotSame : ∀ (lam : Bool) (i j : ℕ),
      GGT.OsinComponents.IsComp lam q i (i + 1) →
      GGT.OsinComponents.IsComp lam q j (j + 1) →
      0 < i → 0 < j → i ≠ j →
      ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + i) (p.length + j) := by
    intro lam i j hiComp hjComp hi0 hj0 hne hconn
    have hjWhole :=
      GGT.OsinComponents.isComp_fourGon_of_isComp_side_of_interior
        p q r s lam hj0 hjComp.2.1 hjComp
    have hjStart : GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + j) := by
      refine ⟨p.length + j + 1, ?_⟩
      convert hjWhole using 1 <;> omega
    exact exactPrefix_not_connected_sameSide_relativeSides E hdesign hcount
      heven hW hv hq p r s lam i hiComp j
      (lt_of_lt_of_le hjComp.1 hjComp.2.1) hne.symm
      hjStart hconn
  obtain ⟨lam, lam', i, hi, hi2, hcomp, hcomp', hdeep, hdeep',
      hclean, hclean'⟩ :=
    exists_adjacent_seam_clean_components_of_sym_prefix E hdesign hv hq
      p r s hlen hnotSame
  obtain ⟨j, hj1, hj, hcompS, hconn, hgap0, hgap1⟩ :=
    hmatch hdesign hcount heven hW hv hq hv' hs p r hclose hr0 hlet hqg
      hrho heps lam i hi (by omega) hcomp hdeep hclean
  obtain ⟨j', hj1', hj', hcompS', hconn', hgap0', hgap1'⟩ :=
    hmatch hdesign hcount heven hW hv hq hv' hs p r hclose hr0 hlet hqg
      hrho heps lam' (i + 1) (by omega) hi2 hcomp' hdeep' hclean'
  exact ⟨lam, lam', i, j, j', hi, hi2, hcomp, hcomp', hj1, hj, hcompS,
    hj1', hj', hcompS', hconn, hconn', hgap0, hgap1, hgap0', hgap1'⟩

end HullSC
end GroupApproximation
