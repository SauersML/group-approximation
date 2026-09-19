import GroupApproximation.GGT.HullSCRelatorSeparation2RelativeCount

/-!
# The published-gap anchor with relative short sides

The finite count and absorption modules deliberately stop at the cyclic
coordinate `j ≠ 1`.  The gap consumer needs the stronger geometric form
`1 < j`: the opposite component must lie strictly before the cyclic seam when
the quadrilateral is rotated to bound the second connector.  Component-start
properness supplies `0 < j`, so the seam exclusion upgrades it to `1 < j`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- Exact cyclic avoidance excludes a second connected component start
strictly inside the same long prefix.  No condition on either short side is
used: strictness lets both component letters be read directly from `q`. -/
theorem exactPrefix_not_connected_sameSide_relativeSides
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length) (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    {v q tail : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hq : v = q ++ tail) (p r s : List (GGT.RelLetter G Bool))
    (lam : Bool) (i : ℕ)
    (hicomp : GGT.OsinComponents.IsComp lam q i (i + 1))
    (i' : ℕ) (hi' : i' < q.length) (hne : i' ≠ i)
    (hstart : GGT.OsinComponents.IsCompStart lam
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i')) :
    ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
      (p.length + i) (p.length + i') := by
  intro hconn
  have hi : i < q.length := lt_of_lt_of_le hicomp.1 hicomp.2.1
  have hiOf := hicomp.2.2.1 i le_rfl (by omega) hi
  obtain ⟨xi, hiRead⟩ := getElem?_comp_of_isCompOf hi hiOf
  obtain ⟨k, hk⟩ := hstart
  have hglobal : p.length + i' <
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length := by
    rw [GGT.OsinComponents.length_fourGon]
    omega
  have hi'Of := hk.2.2.1 (p.length + i') le_rfl hk.1 hglobal
  have hget := GGT.OsinComponents.getElem_fourGon_q p q r s hi' rfl hglobal
  rw [hget] at hi'Of
  obtain ⟨xi', hi'Read'⟩ := getElem?_comp_of_isCompOf hi' hi'Of
  have hmem := GGT.OsinComponents.mem_fam_of_connected_side
    E.rel lam p q r s (Nat.le_of_lt hi) (Nat.le_of_lt hi') hconn
  have hwindow := index_window_of_blockCount E 1 hcount hv hq
    (d := i) (i := i') (Nat.le_of_lt hi) (Nat.le_of_lt hi') hmem
  rcases hwindow with ⟨hii', hgap⟩ | ⟨hi'i, hgap⟩
  · have hlt : i < i' := lt_of_le_of_ne hii' (Ne.symm hne)
    exact hdesign.forwardSpan_not_mem E heven hv hq hlt hi'
      hiRead hi'Read' (le_trans hgap hW) hmem
  · have hlt : i' < i := lt_of_le_of_ne hi'i hne
    have hmem' : (GGT.OsinComponents.vertex (1 : G) q i')⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q i ∈ E.rel.fam lam := by
      have := (E.rel.fam lam).inv_mem hmem
      simpa [mul_inv_rev] using this
    exact hdesign.forwardSpan_not_mem E heven hv hq hlt hi
      hi'Read' hiRead (le_trans hgap hW) hmem'

/-- Exact cyclic avoidance on the oppositely traversed long prefix.  The proof
shifts both incoming component endpoints back by one letter before applying
the same forward cyclic window. -/
theorem exactPrefix_not_connected_oppositeSide_relativeSides
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length) (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    {v s tail : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hs : v = s ++ tail) (p q r : List (GGT.RelLetter G Bool))
    (lam : Bool) (k m : ℕ)
    (hkcomp : ∃ j, j + 1 = k ∧ GGT.OsinComponents.IsComp lam s j k)
    (hm : m ≤ s.length) (hmne : m ≠ k)
    (hstart : GGT.OsinComponents.IsCompStart lam
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
      (p.length + q.length + r.length + (s.length - m))) :
    (GGT.OsinComponents.vertex (1 : G) s k)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) s m ∉ E.rel.fam lam := by
  intro hmem
  obtain ⟨j, hjk, hjcomp⟩ := hkcomp
  have hjlt : j < s.length := lt_of_lt_of_le hjcomp.1 hjcomp.2.1
  have hklen : k ≤ s.length := by simpa only [hjk] using hjcomp.2.1
  have hjOf := hjcomp.2.2.1 j le_rfl (by omega) hjlt
  obtain ⟨xj, hjRead⟩ := getElem?_comp_of_isCompOf hjlt hjOf
  obtain ⟨hm0, xm, hmRead⟩ :=
    exists_comp_letter_of_secondLongSide_start hm hstart
  let a := m - 1
  have halt : a < s.length := by simp only [a]; omega
  have hkmem : xj ∈ E.rel.fam lam :=
    comp_value_mem_fam_of_sym_relator₂ E hv (by
      calc
        v[j]? = (s ++ tail)[j]? := congrArg (fun w => w[j]?) hs
        _ = s[j]? := List.getElem?_append_left hjlt
        _ = _ := hjRead)
  have hamem : xm ∈ E.rel.fam lam :=
    comp_value_mem_fam_of_sym_relator₂ E hv (by
      calc
        v[a]? = (s ++ tail)[a]? := congrArg (fun w => w[a]?) hs
        _ = s[a]? := List.getElem?_append_left halt
        _ = _ := hmRead)
  have hjk' : j + 1 = k := hjk
  have ham : a + 1 = m := by simp only [a]; omega
  have hjstep := vertex_succ_of_getElem? s j (1 : G)
    (GGT.RelLetter.comp lam xj) hjRead
  have haste := vertex_succ_of_getElem? s a (1 : G)
    (GGT.RelLetter.comp lam xm) hmRead
  simp only [GGT.RelLetter.val] at hjstep haste
  have hwindow := index_window_of_blockCount E 1 hcount hv hs
    (d := k) (i := m) hklen hm hmem
  rcases hwindow with ⟨hkm, hgap⟩ | ⟨hmk, hgap⟩
  · have hja : j < a := by omega
    have hshiftMem : (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) s a ∈ E.rel.fam lam := by
      have heq : (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) s a =
          xj * ((GGT.OsinComponents.vertex (1 : G) s k)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) s m) * xm⁻¹ := by
        rw [← hjk', ← ham, hjstep, haste]
        group
      rw [heq]
      exact (E.rel.fam lam).mul_mem
        ((E.rel.fam lam).mul_mem hkmem hmem) ((E.rel.fam lam).inv_mem hamem)
    exact hdesign.forwardSpan_not_mem E heven hv hs hja halt hjRead hmRead
      (by omega) hshiftMem
  · have haj : a < j := by omega
    have hshiftMem : (GGT.OsinComponents.vertex (1 : G) s a)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) s j ∈ E.rel.fam lam := by
      have heq : (GGT.OsinComponents.vertex (1 : G) s a)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) s j =
          xm * (((GGT.OsinComponents.vertex (1 : G) s k)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) s m)⁻¹) * xj⁻¹ := by
        rw [← hjk', ← ham, hjstep, haste]
        group
      rw [heq]
      exact (E.rel.fam lam).mul_mem
        ((E.rel.fam lam).mul_mem hamem ((E.rel.fam lam).inv_mem hmem))
        ((E.rel.fam lam).inv_mem hkmem)
    exact hdesign.forwardSpan_not_mem E heven hv hs haj hjlt hmRead hjRead
      (by omega) hshiftMem

/-- The innermost arc clause when arbitrary relative short sides are excluded
by the finite-absorption cleanliness certificate. -/
theorem innermost_of_sideExclusions_clean
    (D : GGT.RelGenSet G Bool) (lam : Bool)
    (p q r s : List (GGT.RelLetter G Bool))
    (hclose : GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
      GGT.RelLetter.listVal q * GGT.RelLetter.listVal r)
    {i l : ℕ} (hi : i ≤ q.length) (hl : l ≤ s.length)
    (hmatch : GGT.OsinComponents.Connected D.fam lam 1
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - l)))
    (hqside : ∀ i' : ℕ, i' < q.length → i' ≠ i →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
      (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q i' ∉ D.fam lam)
    (hsside : ∀ m : ℕ, m ≤ s.length → m ≠ l →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) s l)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) s m ∉ D.fam lam)
    (hclean : ∀ m, GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
      GGT.OsinComponents.Connected D.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i) m →
      ¬ (m < p.length ∨ ∃ a, a < r.length ∧
        m = p.length + q.length + a)) :
    ∀ t, p.length + i < t →
      t < p.length + q.length + r.length + (s.length - l) →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) t →
      ¬ GGT.OsinComponents.Connected D.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i) t := by
  intro t ht1 ht2 hstart hconnt
  rcases Nat.lt_or_ge t (p.length + q.length) with hq | hq
  · have heq : t = p.length + (t - p.length) := by omega
    have hstart' : GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + (t - p.length)) := by rw [← heq]; exact hstart
    apply hqside (t - p.length) (by omega) (by omega) hstart'
    exact GGT.OsinComponents.mem_fam_of_connected_side D lam p q r s hi
      (by omega) (by rw [← heq]; exact hconnt)
  · rcases Nat.lt_or_ge t (p.length + q.length + r.length) with hr | hs
    · exact hclean t hstart hconnt (Or.inr ⟨t - (p.length + q.length),
        by omega, by omega⟩)
    · obtain ⟨m, hm, -, heq⟩ := GGT.OsinComponents.exists_rev_index
        p.length q.length r.length s.length hs (by omega)
      have hstart' : GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + q.length + r.length + (s.length - m)) := by
        rw [← heq]
        exact hstart
      apply hsside m hm (by omega) hstart'
      refine GGT.OsinComponents.mem_fam_of_common_left
        (A := GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i)
        (GGT.OsinComponents.mem_fam_of_connected_cross D lam p q r s hclose
          hi l hmatch) ?_
      exact GGT.OsinComponents.mem_fam_of_connected_cross D lam p q r s hclose
        hi m (by rw [← heq]; exact hconnt)

/-- The complementary arc clause with arbitrary relative short sides. -/
theorem otherArc_of_sideExclusions_clean
    (D : GGT.RelGenSet G Bool) (lam : Bool)
    (p q r s : List (GGT.RelLetter G Bool))
    (hclose : GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
      GGT.RelLetter.listVal q * GGT.RelLetter.listVal r)
    {i l : ℕ} (hi : i ≤ q.length) (hl : l ≤ s.length)
    (hmatch : GGT.OsinComponents.Connected D.fam lam 1
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - l)))
    (hqside : ∀ i' : ℕ, i' < q.length → i' ≠ i →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
      (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q i' ∉ D.fam lam)
    (hsside : ∀ m : ℕ, m ≤ s.length → m ≠ l →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) s l)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) s m ∉ D.fam lam)
    (hclean : ∀ m, GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
      GGT.OsinComponents.Connected D.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i) m →
      ¬ (m < p.length ∨ ∃ a, a < r.length ∧
        m = p.length + q.length + a)) :
    ∀ o, ((p.length + q.length + r.length + (s.length - l) < o ∧
        o < (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length) ∨
        o < p.length + i) →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) o →
      ¬ GGT.OsinComponents.Connected D.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - l)) o := by
  intro o ho hstart hconno
  rcases ho with ⟨ho1, ho2⟩ | ho
  · rw [GGT.OsinComponents.length_fourGon] at ho2
    obtain ⟨m, hm, -, heq⟩ := GGT.OsinComponents.exists_rev_index
      p.length q.length r.length s.length (by omega) ho2
    have hstart' : GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - m)) := by
      rw [← heq]
      exact hstart
    apply hsside m hm (by omega) hstart'
    exact GGT.OsinComponents.mem_fam_of_connected_revSide D lam p q r s
      hclose l m (by rw [← heq]; exact hconno)
  · rcases Nat.lt_or_ge o p.length with hp | hq
    · apply hclean o hstart
        (GGT.OsinComponents.connected_trans hmatch hconno)
      exact Or.inl hp
    · have heq : o = p.length + (o - p.length) := by omega
      apply hqside (o - p.length) (by omega) (by omega)
        (by rw [← heq]; exact hstart)
      have hconn2 : GGT.OsinComponents.Connected D.fam lam 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + (o - p.length))
          (p.length + q.length + r.length + (s.length - l)) := by
        rw [← heq]
        exact GGT.OsinComponents.connected_symm hconno
      have h2 := GGT.OsinComponents.mem_fam_of_connected_cross D lam p q r s
        hclose (by omega) l hconn2
      have h1 := GGT.OsinComponents.mem_fam_of_connected_cross D lam p q r s
        hclose hi l hmatch
      exact GGT.OsinComponents.mem_fam_of_match_pair h1 h2

/-- Both published gaps are uniformly bounded for a clean matched pair with
arbitrary legal relative short sides. -/
theorem exists_publishedGap_pair_relativeSides
    (D : GGT.RelGenSet G Bool)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Bool) (p q r s : List (GGT.RelLetter G Bool)) (i j : ℕ),
        GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
          GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ GGT.OsinComponents.revWord s, D.IsLetter a) →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ,
          GGT.OsinComponents.fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ GGT.OsinComponents.fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ) ≤
            ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G)
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s) x)
              (GGT.OsinComponents.vertex (1 : G)
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s) y) : ℕ) : ℝ)) →
        0 < i → i + 1 < q.length →
        GGT.OsinComponents.IsComp lam q i (i + 1) →
        1 < j → j ≤ s.length → 0 < r.length →
        GGT.OsinComponents.IsComp lam s (j - 1) j →
        GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + q.length + r.length + (s.length - j)) →
        GGT.OsinComponents.Connected D.fam lam 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i)
          (p.length + q.length + r.length + (s.length - j)) →
        (∀ i' : ℕ, i' < q.length → i' ≠ i →
          GGT.OsinComponents.IsCompStart lam
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
          (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) q i' ∉ D.fam lam) →
        (∀ m : ℕ, m ≤ s.length → m ≠ j →
          GGT.OsinComponents.IsCompStart lam
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
            (p.length + q.length + r.length + (s.length - m)) →
          (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) s m ∉ D.fam lam) →
        (∀ m, GGT.OsinComponents.IsCompStart lam
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
          GGT.OsinComponents.Connected D.fam lam 1
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i) m →
          ¬ (m < p.length ∨ ∃ a, a < r.length ∧
            m = p.length + q.length + a)) →
        ((GGT.OsinComponents.vertex (1 : G) s (j - 1))⁻¹ *
            (GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q i)
              ∈ D.relBall lam (C * 4)) ∧
          ((GGT.RelLetter.listVal p * GGT.OsinComponents.vertex (1 : G) q (i + 1))⁻¹ *
            GGT.OsinComponents.vertex (1 : G) s j ∈ D.relBall lam (C * 4)) := by
  have hbound := GGT.OsinComponents.sixBound_one_of_fourPointHyperbolic D hsymm hδ
  have hcut := GGT.OsinComponents.connector_mem_relBall_one D hbound
    (bn : ℝ) (Nat.cast_nonneg bn)
  obtain ⟨C, hC, hcore⟩ :=
    GGT.OsinComponents.two_block_conj_named_of_polygonComponents_at
      D hsymm 1 (bn : ℝ) hcut
  refine ⟨C, hC, ?_⟩
  intro lam p q r s i j hclose hlet hqg hi hiend hcompq hj1 hj hr0
    hcomps hstart hconn hqside hsside hclean
  have hbridgeq :=
    GGT.OsinComponents.isComp_fourGon_of_isComp_side_of_interior
      p q r s lam hi hiend hcompq
  have hbridges :=
    GGT.OsinComponents.isComp_fourGon_of_isComp_opposite_of_start
      p q r s lam hj1 hj hcomps hstart
  have hwrap : ∀ h0 : 0 < (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length,
      p.length + q.length + r.length + (s.length - (j - 1)) =
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length →
      ¬ ((p ++ q ++ r ++ GGT.OsinComponents.revWord s)[0]'h0).IsCompOf lam := by
    intro h0 heq
    rw [GGT.OsinComponents.length_fourGon] at heq
    omega
  exact hcore lam p q r s i (i + 1) (j - 1) j hclose hlet hqg
    hcompq hcomps hbridgeq hbridges hwrap (by omega) (by omega) hconn
    (innermost_of_sideExclusions_clean D lam p q r s hclose
      (by omega) hj hconn hqside hsside hclean)
    (otherArc_of_sideExclusions_clean D lam p q r s hclose
      (by omega) hj hconn hqside hsside hclean)

/-- A long exact-relator prefix supplies a clean opposite match strictly away
from the cyclic seam, with arbitrary legal relative connector words. -/
theorem exists_exact_prefix_publishedGapAnchor_relativeSides
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
        ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
        ∀ {v q tail : List (GGT.RelLetter G Bool)},
          RelWord.Sym
            (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
          v = q ++ tail →
          ∀ (p r s : List (GGT.RelLetter G Bool)),
            GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
              GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
            GGT.OsinComponents.IsQuasiGeodesicPolygon E.rel 1 (bn : ℝ) 4 1
              (p ++ q ++ r ++ GGT.OsinComponents.revWord s) →
            C * 4 ≤ rho →
            p.length + r.length + 2 + 3 ≤ q.length →
            (∀ (lam : Bool) (i : ℕ),
              GGT.OsinComponents.IsComp lam q i (i + 1) →
              ∀ i', i' < q.length → i' ≠ i →
                GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i') →
                ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) (p.length + i')) →
            ∃ (lam : Bool) (i j : ℕ),
              0 < i ∧ i + 1 < q.length ∧
              GGT.OsinComponents.IsComp lam q i (i + 1) ∧
              1 < j ∧ j ≤ s.length ∧
              GGT.OsinComponents.IsCompStart lam
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              (∃ h : G, h ∈ E.rel.fam lam ∧
                GGT.RelLetter.listVal p *
                    GGT.OsinComponents.vertex (1 : G) q i * h =
                  GGT.OsinComponents.vertex (1 : G) s j) ∧
              ∀ m, GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
                GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) m →
                ¬ (m < p.length ∨
                  ∃ a : ℕ, a < r.length ∧
                    m = p.length + q.length + a) := by
  obtain ⟨C, hC, hmatch⟩ :=
    exists_exact_prefix_seam_clean_match_relativeSides E hsymm hδ
  refine ⟨C, hC, ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign v q tail hv hq
    p r s hclose hpoly hrho hlen hnotSame
  obtain ⟨lam, i, j, hi, hiend, hicomp, hj, hjne, hjstart,
      hconnector, hclean⟩ :=
    hmatch hdesign hv hq p r s hclose hpoly hrho hlen hnotSame
  have hjpos : 0 < j := by
    obtain ⟨k, hk⟩ := hjstart
    have hwordLength :
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length =
          p.length + q.length + r.length + s.length :=
      GGT.OsinComponents.length_fourGon p q r s
    have hstartlt :
        p.length + q.length + r.length + (s.length - j) <
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s).length :=
      lt_of_lt_of_le hk.1 hk.2.1
    rw [hwordLength] at hstartlt
    omega
  exact ⟨lam, i, j, hi, hiend, hicomp, by omega, hj, hjstart,
    hconnector, hclean⟩

/-- The exact-design matched-pair output, with arbitrary relative short sides. -/
def ExactPublishedGapOutput (E : HypEmbeddedCore₂ A N) (C bn : ℕ) : Prop :=
  ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
    ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
    RelatorBlockCountAt₂ E [baseLetter] ms 1 →
    Even ms.length → 1 + blockConst [baseLetter] 1 ≤ W →
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
        p.length + r.length + 2 + 3 ≤ q.length →
        ∃ (lam : Bool) (i j : ℕ),
          0 < i ∧ i + 1 < q.length ∧
          GGT.OsinComponents.IsComp lam q i (i + 1) ∧
          1 < j ∧ j ≤ s.length ∧
          GGT.OsinComponents.IsComp lam s (j - 1) j ∧
          GGT.OsinComponents.IsCompStart lam
            (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
            (p.length + q.length + r.length + (s.length - j)) ∧
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
                ∈ E.rel.relBall lam eps)

/-- The seam-safe anchor together with the two bounded polygon gaps.  Both
long sides are prefixes of members of the exact symmetrized family, so the
opposite component read from the polygon start is automatically the singleton
component of that prefix.  The returned gaps are enlarged directly to the
design avoidance radius `eps`; no spelling of either short side is used. -/
theorem exists_exact_prefix_publishedGapPair_relativeSides
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
        ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
        RelatorBlockCountAt₂ E [baseLetter] ms 1 →
        Even ms.length → 1 + blockConst [baseLetter] 1 ≤ W →
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
            p.length + r.length + 2 + 3 ≤ q.length →
            ∃ (lam : Bool) (i j : ℕ),
              0 < i ∧ i + 1 < q.length ∧
              GGT.OsinComponents.IsComp lam q i (i + 1) ∧
              1 < j ∧ j ≤ s.length ∧
              GGT.OsinComponents.IsComp lam s (j - 1) j ∧
              GGT.OsinComponents.IsCompStart lam
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
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
  obtain ⟨Ca, hCa, hanchor⟩ :=
    exists_exact_prefix_publishedGapAnchor_relativeSides E hsymm hδ
  obtain ⟨Cg, hCg, hgap⟩ :=
    exists_publishedGap_pair_relativeSides E.rel hsymm hδ
  refine ⟨max Ca Cg, lt_of_lt_of_le hCa (Nat.le_max_left _ _), ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign hcount heven hW
    v q tail v' s tail' hv hq hv' hs p r hclose hr0 hlet hqg hrho heps hlen
  have hpoly : GGT.OsinComponents.IsQuasiGeodesicPolygon E.rel 1 (bn : ℝ) 4 1
      (p ++ q ++ r ++ GGT.OsinComponents.revWord s) :=
    GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon p q r s E.rel
      hlet hclose hqg
  have hCaRho : Ca * 4 ≤ rho := by
    exact le_trans (Nat.mul_le_mul_right 4 (Nat.le_max_left Ca Cg)) hrho
  have hCgEps : Cg * 4 ≤ eps := by
    exact le_trans (Nat.mul_le_mul_right 4 (Nat.le_max_right Ca Cg)) heps
  have hnotSame : ∀ (lam : Bool) (i : ℕ),
      GGT.OsinComponents.IsComp lam q i (i + 1) →
      ∀ i', i' < q.length → i' ≠ i →
        GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
        ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + i) (p.length + i') := by
    intro lam i hicomp i' hi' hne hstart
    exact exactPrefix_not_connected_sameSide_relativeSides E hdesign hcount
      heven hW hv hq p r s lam i hicomp i' hi' hne hstart
  obtain ⟨lam, i, j, hi, hiend, hicomp, hj1, hj, hjstart,
      ⟨h, hh, hc⟩, hclean⟩ :=
    hanchor hdesign hv hq p r s hclose hpoly hCaRho hlen hnotSame
  obtain ⟨hj0, x, hx⟩ :=
    exists_comp_letter_of_secondLongSide_start hj hjstart
  have hxv : v'[j - 1]? = some (GGT.RelLetter.comp lam x) := by
    rw [hs, List.getElem?_append_left (by omega : j - 1 < s.length)]
    exact hx
  have hcompsV := isComp_of_sym_exactRelator E hv' hxv
  have hcomps : GGT.OsinComponents.IsComp lam s (j - 1) j := by
    rw [hs] at hcompsV
    have hpref := isComp_prefix hcompsV (by omega : j - 1 + 1 ≤ s.length)
    convert hpref using 1
    all_goals omega
  have hconn := GGT.OsinComponents.connected_of_connector E.rel lam p q r s
    hclose (by omega : i ≤ q.length) j hh hc
  have hqside : ∀ i' : ℕ, i' < q.length → i' ≠ i →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s) (p.length + i') →
      (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q i' ∉ E.rel.fam lam := by
    intro i' hi' hne hstart hmem
    exact hnotSame lam i hicomp i' hi' hne hstart
      ((GGT.OsinComponents.connected_fourGon_side_iff E.rel lam p q r s
        (by omega) (by omega)).mpr hmem)
  have hsside : ∀ m : ℕ, m ≤ s.length → m ≠ j →
      GGT.OsinComponents.IsCompStart lam
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + q.length + r.length + (s.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) s j)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) s m ∉ E.rel.fam lam := by
    intro m hm hne hstart
    exact exactPrefix_not_connected_oppositeSide_relativeSides E hdesign hcount
      heven hW hv' hs p q r lam j m ⟨j - 1, by omega, hcomps⟩ hm hne hstart
  obtain ⟨hgap0, hgap1⟩ := hgap lam p q r s i j hclose hlet hqg
    hi hiend hicomp hj1 hj hr0 hcomps hjstart hconn hqside hsside hclean
  exact ⟨lam, i, j, hi, hiend, hicomp, hj1, hj, hcomps, hjstart,
    ⟨h, hh, hc⟩,
    GGT.OsinComponents.relBall_mono_radius E.rel lam hCgEps hgap0,
    GGT.OsinComponents.relBall_mono_radius E.rel lam hCgEps hgap1⟩

/-- Packaged form of `exists_exact_prefix_publishedGapPair_relativeSides`. -/
theorem exists_exactPublishedGapOutput
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ ExactPublishedGapOutput E C bn := by
  simpa only [ExactPublishedGapOutput] using
    exists_exact_prefix_publishedGapPair_relativeSides E hsymm hδ

end HullSC
end GroupApproximation
