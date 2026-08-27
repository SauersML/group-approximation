import GroupApproximation.Sofic.WreathPermLayer
import GroupApproximation.Sofic.WreathChartLamp
import GroupApproximation.Sofic.SoficPiProduct

/-!
# Theorem 29.6: the generalized wreath product of sofic data is sofic

If `K` and `G` are sofic and the action `G ↷ X` is sofic, then the
permutational wreath product `K^{(X)} ⋊ G` is sofic.

The model is assembled from three approximations at once.  A sofic action model
supplies a finite base set `A`, an approximate translation `φ`, a large good set
and injective charts `π_s : E → B` of the tested window.  Because `B` is finite,
`J = K^B` is sofic (Section 29.3), and a model of `J` on a finite set `D`
supplies the lamp layer.  A model of `G` on `Ω` is carried along untouched: the
wreath model cannot separate two elements with different acting parts, since a
sofic action model is not required to be free, so the acting coordinate is
recorded separately -- this is the role Section 29.7 identifies for soficity of
the acting group.

The model set is `(D × A) × Ω`, and an element `f h` acts by

`((d, a), ω) ↦ ((θ (L(f) (φ(h) a)) d, φ(h) a), ψ(h) ω)`,

where `L(f)(s)` is the lamp read through the chart at `s`.  Multiplicativity is
the three-discarded-sets count of Section 29.6 together with the transport
identity (29.3); separation splits according to whether the acting parts differ.
-/

namespace GroupApproximation

namespace GeneralizedWreath

open WreathLayer WreathChart

variable {K G X : Type} [Group K] [Group G] [MulAction G X]

/-- **Theorem 29.6.**  A permutational wreath product of sofic groups along a
sofic action is sofic. -/
theorem isSofic_wreath (hK : IsSofic K) (hG : IsSofic G)
    (hXact : IsSoficAction G X) : IsSofic (Wreath K G X) := by
  classical
  intro F ε hε
  set ε₀ : ℝ := min ε 1 / 6 with hε₀def
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; positivity
  have hε₀small : ε₀ ≤ 1 / 6 := by
    rw [hε₀def]
    have : min ε 1 ≤ 1 := min_le_right _ _
    linarith
  have hε₀le : 6 * ε₀ ≤ ε := by
    rw [hε₀def]
    have : min ε 1 ≤ ε := min_le_left _ _
    linarith
  -- supports of the tested lamps
  have hsuppFin : ∀ f : Lamp K X, {x : X | f.toFun x ≠ 1}.Finite := fun f => f.2
  set supps : Finset X := F.biUnion (fun w => (hsuppFin w.left).toFinset)
    with hsupps
  set FG : Finset G := F.image SemidirectProduct.right with hFG
  set F' : Finset G := FG ∪ (FG ×ˢ FG).image (fun p => p.1 * p.2) with hF'
  set E : Finset X :=
    supps ∪ FG.biUnion (fun g => supps.image (fun x => g • x)) with hE
  have hFGmem : ∀ w ∈ F, w.right ∈ FG := fun w hw => Finset.mem_image_of_mem _ hw
  have hFF : ∀ g ∈ FG, g ∈ F' := fun g hg => Finset.mem_union_left _ hg
  have hFF2 : ∀ g ∈ FG, ∀ h ∈ FG, g * h ∈ F' := by
    intro g hg h hh
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩)
  have hsuppE : ∀ w ∈ F, ∀ x : X, (w.left).toFun x ≠ 1 → x ∈ E := by
    intro w hw x hx
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Set.Finite.mem_toFinset _).mpr hx⟩
  have hsuppTrans : ∀ w ∈ F, ∀ g ∈ FG, ∀ x : X,
      (w.left).toFun x ≠ 1 → g • x ∈ E := by
    intro w hw g hg x hx
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, hg, ?_⟩)
    exact Finset.mem_image.mpr ⟨x, Finset.mem_biUnion.mpr
      ⟨w, hw, (Set.Finite.mem_toFinset _).mpr hx⟩, rfl⟩
  -- the sofic action model
  obtain ⟨M⟩ := hXact F' E ε₀ hε₀
  letI : Fintype M.Site := M.siteFintype
  letI : DecidableEq M.Site := M.siteDecEq
  letI : Fintype M.Chart := M.chartFintype
  letI : DecidableEq M.Chart := Classical.decEq _
  set A : FiniteModel := ⟨M.Site, M.siteFintype, M.siteDecEq⟩ with hAdef
  have hAcard : 0 < Fintype.card A := M.siteNonempty
  have hAcardR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hAcard
  -- the lamp group of the chart target and its labels
  set L : Wreath K G X → M.Site → (M.Chart → K) :=
    fun w s => if s ∈ M.good then chartLamp E (M.chart s) w.left else 1 with hLdef
  set FJ : Finset (M.Chart → K) :=
    (Finset.univ ×ˢ F).image (fun p : M.Site × Wreath K G X => L p.2 p.1)
    with hFJ
  have hLmem : ∀ w ∈ F, ∀ s : M.Site, L w s ∈ FJ := by
    intro w hw s
    exact Finset.mem_image.mpr
      ⟨(s, w), Finset.mem_product.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩
  have hJsofic : IsSofic (M.Chart → K) :=
    PiSofic.isSofic_pi (K := fun _ : M.Chart => K) (fun _ => hK)
  obtain ⟨N⟩ := hJsofic FJ ε₀ hε₀
  obtain ⟨P⟩ := hG FG ε₀ hε₀
  set D : FiniteModel := N.carrier with hDdef
  set Ω : FiniteModel := P.carrier with hΩdef
  have hDcard : 0 < Fintype.card D := N.nonempty
  have hΩcard : 0 < Fintype.card Ω := P.nonempty
  have hDAcard : 0 < Fintype.card (prodModel D A) := by
    rw [show Fintype.card (prodModel D A) = Fintype.card D * Fintype.card A from
      Fintype.card_prod _ _]
    exact Nat.mul_pos hDcard hAcard
  -- the model map
  set Θ : Wreath K G X → M.Site → Equiv.Perm D := fun w s => N.map (L w s)
    with hΘdef
  set inner : Wreath K G X → Equiv.Perm (prodModel D A) :=
    fun w => fiberPerm (Θ w) (M.act w.right) with hinner
  set Φ : Wreath K G X → Equiv.Perm (prodModel (prodModel D A) Ω) :=
    fun w => fiberPerm (fun _ : Ω => inner w) (P.map w.right) with hΦ
  -- good model points and their complement
  have hbadA : ((Finset.univ \ M.good).card : ℝ) ≤ ε₀ * Fintype.card A := by
    have hcards : (Finset.univ \ M.good).card = Fintype.card A - M.good.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hle : M.good.card ≤ Fintype.card A :=
      Finset.card_le_card (Finset.subset_univ _)
    have hR : ((Finset.univ \ M.good).card : ℝ)
        = (Fintype.card A : ℝ) - M.good.card := by
      rw [hcards]; exact Nat.cast_sub hle
    have hgc := M.good_card
    rw [hR]
    have hcardEq : (Fintype.card A : ℝ) = (Fintype.card M.Site : ℝ) := rfl
    rw [hcardEq]
    nlinarith [hgc]
  refine ⟨{
    carrier := prodModel (prodModel D A) Ω
    nonempty := ?_
    map := Φ
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [show Fintype.card (prodModel (prodModel D A) Ω)
      = Fintype.card (prodModel D A) * Fintype.card Ω from Fintype.card_prod _ _]
    exact Nat.mul_pos hDAcard hΩcard
  · -- multiplicativity
    intro w₁ hw₁ w₂ hw₂
    set h₁ : G := w₁.right with hh₁
    set h₂ : G := w₂.right with hh₂
    -- the inner comparison
    have hinnerprod : inner w₁ * inner w₂
        = fiberPerm (fun a => Θ w₁ a * Θ w₂ ((M.act h₁)⁻¹ a))
            (M.act h₁ * M.act h₂) := fiberPerm_mul _ _ _ _
    set badA : Finset M.Site :=
      (Finset.univ.filter fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a)
        ∪ ((Finset.univ.filter fun a => M.act (h₁ * h₂) a ∉ M.good)
          ∪ (Finset.univ.filter fun a => M.act h₂ a ∉ M.good)) with hbadAdef
    have hinnerle : hammingDistance (prodModel D A) (inner (w₁ * w₂))
        (inner w₁ * inner w₂)
        ≤ (badA.card : ℝ) / Fintype.card A + ε₀ := by
      rw [hinnerprod]
      have hright : (w₁ * w₂).right = h₁ * h₂ := rfl
      simp only [hinner]
      rw [hright]
      refine hammingDistance_fiberPerm_le _ _ _ _ hDcard hAcard badA hε₀.le ?_
      intro a ha
      have hnot : a ∉ (Finset.univ.filter
          fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a) ∧
          a ∉ (Finset.univ.filter fun a => M.act (h₁ * h₂) a ∉ M.good) ∧
          a ∉ (Finset.univ.filter fun a => M.act h₂ a ∉ M.good) := by
        rw [hbadAdef, Finset.mem_union, Finset.mem_union] at ha
        push Not at ha
        exact ⟨ha.1, ha.2.1, ha.2.2⟩
      have heqbase : M.act (h₁ * h₂) a = (M.act h₁ * M.act h₂) a := by
        by_contra hcon
        exact hnot.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      have hsgood : M.act (h₁ * h₂) a ∈ M.good := by
        by_contra hcon
        exact hnot.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      have hrgood : M.act h₂ a ∈ M.good := by
        by_contra hcon
        exact hnot.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      refine ⟨heqbase, ?_⟩
      -- the transport identity turns the labels into a genuine product
      set s : M.Site := M.act (h₁ * h₂) a with hs
      set r : M.Site := M.act h₂ a with hr
      have hsr : (M.act h₁) r = s := by
        show (M.act h₁) ((M.act h₂) a) = (M.act (h₁ * h₂)) a
        rw [← hs, heqbase]
        rfl
      have hinv : (M.act h₁)⁻¹ s = r := by
        rw [← hsr]
        simp
      have hlabel : L (w₁ * w₂) s = L w₁ s * L w₂ r := by
        have hleft : (w₁ * w₂).left = w₁.left * lampAut h₁ w₂.left := rfl
        rw [hLdef]
        simp only [if_pos hsgood, if_pos hrgood, hleft]
        rw [chartLamp_mul]
        congr 1
        refine chartLamp_congr (K := K) ?_ ?_ ?_ ?_
        · intro x hx y hy hxy
          exact M.chart_inj s hsgood x hx y hy hxy
        · intro x hx y hy hxy
          exact M.chart_inj r hrgood x hx y hy hxy
        · intro x hx
          exact ⟨hsuppE w₂ hw₂ x hx,
            hsuppTrans w₂ hw₂ h₁ (hFGmem w₁ hw₁) x hx⟩
        · intro x hx hinvx
          have := M.chart_equivariant h₁ (hFF h₁ (hFGmem w₁ hw₁)) r hrgood
            (by rw [hsr]; exact hsgood) x hx hinvx
          rw [hsr] at this
          exact this
      have hmul := N.multiplicative (L w₁ s) (hLmem w₁ hw₁ s) (L w₂ r)
        (hLmem w₂ hw₂ r)
      have hbase' : (M.act h₁ * M.act h₂) a = s := heqbase.symm
      rw [hbase', hinv]
      show hammingDistance D (N.map (L (w₁ * w₂) s))
        (N.map (L w₁ s) * N.map (L w₂ r)) ≤ ε₀
      rw [hlabel]
      exact hmul
    -- the outer comparison
    set badΩ : Finset Ω :=
      Finset.univ.filter fun ω => P.map (h₁ * h₂) ω ≠ (P.map h₁ * P.map h₂) ω
      with hbadΩdef
    have houter : hammingDistance (prodModel (prodModel D A) Ω) (Φ (w₁ * w₂))
        (Φ w₁ * Φ w₂)
        ≤ (badΩ.card : ℝ) / Fintype.card Ω
          + ((badA.card : ℝ) / Fintype.card A + ε₀) := by
      have hprod : Φ w₁ * Φ w₂
          = fiberPerm (fun _ : Ω => inner w₁ * inner w₂)
              (P.map h₁ * P.map h₂) := by
        simp only [hΦ]
        rw [fiberPerm_mul]
      have hright : (w₁ * w₂).right = h₁ * h₂ := rfl
      rw [hprod]
      simp only [hΦ]
      rw [hright]
      refine hammingDistance_fiberPerm_le _ _ _ _ hDAcard hΩcard badΩ
        (by positivity) ?_
      intro ω hω
      have heq : P.map (h₁ * h₂) ω = (P.map h₁ * P.map h₂) ω := by
        by_contra hcon
        exact hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      exact ⟨heq, hinnerle⟩
    -- the two discarded proportions
    have hbadΩle : (badΩ.card : ℝ) / Fintype.card Ω ≤ ε₀ := by
      have hd := P.multiplicative h₁ (hFGmem w₁ hw₁) h₂ (hFGmem w₂ hw₂)
      rw [hammingDistance, hammingDisagreement] at hd
      exact hd
    have hbadAle : (badA.card : ℝ) / Fintype.card A ≤ 3 * ε₀ := by
      have hcard1 : ((Finset.univ.filter
          fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a).card : ℝ)
          ≤ ε₀ * Fintype.card A := by
        have hd := M.act_mul h₁ (hFF h₁ (hFGmem w₁ hw₁)) h₂
          (hFF h₂ (hFGmem w₂ hw₂))
        rw [permDist, div_le_iff₀ hAcardR] at hd
        calc ((Finset.univ.filter
            fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a).card : ℝ)
            ≤ ε₀ * Fintype.card M.Site := hd
          _ = ε₀ * Fintype.card A := rfl
      have hpre : ∀ σ : Equiv.Perm M.Site,
          ((Finset.univ.filter fun a => σ a ∉ M.good).card : ℝ)
            ≤ ε₀ * Fintype.card A := by
        intro σ
        have himg : (Finset.univ.filter fun a => σ a ∉ M.good)
            = (Finset.univ \ M.good).image σ.symm := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_image, Finset.mem_sdiff]
          constructor
          · intro ha
            exact ⟨σ a, ha, by simp⟩
          · rintro ⟨b, hb, rfl⟩
            simpa using hb
        rw [himg, Finset.card_image_of_injective _ σ.symm.injective]
        exact hbadA
      have hsum : (badA.card : ℝ) ≤ 3 * (ε₀ * Fintype.card A) := by
        have h1 := hcard1
        have h2 := hpre (M.act (h₁ * h₂))
        have h3 := hpre (M.act h₂)
        have hle : badA.card ≤ (Finset.univ.filter
            fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a).card
            + ((Finset.univ.filter fun a => M.act (h₁ * h₂) a ∉ M.good).card
              + (Finset.univ.filter fun a => M.act h₂ a ∉ M.good).card) := by
          rw [hbadAdef]
          exact le_trans (Finset.card_union_le _ _)
            (Nat.add_le_add_left (Finset.card_union_le _ _) _)
        have hleR : (badA.card : ℝ) ≤ ((Finset.univ.filter
            fun a => M.act (h₁ * h₂) a ≠ (M.act h₁ * M.act h₂) a).card : ℝ)
            + (((Finset.univ.filter
                fun a => M.act (h₁ * h₂) a ∉ M.good).card : ℝ)
              + ((Finset.univ.filter fun a => M.act h₂ a ∉ M.good).card : ℝ)) := by
          exact_mod_cast hle
        linarith
      rw [div_le_iff₀ hAcardR]
      linarith
    linarith [houter, hbadΩle, hbadAle, hε₀le]
  · -- separation
    intro w₁ hw₁ w₂ hw₂ hne
    by_cases hright : w₁.right = w₂.right
    · -- same acting part: the lamps must differ inside the window
      have hleft : w₁.left ≠ w₂.left := by
        intro hcon
        exact hne (SemidirectProduct.ext hcon hright)
      obtain ⟨x₀, hx₀⟩ : ∃ x : X, (w₁.left).toFun x ≠ (w₂.left).toFun x := by
        by_contra hcon
        push Not at hcon
        exact hleft (Lamp.ext hcon)
      have hx₀E : x₀ ∈ E := by
        by_cases h1 : (w₁.left).toFun x₀ ≠ 1
        · exact hsuppE w₁ hw₁ x₀ h1
        · push Not at h1
          refine hsuppE w₂ hw₂ x₀ ?_
          intro hcon
          exact hx₀ (by rw [h1, hcon])
      -- the inner layer separates
      have hinnersep : (1 - ε₀) * (1 - ε₀)
          ≤ hammingDistance (prodModel D A) (inner w₁) (inner w₂) := by
        simp only [hinner]
        rw [hright]
        refine le_trans ?_ (hammingDistance_fiberPerm_ge (Θ w₁) (Θ w₂)
          (M.act w₂.right) (M.act w₂.right) hDcard hAcard
          (Finset.univ.filter fun a => M.act w₂.right a ∉ M.good)
          (c := 1 - ε₀) ?_)
        · have hfilter : ((Finset.univ.filter
              fun a => M.act w₂.right a ∉ M.good).card : ℝ)
              ≤ ε₀ * Fintype.card A := by
            have himg : (Finset.univ.filter fun a => M.act w₂.right a ∉ M.good)
                = (Finset.univ \ M.good).image (M.act w₂.right).symm := by
              ext a
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_image, Finset.mem_sdiff]
              constructor
              · intro ha
                exact ⟨M.act w₂.right a, ha, by simp⟩
              · rintro ⟨b, hb, rfl⟩
                simpa using hb
            rw [himg, Finset.card_image_of_injective _
              (M.act w₂.right).symm.injective]
            exact hbadA
          have hle : ((Finset.univ.filter
              fun a => M.act w₂.right a ∉ M.good).card : ℝ)
              / Fintype.card A ≤ ε₀ := by
            rw [div_le_iff₀ hAcardR]
            linarith
          nlinarith [hε₀.le, hε₀small]
        · intro a ha
          have hgood : M.act w₂.right a ∈ M.good := by
            by_contra hcon
            exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
          rw [if_pos rfl]
          set s : M.Site := M.act w₂.right a with hs
          have hLne : L w₁ s ≠ L w₂ s := by
            rw [hLdef]
            simp only [if_pos hgood]
            refine chartLamp_ne (K := K) ?_ hx₀E hx₀
            intro y hy z hz hyz
            exact M.chart_inj s hgood y hy z hz hyz
          have hsep := N.separated (L w₁ s) (hLmem w₁ hw₁ s) (L w₂ s)
            (hLmem w₂ hw₂ s) hLne
          rw [hΘdef]
          exact hsep
      -- the outer layer only copies it
      have houter : hammingDistance (prodModel D A) (inner w₁) (inner w₂)
          ≤ hammingDistance (prodModel (prodModel D A) Ω) (Φ w₁) (Φ w₂) := by
        simp only [hΦ]
        rw [hright]
        have := hammingDistance_fiberPerm_ge (fun _ : Ω => inner w₁)
          (fun _ : Ω => inner w₂) (P.map w₂.right) (P.map w₂.right) hDAcard
          hΩcard (∅ : Finset Ω)
          (c := hammingDistance (prodModel D A) (inner w₁) (inner w₂))
          (fun ω _ => by rw [if_pos rfl])
        simpa using this
      have : (1 - ε₀) * (1 - ε₀) ≤ hammingDistance
          (prodModel (prodModel D A) Ω) (Φ w₁) (Φ w₂) :=
        le_trans hinnersep houter
      nlinarith [hε₀.le, hε₀small]
    · -- different acting parts: the model of `G` separates
      have hsep := P.separated w₁.right (hFGmem w₁ hw₁) w₂.right
        (hFGmem w₂ hw₂) hright
      have hge : 1 - ε₀ ≤ hammingDistance (prodModel (prodModel D A) Ω)
          (Φ w₁) (Φ w₂) := by
        simp only [hΦ]
        refine le_trans ?_ (hammingDistance_fiberPerm_ge (fun _ : Ω => inner w₁)
          (fun _ : Ω => inner w₂) (P.map w₁.right) (P.map w₂.right) hDAcard
          hΩcard (Finset.univ.filter
            fun ω => P.map w₁.right ω = P.map w₂.right ω) (c := 1) ?_)
        · have hcard : ((Finset.univ.filter
              fun ω => P.map w₁.right ω = P.map w₂.right ω).card : ℝ)
              / Fintype.card Ω ≤ ε₀ := by
            have hΩR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hΩcard
            have hsplit : (Finset.univ.filter
                fun ω => P.map w₁.right ω = P.map w₂.right ω).card
                + (hammingDisagreement (P.map w₁.right) (P.map w₂.right)).card
                = Fintype.card Ω := by
              rw [hammingDisagreement,
                Finset.card_filter_add_card_filter_not, Finset.card_univ]
            have hsplitR : ((Finset.univ.filter
                fun ω => P.map w₁.right ω = P.map w₂.right ω).card : ℝ)
                + ((hammingDisagreement (P.map w₁.right)
                  (P.map w₂.right)).card : ℝ) = (Fintype.card Ω : ℝ) := by
              exact_mod_cast hsplit
            rw [hammingDistance, le_div_iff₀ hΩR] at hsep
            rw [div_le_iff₀ hΩR]
            linarith
          linarith
        · intro ω hω
          have hne' : P.map w₁.right ω ≠ P.map w₂.right ω := by
            intro hcon
            exact hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
          rw [if_neg hne']
      linarith

end GeneralizedWreath

end GroupApproximation
