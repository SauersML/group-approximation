import GroupApproximation.Analysis.AmenableExtensionWindow
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical trace of an amenable extension of a locally RF group

`non_mf_groups_exist.tex`, Proposition `prop:locally-rf-by-z-trace`, second
assertion and its proof:

> let `P` be the projection of `ℓ²(G/H)` onto `ℓ²(T)`, and put
> `Φ(b) = Pλ(b)P|_{ℓ²(T)}`.  This map is u.c.p., and for `g ∈ E` and `ḡx ∈ F`,
> `g σ(x) r_q H = σ(ḡx) r_{θ(b(g,x))q} H ∈ T`.  So for `g,h ∈ E` the identity
> `Φ(u_{gh}) - Φ(u_g)Φ(u_h) = Pλ(g)(1-P)λ(h)P` and the rank of `(1-P)λ(h)P`,
> at most `|{x ∈ F : h̄x ∉ F}| |Q|`, give
> `‖Φ(u_{gh}) - Φ(u_g)Φ(u_h)‖₂² ≤ |{x ∈ F : h̄x ∉ F}|/|F|`.
> The normalized trace of `Φ(u_g)` is the fraction of points of `T` fixed by
> `g`, and for `g ∈ E ∖ {1}` it is zero.

The finite data and the two geometric facts are
`Analysis.AmenableExtensionWindow`.  What is added here is the analysis: the
escape set of a tested element is contained in the Følner boundary times the
fibre, which is exactly the printed rank bound, and the printed fixed-point
computation.

The printed rank estimate is not re-proved: the corpus already has
`QuasiRegularCompression.hsNorm_generatorDefect_le_sqrt_escape`, which bounds
the Hilbert--Schmidt defect of a quasi-regular compression by the square root
of the escape ratio.  The Følner condition is what makes that ratio small, and
at stage `n` it is below `1/(n+1)` by construction of the Følner set.

The fixed-point computation runs in one step rather than the printed two.  A
fixed selected coset forces `w⁻¹g⁻¹w ∈ H ≤ N` for `w = σ(x)r_q`, and reading
that in `G/N` already gives `ḡ = 1`; so the printed case `ḡ ≠ 1` is not a case
at all, and the remaining case is the printed one, where normality of `H` in
`N₀` turns the cocycle value `b(g,x)` into an element of `H` and contradicts
the choice of the packet.
-/

namespace GroupApproximation
namespace AmenableExtensionTrace

open Filter Matrix Quasidiagonal ResidualFinitePacket
open LocallyRFByIntAmenableTrace LocallyRFByIntSchedule SoficByAmenablePermanence
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] [Countable G] (N : Subgroup G) [N.Normal]

/-! ### The compression at one stage -/

/-- The printed u.c.p. map `Φ`. -/
def extMap (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) :
    MaximalGroupCStar G →ₗ[ℂ]
      Matrix (extModel N hN hA n) (extModel N hN hA n) ℂ :=
  QuasiRegularCompression.compressionMap (stageH N hN hA n) (extModel N hN hA n)
    (extCoset N hN hA n)

theorem extMap_one (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) : extMap N hN hA n 1 = 1 :=
  QuasiRegularCompression.compressionMap_one (stageH N hN hA n)
    (extModel N hN hA n) (extCoset_injective N hN hA n)

theorem extMap_completelyPositive (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) :
    IsCompletelyPositiveOnMatrices (extModel N hN hA n) ⇑(extMap N hN hA n) :=
  QuasiRegularCompression.isCompletelyPositiveOnMatrices_compressionMap
    (stageH N hN hA n) (extModel N hN hA n) (extCoset N hN hA n)

theorem norm_extMap_le (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (a : MaximalGroupCStar G) :
    ‖extMap N hN hA n a‖ ≤ ‖a‖ :=
  QuasiRegularCompression.norm_compressionMap_le (stageH N hN hA n)
    (extModel N hN hA n) (extCoset_injective N hN hA n) a

/-! ### The printed rank bound: escape is the Følner boundary -/

/-- The printed escape count: at most the Følner boundary times the fibre.
Every escaping coordinate has its Følner coordinate on the boundary, which is
the printed rank bound for `(1-P)λ(h)P`. -/
theorem card_escape_le (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {h : G}
    (hh : h ∈ exhaustion G 1 n) :
    ((QuasiRegularCompression.escape (stageH N hN hA n) (extModel N hN hA n)
        (extCoset N hN hA n) h).card : ℝ) ≤
      ((AmenableActionSofic.boundary (folnerSet N hA n)
        (QuotientGroup.mk h)).card : ℝ) *
        (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ) := by
  classical
  have hnat : (QuasiRegularCompression.escape (stageH N hN hA n)
      (extModel N hN hA n) (extCoset N hN hA n) h).card ≤
      ((AmenableActionSofic.boundary (folnerSet N hA n) (QuotientGroup.mk h)) ×ˢ
        (Finset.univ :
          Finset (cocyclePacket N hN hA n).quotientModel)).card := by
    refine Finset.card_le_card_of_injOn
      (fun z ↦ (((z.1 : ↥(folnerSet N hA n)) : G ⧸ N), z.2)) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, QuasiRegularCompression.mem_escape] at hz
      rw [Finset.mem_coe]
      show (((z.1 : ↥(folnerSet N hA n)) : G ⧸ N), z.2) ∈
        (AmenableActionSofic.boundary (folnerSet N hA n) (QuotientGroup.mk h)) ×ˢ
          (Finset.univ :
            Finset (cocyclePacket N hN hA n).quotientModel)
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      rw [AmenableActionSofic.mem_boundary]
      refine ⟨z.1.2, fun hcon ↦ hz ?_⟩
      exact extCoset_smul_mem_range N hN hA n hh z hcon
    · intro a _ b _ hab
      have hab' : (((a.1 : ↥(folnerSet N hA n)) : G ⧸ N), a.2) =
          (((b.1 : ↥(folnerSet N hA n)) : G ⧸ N), b.2) := hab
      have h1 := congrArg Prod.fst hab'
      have h2 := congrArg Prod.snd hab'
      exact Prod.ext (Subtype.ext h1) h2
  have hcardprod : ((AmenableActionSofic.boundary (folnerSet N hA n)
      (QuotientGroup.mk h)) ×ˢ
      (Finset.univ :
        Finset (cocyclePacket N hN hA n).quotientModel)).card =
      (AmenableActionSofic.boundary (folnerSet N hA n)
        (QuotientGroup.mk h)).card *
        Fintype.card (cocyclePacket N hN hA n).quotientModel := by
    rw [Finset.card_product, Finset.card_univ]
  rw [hcardprod] at hnat
  exact_mod_cast hnat

theorem card_extModel (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) :
    (Fintype.card (extModel N hN hA n) : ℝ) =
      ((folnerSet N hA n).card : ℝ) *
        (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ) := by
  have hcard : Fintype.card (extModel N hN hA n) =
      Fintype.card ↥(folnerSet N hA n) *
        Fintype.card (cocyclePacket N hN hA n).quotientModel := by
    show Fintype.card (↥(folnerSet N hA n) ×
      (cocyclePacket N hN hA n).quotientModel) = _
    exact Fintype.card_prod _ _
  rw [hcard, Fintype.card_coe]
  push_cast
  ring

/-- **The printed Hilbert--Schmidt bound.**  At stage `n` the defect of every
tested pair is below the square root of the Følner tolerance. -/
theorem hsNorm_extDefect_le (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (g : G) {h : G}
    (hh : h ∈ exhaustion G 1 n) :
    hsNorm (extModel N hN hA n)
        (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)) ≤
      Real.sqrt (1 / ((n : ℝ) + 1)) := by
  have hbase := QuasiRegularCompression.hsNorm_generatorDefect_le_sqrt_escape
    (stageH N hN hA n) (extModel N hN hA n) (extCoset_injective N hN hA n) g h
  have hQpos : (0 : ℝ) <
      Fintype.card (cocyclePacket N hN hA n).quotientModel := by
    exact_mod_cast Fintype.card_pos
  have hFpos : (0 : ℝ) < ((folnerSet N hA n).card : ℝ) := by
    have := Finset.card_pos.mpr (folnerSet_nonempty N hA n)
    exact_mod_cast this
  have hMpos : (0 : ℝ) < (Fintype.card (extModel N hN hA n) : ℝ) := by
    rw [card_extModel]
    positivity
  have hbd := folnerSet_boundary_lt N hA n (mk_mem_quotientWindow N hh)
  have hratio : ((QuasiRegularCompression.escape (stageH N hN hA n)
      (extModel N hN hA n) (extCoset N hN hA n) h).card : ℝ) /
      (Fintype.card (extModel N hN hA n) : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hMpos, card_extModel]
    calc
      ((QuasiRegularCompression.escape (stageH N hN hA n) (extModel N hN hA n)
          (extCoset N hN hA n) h).card : ℝ)
          ≤ ((AmenableActionSofic.boundary (folnerSet N hA n)
              (QuotientGroup.mk h)).card : ℝ) *
            (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ) :=
            card_escape_le N hN hA n hh
      _ ≤ (1 / ((n : ℝ) + 1) * ((folnerSet N hA n).card : ℝ)) *
            (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ) := by
            exact mul_le_mul_of_nonneg_right hbd.le hQpos.le
      _ = 1 / ((n : ℝ) + 1) *
            (((folnerSet N hA n).card : ℝ) *
              (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ)) := by
            ring
  refine le_trans ?_ (Real.sqrt_le_sqrt hratio)
  simpa only [QuasiRegularCompression.generatorDefect, extMap] using hbase

theorem tendsto_ext_generator_mul_hs (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (g h : G) :
    Tendsto (fun n ↦ hsNorm (extModel N hN hA n)
      (extMap N hN hA n
          (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h) -
        extMap N hN hA n (maximalGroupCStarGenerator G g) *
          extMap N hN hA n (maximalGroupCStarGenerator G h)))
      atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ ↦ Real.sqrt (1 / ((n : ℝ) + 1)))
  · exact Eventually.of_forall fun n ↦ hsNorm_nonneg _ _
  · filter_upwards [eventually_eventually_mem_exhaustion G 1 h] with n hn
    rw [maximalGroupCStarGenerator_mul]
    exact hsNorm_extDefect_le N hN hA n g hn
  · have hzero : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp : Tendsto (fun n : ℕ ↦ Real.sqrt (1 / ((n : ℝ) + 1))) atTop
        (nhds (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hzero
    rwa [Real.sqrt_zero] at hcomp

/-! ### The printed fixed-point computation -/

/-- **The printed trace clause.**  A tested nonidentity element fixes no
selected coset. -/
theorem ext_no_fixed_coset (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G}
    (hg : g ∈ exhaustion G 1 n) (hg1 : g ≠ 1) (z : extModel N hN hA n) :
    g • extCoset N hN hA n z ≠ extCoset N hN hA n z := by
  intro hfix
  obtain ⟨x, q⟩ := z
  set w : G := sect N (x : G ⧸ N) * windowEmb N hA n (Quotient.out q) with hw
  have hfix' : (QuotientGroup.mk (g * w) : G ⧸ stageH N hN hA n) =
      QuotientGroup.mk w := hfix
  have hmem := (QuotientGroup.eq (s := stageH N hN hA n)).mp hfix'
  have hmemN : (g * w)⁻¹ * w ∈ N := stageH_le N hN hA n hmem
  -- reading the fixed-point condition in `G / N` gives `ḡ = 1`
  have hmkw : (QuotientGroup.mk w : G ⧸ N) = (x : G ⧸ N) := by
    rw [hw, QuotientGroup.mk_mul, mk_windowEmb, mul_one, mk_sect]
  have hmkg : (QuotientGroup.mk g : G ⧸ N) = 1 := by
    have hq : (QuotientGroup.mk (g * w) : G ⧸ N) = QuotientGroup.mk w :=
      (QuotientGroup.eq (s := N)).mpr hmemN
    rw [QuotientGroup.mk_mul, hmkw] at hq
    have hq2 : (QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N) = 1 * (x : G ⧸ N) := by
      rw [one_mul]
      exact hq
    exact mul_right_cancel hq2
  have hgN : g ∈ N := (QuotientGroup.eq_one_iff g).mp hmkg
  -- the cocycle value at this Følner coordinate
  have hcoc : esCocycle N g (x : G ⧸ N) =
      (sect N (x : G ⧸ N))⁻¹ * g * sect N (x : G ⧸ N) := by
    rw [esCocycle, hmkg, one_mul]
  have hb : esCocycleN N g (x : G ⧸ N) ∈ cocycleWindow N hA n :=
    esCocycleN_mem_cocycleWindow N hA hg x.2
  set b : ↥(cocycleSubgroup N hA n) :=
    ⟨esCocycleN N g (x : G ⧸ N), mem_cocycleSubgroup N hA hb⟩ with hbdef
  have hbG : windowEmb N hA n b = esCocycle N g (x : G ⧸ N) := rfl
  have hbne : esCocycleN N g (x : G ⧸ N) ≠ 1 := by
    intro hone
    have h0 : esCocycle N g (x : G ⧸ N) = 1 := congrArg Subtype.val hone
    rw [hcoc] at h0
    have h2 : g = sect N (x : G ⧸ N) *
        ((sect N (x : G ⧸ N))⁻¹ * g * sect N (x : G ⧸ N)) *
        (sect N (x : G ⧸ N))⁻¹ := by group
    rw [h0, mul_one, mul_inv_cancel] at h2
    exact hg1 h2
  -- the fixed-point condition, rewritten through the window embedding
  have hrw : (g * w)⁻¹ * w =
      windowEmb N hA n ((Quotient.out q)⁻¹ * b⁻¹ * Quotient.out q) := by
    rw [map_mul, map_mul, map_inv, map_inv, hbG, hcoc, hw]
    group
  rw [hrw, mem_stageH_iff] at hmem
  have hconj := (cocyclePacket N hN hA n).normal'.conj_mem _ hmem (Quotient.out q)
  have hrewrite : (Quotient.out q) *
      ((Quotient.out q)⁻¹ * b⁻¹ * Quotient.out q) * (Quotient.out q)⁻¹ = b⁻¹ := by
    group
  rw [hrewrite] at hconj
  exact (cocyclePacket N hN hA n).avoids b (mem_cocyclePacketSet N hA hb hbne)
    ((cocyclePacket N hN hA n).subgroup.inv_mem_iff.mp hconj)

theorem ext_generator_trace_eq_zero (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G}
    (hg : g ∈ exhaustion G 1 n) (hg1 : g ≠ 1) :
    normTrace (extModel N hN hA n)
      (extMap N hN hA n (maximalGroupCStarGenerator G g)) = 0 :=
  QuasiRegularCompression.normTrace_compressionMap_generator_eq_zero
    (stageH N hN hA n) (extModel N hN hA n) (extCoset N hN hA n) g
    (ext_no_fixed_coset N hN hA n hg hg1)

theorem tendsto_ext_generator_trace (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (g : G) :
    Tendsto (fun n ↦
      ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g) -
        normTrace (extModel N hN hA n)
          (extMap N hN hA n (maximalGroupCStarGenerator G g))‖)
      atTop (nhds 0) := by
  by_cases hg : g = 1
  · subst hg
    have hgen : maximalGroupCStarGenerator G 1 = 1 :=
      congrArg (fun w : unitary (MaximalGroupCStar G) ↦
        (w : MaximalGroupCStar G))
        (map_one (maximalGroupCStarUnitaryHom G))
    have hzero : ∀ n : ℕ,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G 1) -
          normTrace (extModel N hN hA n)
            (extMap N hN hA n (maximalGroupCStarGenerator G 1))‖ = 0 := by
      intro n
      rw [canonicalMaximalTrace_generator_one, hgen, extMap_one,
        normTrace_one' (extModel N hN hA n) Fintype.card_pos, sub_self, norm_zero]
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · have heq : ∀ᶠ n in atTop,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g) -
          normTrace (extModel N hN hA n)
            (extMap N hN hA n (maximalGroupCStarGenerator G g))‖ = 0 := by
      filter_upwards [eventually_eventually_mem_exhaustion G 1 g] with n hn
      rw [canonicalMaximalTrace_generator_of_ne_one G hg,
        ext_generator_trace_eq_zero N hN hA n hn hg, sub_self, norm_zero]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)

/-! ### The printed second assertion -/

/-- **`prop:locally-rf-by-z-trace`, second assertion, as a closed
proposition.**  For every extension of countable groups with locally
residually finite kernel and amenable quotient, the canonical trace of the
maximal group C⋆-algebra of the extension is amenable. -/
def PrintedAmenableExtensionCanonicalTraceAmenable : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
    IsLocallyResiduallyFinite ↥N → Amenability.IsAmenable (G ⧸ N) →
      IsAmenableTrace
        (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

theorem manuscriptPrintedAmenableExtensionCanonicalTraceAmenable :
    PrintedAmenableExtensionCanonicalTraceAmenable := by
  intro G _ _ N _ hN hA
  exact ⟨amenableTraceModel_of_dense_generators
    (extMap N hN hA) (extMap_one N hN hA) (extMap_completelyPositive N hN hA)
    (norm_extMap_le N hN hA) (canonicalMaximalTrace G)
    (Set.range (maximalGroupCStarGenerator G))
    (maximalGroupCStar_dense_span_generator G)
    (by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      exact tendsto_ext_generator_mul_hs N hN hA g h)
    (by
      rintro _ ⟨g, rfl⟩
      exact tendsto_ext_generator_trace N hN hA g)⟩

/-! ### The printed proposition, both assertions -/

/-- **`prop:locally-rf-by-z-trace` as printed**, both assertions in one closed
proposition: for an extension `1 → N → G → A → 1` of countable groups with `N`
locally residually finite and `A` amenable, the canonical trace of
`C*_max(N)` is quasidiagonal and the canonical trace of `C*_max(G)` is
amenable. -/
def PrintedAmenableExtensionTrace : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
    IsLocallyResiduallyFinite ↥N → Amenability.IsAmenable (G ⧸ N) →
      IsQuasidiagonalTrace
          (fun a : MaximalGroupCStar ↥N ↦ canonicalMaximalTrace ↥N a) ∧
        IsAmenableTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

theorem manuscriptPrintedAmenableExtensionTrace :
    PrintedAmenableExtensionTrace := by
  intro G _ _ N _ hN hA
  refine ⟨?_, manuscriptPrintedAmenableExtensionCanonicalTraceAmenable G N hN hA⟩
  exact manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal ↥N hN

end

end AmenableExtensionTrace
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  AmenableExtensionTrace.manuscriptPrintedAmenableExtensionCanonicalTraceAmenable

#audit_closed_axioms
  AmenableExtensionTrace.manuscriptPrintedAmenableExtensionTrace
