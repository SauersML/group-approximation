import GroupApproximation.Analysis.AmenableExtensionAmenableTrace

/-!
# `prop:locally-rf-by-z-trace`, sentence by sentence

`non_mf_groups_exist.tex`, the printed proof of Proposition
`prop:locally-rf-by-z-trace`.  The statement is carried by
`AmenableExtensionTrace.manuscriptPrintedAmenableExtensionTrace`; this module
adds one named lemma per printed sentence, each quoting its sentence verbatim
and each proved from the pieces already landed in
`Analysis.LocallyRFQuasidiagonalTrace` and
`Analysis.AmenableExtensionWindow`/`AmenableExtensionAmenableTrace`.

No new mathematics: every lemma below is a wrapper.  Where a printed sentence
is exactly a landed lemma the wrapper is a definitional alias; where a printed
sentence asserts several things at once the wrapper is their conjunction.

The proof splits at "For the second assertion"; sentences 1--4 are the
quasidiagonality of the kernel trace and sentences 5--11 the amenability of the
ambient trace.
-/

namespace GroupApproximation
namespace AmenableExtensionSentences

open Filter Matrix Quasidiagonal ResidualFinitePacket
open LocallyRFByIntAmenableTrace LocallyRFByIntSchedule SoficByAmenablePermanence
open AmenableExtensionTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## First assertion: the canonical trace of `C*_max(N)` is quasidiagonal -/

section First

variable {N : Type} [Group N] [Countable N]

/-- **Printed sentence 1.**

> For the first assertion, let `E ⊆ N` be finite, put `N₀ = ⟨E⟩`, and choose a
> finite quotient `θ : N₀ → Q` with `θ(x) ≠ 1` for `x ∈ E ∖ {1}`; put
> `H = ker θ`.

`E` is the standard exhaustion at stage `n`, `N₀` is `stageSubgroup`, the
finite quotient is `stagePacket`, and `H` is `stageKernel`.  The content of the
sentence is that the quotient separates every nonidentity tested element, which
is what `Packet.avoids` says of the packet chosen. -/
theorem manuscriptSentence_stagePacketSeparates
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) {g : N}
    (hg : g ∈ exhaustion N 1 n) (hg1 : g ≠ 1) :
    (⟨g, mem_stageSubgroup hg⟩ : ↥(stageSubgroup N n)) ∉
      (stagePacket hN n).subgroup :=
  (stagePacket hN n).avoids _ (mem_stagePacketSet hg hg1)

/-- **Printed sentence 2.**

> In the quasi-regular representation of `N` on `ℓ²(N/H)`, the
> finite-dimensional subspace `ℓ²(N₀/H)` is `N₀`-invariant, and compression to
> it is a u.c.p. map `φ_E` on `C*_max(N)` that restricts to a representation of
> `C*_max(N₀)`.

The three clauses in order: `N₀`-invariance of the selected cosets, unitality
and complete positivity with contractivity, and exact multiplicativity on the
canonical unitaries of `N₀` --- which is what "restricts to a representation"
asserts, since the compression is already u.c.p. -/
theorem manuscriptSentence_stageCompressionUCP
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) :
    (∀ (h : N), h ∈ stageSubgroup N n → ∀ q : stageModel hN n,
        h • stageCoset hN n q ∈ Set.range (stageCoset hN n)) ∧
      stageMap hN n 1 = 1 ∧
      IsCompletelyPositiveOnMatrices (stageModel hN n) ⇑(stageMap hN n) ∧
      (∀ a : MaximalGroupCStar N, ‖stageMap hN n a‖ ≤ ‖a‖) ∧
      (∀ (g h : N), h ∈ exhaustion N 1 n →
        stageMap hN n (maximalGroupCStarGenerator N (g * h)) -
          stageMap hN n (maximalGroupCStarGenerator N g) *
            stageMap hN n (maximalGroupCStarGenerator N h) = 0) :=
  ⟨fun _ hh q ↦ stageCoset_smul_mem_range hN n hh q, stageMap_one hN n,
    stageMap_completelyPositive hN n, norm_stageMap_le hN n,
    fun g _ hh ↦ stage_generator_defect_eq_zero hN n g hh⟩

/-- **Printed sentence 3.**

> For `x ∈ E ∖ {1}`, the element `x` fixes no coset `nH` with `n ∈ N₀`, because
> `n⁻¹xn ∈ H` would give `x ∈ H` by normality of `H` in `N₀`; so
> `tr(φ_E(u_x)) = 0`.

The reason clause is exactly the proof of `stage_no_fixed_coset`: normality of
the packet kernel in the stage subgroup turns a fixed coset into membership of
the tested element in the kernel, which the packet forbids. -/
theorem manuscriptSentence_stageTraceZero
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) {g : N}
    (hg : g ∈ exhaustion N 1 n) (hg1 : g ≠ 1) :
    (∀ q : stageModel hN n, g • stageCoset hN n q ≠ stageCoset hN n q) ∧
      normTrace (stageModel hN n)
        (stageMap hN n (maximalGroupCStarGenerator N g)) = 0 :=
  ⟨fun q ↦ stage_no_fixed_coset hN n hg hg1 q,
    stage_generator_trace_eq_zero hN n hg hg1⟩

/-- **Printed sentence 4.**

> Along an exhaustion of `N` by finite sets `E`, the maps `φ_E` are eventually
> multiplicative on each pair of canonical unitaries, and their traces converge
> to `τ_N` on every canonical unitary; density of the group algebra and
> contractivity extend both limits to `C*_max(N)`.

The two limits are the operator-norm multiplicativity and the trace clause; the
extension to the whole algebra is
`AmenableExtensionTrace.quasidiagonalTraceModel_of_dense_generators`, and the
conclusion is the first assertion of the proposition. -/
theorem manuscriptSentence_stageLimitsExtend
    (hN : IsLocallyResiduallyFinite N) :
    (∀ g h : N, Tendsto (fun n ↦ ‖stageMap hN n
        (maximalGroupCStarGenerator N g * maximalGroupCStarGenerator N h) -
      stageMap hN n (maximalGroupCStarGenerator N g) *
        stageMap hN n (maximalGroupCStarGenerator N h)‖) atTop (nhds 0)) ∧
      (∀ g : N, Tendsto (fun n ↦
        ‖canonicalMaximalTrace N (maximalGroupCStarGenerator N g) -
          normTrace (stageModel hN n)
            (stageMap hN n (maximalGroupCStarGenerator N g))‖) atTop (nhds 0)) ∧
      IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar N ↦ canonicalMaximalTrace N a) :=
  ⟨tendsto_stage_generator_mul_op hN, tendsto_stage_generator_trace hN,
    manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal N hN⟩

end First

/-! ## Second assertion: the canonical trace of `C*_max(G)` is amenable -/

section Second

variable {G : Type} [Group G] [Countable G] (N : Subgroup G) [N.Normal]

/-- **Printed sentence 5.**

> For the second assertion, write `g ↦ ḡ` for the quotient map `G → A`, and fix
> a finite set `E ⊆ G`, a finite Følner set `F ⊆ A`, and a section
> `σ : A → G`.  For `g ∈ E` and `x ∈ F` put
> `b(g,x) = σ(ḡx)⁻¹ g σ(x) ∈ N`.

The section is `SoficByAmenablePermanence.sect`, the Følner set is `folnerSet`
at boundary tolerance `1/(n+1)`, and `b(g,x)` is the Elek--Szabó displacement
cocycle `esCocycleN`, whose values lie in `N` by construction. -/
theorem manuscriptSentence_cocycleValues
    (hA : Amenability.IsAmenable (G ⧸ N)) {n : ℕ} {g : G}
    (hg : g ∈ exhaustion G 1 n) {x : G ⧸ N} (hx : x ∈ folnerSet N hA n) :
    (folnerSet N hA n).Nonempty ∧
      esCocycleN N g x ∈ cocycleWindow N hA n :=
  ⟨folnerSet_nonempty N hA n, esCocycleN_mem_cocycleWindow N hA hg hx⟩

/-- **Printed sentence 6.**

> The subgroup `N₀` generated by these finitely many elements is residually
> finite; choose a finite quotient `θ : N₀ → Q` with `θ(b(g,x)) ≠ 1` whenever
> `b(g,x) ≠ 1`, put `H = ker θ`, and choose representatives `r_q ∈ N₀` of the
> cosets of `H` in `N₀`.

`N₀` is `cocycleSubgroup`, finitely generated by construction and residually
finite by the hypothesis on `N`; the quotient is `cocyclePacket`; `H` read
inside `G` is `stageH`; and the representatives are `Quotient.out`. -/
theorem manuscriptSentence_cocyclePacketSeparates
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) {n : ℕ} {b : ↥N}
    (hb : b ∈ cocycleWindow N hA n) (hne : b ≠ 1) :
    (cocycleSubgroup N hA n).FG ∧
      (⟨b, mem_cocycleSubgroup N hA hb⟩ : ↥(cocycleSubgroup N hA n)) ∉
        (cocyclePacket N hN hA n).subgroup :=
  ⟨cocycleSubgroup_fg N hA n,
    (cocyclePacket N hN hA n).avoids _ (mem_cocyclePacketSet N hA hb hne)⟩

/-- **Printed sentence 7.**

> The cosets `σ(x)r_qH`, `x ∈ F`, `q ∈ Q`, are pairwise distinct, since
> equality forces `x = x'` in `A` and then `q = q'`; let `T` be their set, let
> `P` be the projection of `ℓ²(G/H)` onto `ℓ²(T)`, and put
> `Φ(b) = Pλ(b)P|_{ℓ²(T)}` for `b ∈ C*_max(G)`, where `λ` is the quasi-regular
> representation.

The distinctness is `extCoset_injective`, proved in the printed order: both
sides have the same image in `G/N`, which forces the Følner coordinate, and
then the fibre.  `T` is the range of `extCoset` and `Φ` is `extMap`, the
quasi-regular compression to it. -/
theorem manuscriptSentence_cosetsDistinct
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) :
    Function.Injective (extCoset N hN hA n) :=
  extCoset_injective N hN hA n

/-- **Printed sentence 8.**

> This map is u.c.p., and for `g ∈ E` and `ḡx ∈ F`,
> `g σ(x) r_q H = σ(ḡx) r_{θ(b(g,x))q} H ∈ T`.

Unitality, complete positivity and contractivity of `Φ`, and the printed
translation formula, which is the only place the Følner condition is used
positively. -/
theorem manuscriptSentence_compressionUCPAndTranslation
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) :
    extMap N hN hA n 1 = 1 ∧
      IsCompletelyPositiveOnMatrices (extModel N hN hA n) ⇑(extMap N hN hA n) ∧
      (∀ a : MaximalGroupCStar G, ‖extMap N hN hA n a‖ ≤ ‖a‖) ∧
      (∀ (g : G), g ∈ exhaustion G 1 n → ∀ z : extModel N hN hA n,
        (QuotientGroup.mk g : G ⧸ N) * (z.1 : G ⧸ N) ∈ folnerSet N hA n →
          g • extCoset N hN hA n z ∈ Set.range (extCoset N hN hA n)) :=
  ⟨extMap_one N hN hA n, extMap_completelyPositive N hN hA n,
    norm_extMap_le N hN hA n,
    fun _ hg z hin ↦ extCoset_smul_mem_range N hN hA n hg z hin⟩

/-- **Printed sentence 9.**

> So for `g,h ∈ E` the identity
> `Φ(u_{gh}) - Φ(u_g)Φ(u_h) = Pλ(g)(1-P)λ(h)P` and the rank of
> `(1-P)λ(h)P`, at most `|{x ∈ F : h̄x ∉ F}| |Q|`, give
> `‖Φ(u_{gh}) - Φ(u_g)Φ(u_h)‖₂² ≤ |{x ∈ F : h̄x ∉ F}| / |F|`.

The rank bound is `card_escape_le`: the escaping coordinates inject into the
Følner boundary times the fibre.  The Hilbert--Schmidt consequence is
`hsNorm_extDefect_le`, stated at stage `n` against the tolerance `1/(n+1)`
that the Følner set was chosen for. -/
theorem manuscriptSentence_rankBoundGivesHS
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (g : G) {h : G}
    (hh : h ∈ exhaustion G 1 n) :
    ((QuasiRegularCompression.escape (stageH N hN hA n) (extModel N hN hA n)
        (extCoset N hN hA n) h).card : ℝ) ≤
        ((AmenableActionSofic.boundary (folnerSet N hA n)
          (QuotientGroup.mk h)).card : ℝ) *
          (Fintype.card (cocyclePacket N hN hA n).quotientModel : ℝ) ∧
      hsNorm (extModel N hN hA n)
        (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)) ≤
        Real.sqrt (1 / ((n : ℝ) + 1)) :=
  ⟨card_escape_le N hN hA n hh, hsNorm_extDefect_le N hN hA n g hh⟩

/-- **Printed sentence 10.**

> The normalized trace of `Φ(u_g)` is the fraction of points of `T` fixed by
> `g`, and for `g ∈ E ∖ {1}` it is zero: if `ḡ ≠ 1`, then `g` moves the
> `F`-coordinate of every point, and if `ḡ = 1`, then
> `gσ(x)r_qH = σ(x)r_{θ(b(g,x))q}H` with `b(g,x) = σ(x)⁻¹gσ(x) ≠ 1`, so
> `θ(b(g,x))q ≠ q`.

`ext_no_fixed_coset` runs the two printed cases in one step rather than two: a
fixed coset forces `w⁻¹g⁻¹w ∈ H ≤ N`, and reading that in `G/N` already gives
`ḡ = 1`, so the first printed case cannot occur and the second is the whole
argument. -/
theorem manuscriptSentence_traceIsFixedPointFraction
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G}
    (hg : g ∈ exhaustion G 1 n) (hg1 : g ≠ 1) :
    (∀ z : extModel N hN hA n,
        g • extCoset N hN hA n z ≠ extCoset N hN hA n z) ∧
      normTrace (extModel N hN hA n)
        (extMap N hN hA n (maximalGroupCStarGenerator G g)) = 0 :=
  ⟨fun z ↦ ext_no_fixed_coset N hN hA n hg hg1 z,
    ext_generator_trace_eq_zero N hN hA n hg hg1⟩

/-- **Printed sentence 11.**

> Taking Følner sets with `|{x ∈ F : h̄x ∉ F}|/|F| → 0` for the finitely many
> `h ∈ E`, along an exhaustion of `G` by finite sets `E`, the maps `Φ` are
> asymptotically multiplicative in normalized Hilbert--Schmidt norm and their
> traces converge to `τ_G` on the canonical unitaries; density and
> contractivity extend both limits to `C*_max(G)`.

The Følner sets with vanishing boundary ratio are built into the stage
schedule, at tolerance `1/(n+1)`.  The extension to the whole algebra is
`Quasidiagonal.amenableTraceModel_of_dense_generators`, and the conclusion is
the second assertion. -/
theorem manuscriptSentence_folnerLimitsExtend
    (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) :
    (∀ g h : G, Tendsto (fun n ↦ hsNorm (extModel N hN hA n)
        (extMap N hN hA n
            (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)))
        atTop (nhds 0)) ∧
      (∀ g : G, Tendsto (fun n ↦
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g) -
          normTrace (extModel N hN hA n)
            (extMap N hN hA n (maximalGroupCStarGenerator G g))‖)
        atTop (nhds 0)) ∧
      IsAmenableTrace
        (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  ⟨tendsto_ext_generator_mul_hs N hN hA, tendsto_ext_generator_trace N hN hA,
    manuscriptPrintedAmenableExtensionCanonicalTraceAmenable G N hN hA⟩

end Second

end

end AmenableExtensionSentences
end GroupApproximation
