import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaKazhdanOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow

/-!
# Proof sentences of the normal Kazhdan radical theorem

`non_mf_groups_exist.tex`, the proof of `thm:normal-kazhdan` and the proof of
`thm:compression-criterion` that follows it.  One declaration per printed
sentence:

* the pullback of asymptotic representations along `G → Θ(G)`;
* the agreement of the two fixed-vector ranges, from `gKg⁻¹ = K`;
* `Θ̂` as the coordinate restriction of `g ↦ q Θ(g)`;
* vanishing of the Kazhdan projection of `K` under `Θ̂`, and the positive
  element `b` it produces;
* the displayed inequality `b ≥ (κ²/|S|) 1`;
* the fixed `s₀ ∈ S` surviving on a subsequence;
* "every corona homomorphism kills `K`";
* normality of `R_{∞→2}(G)` giving `𝔇_G(L) ≤ R_{∞→2}(G)`.

The theorem itself is `NormalKazhdan`; the corner construction it consumes is
`CentralCoronaCorner`, and the corner Kazhdan order is
`CornerCoronaKazhdanOrder`.  What is added here is the individual printed step,
each named on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open MaximalCStarKazhdanProjection
open PrintedCornerCompression
open scoped InnerProductSpace Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u v w

/-! ## Passage to the corona image -/

/-- **`thm:normal-kazhdan`, sentence `a0b0530276cd`.**

> It lies in `R_{∞→2}(Θ(G))`, because every operator norm asymptotic
> representation of `Θ(G)` pulls back along `G → Θ(G)` to one of `G`.

The printed "because" is the first conjunct: restriction along `Θ` turns an
operator norm asymptotic representation of the image into one of `G`, on the
same models and with the same matrices.  The printed conclusion is the second:
the image of a subgroup of the shadow residual is again inside the shadow
residual. -/
theorem manuscriptSentence_shadowResidualPullsBackAlongQuotient
    {G H : Type} [Group G] [Group H] (Theta : G →* H) (K : Subgroup G)
    (hK : K ≤ opToHSShadowResidual G) :
    (∀ (W : OpAlmostRepresentation H) (n : ℕ) (g : G),
        (W.comap Theta).map n g = W.map n (Theta g)) ∧
      K.map Theta ≤ opToHSShadowResidual H := by
  refine ⟨fun _ _ _ ↦ rfl, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact map_opToHSShadowResidual_le Theta ⟨x, hK hx, rfl⟩

/-! ## Normality of `K` and the two fixed-vector ranges -/

/-- Conjugation by a unitary and its inverse identifies the fixed vectors of a
projection with the fixed vectors of its conjugate.  This is the range half of
the printed sentence `Θ(g) p Θ(g)* = p`, stated in the only form the printed
argument uses: a vector is in the range of the conjugated projection exactly
when its `Θ(g)*`-translate is in the range of the original. -/
theorem unitary_conj_apply_eq_self_iff {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {a b P : E →L[ℂ] E}
    (hba : b * a = 1) (hab : a * b = 1) (x : E) :
    a (P (b x)) = x ↔ P (b x) = b x := by
  constructor
  · intro h
    have h1 : b (a (P (b x))) = P (b x) :=
      calc b (a (P (b x))) = (b * a) (P (b x)) := rfl
        _ = (1 : E →L[ℂ] E) (P (b x)) := by rw [hba]
        _ = P (b x) := rfl
    rw [h] at h1
    exact h1.symm
  · intro h
    rw [h]
    calc a (b x) = (a * b) x := rfl
      _ = (1 : E →L[ℂ] E) x := by rw [hab]
      _ = x := rfl

/-- **`thm:normal-kazhdan`, sentence `9cf6f763cab0`.**

> The two ranges agree because `gKg⁻¹ = K`.

The two ranges of the printed display `Θ(g) p Θ(g)* = p`: the range of the
conjugated projection and the range of `p` itself.  `hPfix` says that the
range of `p` is the space of `K`-fixed vectors, and normality of `K` — used
exactly once, through
`manuscriptSentence173_conjugateProjectionRangeArgument_allUniverses` — says
that translating by `Θ(g)*` permutes that space. -/
theorem manuscriptSentence_conjugatedProjectionRangesAgree
    {H : Type u} [Group H] {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (rho : H →* unitary (E →L[ℂ] E)) (K : Subgroup H) [K.Normal]
    (P : E →L[ℂ] E)
    (hPfix : ∀ x : E, P x = x ↔
      ∀ k ∈ K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x)
    (g : H) (x : E) :
    ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          (P ((star ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x)) = x
      ↔ P x = x := by
  have hstar : star ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      = ((rho g⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hvu : ((rho g⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
      ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1 := by
    have h : rho g⁻¹ * rho g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg Subtype.val h
  have huv : ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
      ((rho g⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1 := by
    have h : rho g * rho g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg Subtype.val h
  rw [hstar, unitary_conj_apply_eq_self_iff hvu huv x, hPfix, hPfix]
  exact manuscriptSentence173_conjugateProjectionRangeArgument_allUniverses
    rho K g⁻¹ x

/-! ## The compressed representation `Θ̂` -/

/-- **`thm:normal-kazhdan`, sentence `ce3e951df37c`.**

> Under the coordinatewise corner identifications, `Θ̂` is the coordinate
> restriction of `g ↦ q Θ(g)`.

`Θ̂` is the corona homomorphism of the corner representation produced by
`lem:central-corona-corner`.  "Coordinate restriction of `g ↦ q Θ(g)`" is the
displayed pair of clauses: the corona class of the compressions
`Q V_n(g) Q` is the corner value `q Θ(g)`, and the polar-corrected corner maps
differ from those compressions by a norm-null sequence.  The middle clause
names the coordinate identification: the corner matrices are the lifted
`Θ`-microstates along the extracted subsequence. -/
theorem manuscriptSentence_hatThetaIsCoordinateRestriction
    (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hqstar : star q = q) (hqidem : q * q = q) (hqne : q ≠ 0)
    (hcentral : ∀ g : G,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * q =
        q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ (Q : BoundedMatrixSequence (fun n ↦ X n)) (φ : ℕ → ℕ)
      (D : PrintedCornerData G (fun k ↦ X (φ k))),
      StrictMono φ ∧
      (∀ k g, (D.V k g : Matrix (X (φ k)) (X (φ k)) ℂ) =
        CollapseUnitaryLift.liftFam X rho g (φ k)) ∧
      (∀ g : G,
        normMatrixCStarCoronaMk (fun n ↦ X n)
              (Q * unitarySequenceBounded X
                (CollapseUnitaryLift.liftFam X rho g) * Q)
            = q * ((rho g : unitary
                (NormMatrixCStarCorona (fun n ↦ X n))) :
                  NormMatrixCStarCorona (fun n ↦ X n)) ∧
        Tendsto (fun k ↦
          ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
            - D.compress k g‖) atTop (nhds 0)) := by
  obtain ⟨Q, φ, D, hφ, -, -, -, hV, -, -, -, -, -, hlast⟩ :=
    manuscriptCentralCoronaCorner G X rho q hqstar hqidem hqne hcentral
  exact ⟨Q, φ, D, hφ, hV, hlast⟩

/-! ## The Kazhdan inequality on the corner -/

/-- **`thm:normal-kazhdan`, sentence `07e1f76e9a5d`.**

> The Kazhdan projection of `K` under `Θ̂` is zero, so `Θ̂|_K` has no nonzero
> fixed vectors, and the Kazhdan inequality gives, for the positive element
> `b = |S|⁻¹ ∑_{s∈S} (Θ̂(s) - 1)*(Θ̂(s) - 1)` …

The two printed clauses.  The first is the printed implication from vanishing
of the Kazhdan projection to the absence of nonzero fixed vectors.  The second
identifies the quadratic form of the printed positive element `b` — carried
here by `unitaryGram`, which is `b` with the factor `|S|⁻¹` left off — as the
squared displacement sum the Kazhdan inequality bounds; that identification is
what makes `b` the element the next sentence's inequality is about. -/
theorem manuscriptSentence_kazhdanProjectionZeroGivesNoFixedVectors
    {K : Type w} [Group K] (D : KazhdanData K)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (hS : IsKazhdanPair.{w, v} K D.S D.kappa)
    (Theta : K →* unitary (E →L[ℂ] E))
    (hzero : KazhdanProjectionImageZero D Theta) :
    (∀ y : E,
        (∀ k : K, ((Theta k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y = y) →
          y = 0) ∧
      ∀ x : E,
        (⟪x, unitaryGram D.S
            (fun s ↦ ((Theta s : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
              x⟫_ℂ).re
          = ∑ s ∈ D.S,
              ‖((Theta s : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x - x‖ ^ 2 :=
  ⟨noInvariantVectors_of_kazhdanProjectionImageZero D hS Theta hzero,
    fun x ↦ re_inner_unitaryGram D.S
      (fun s ↦ ((Theta s : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x⟩

/-- **`thm:normal-kazhdan`, sentence `0b6f90d84465`.**

> …the inequality `b ≥ (κ²/|S|) 1`.

The printed display, in the quadratic-form reading of the operator order: the
average squared displacement operator dominates `κ²/|S|` times the identity on
every vector.  `unitaryGram D.S Θ̂` is `|S| b`, so the printed normalization is
restored by the factor `|S|⁻¹` on the right. -/
theorem manuscriptSentence_kazhdanAverageLowerBound
    {K : Type w} [Group K] (D : KazhdanData K)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (hS : IsKazhdanPair.{w, v} K D.S D.kappa)
    (Theta : K →* unitary (E →L[ℂ] E))
    (hzero : KazhdanProjectionImageZero D Theta) (x : E) :
    D.kappa ^ 2 / D.S.card * ‖x‖ ^ 2
      ≤ (D.S.card : ℝ)⁻¹ *
        (⟪x, unitaryGram D.S
            (fun s ↦ ((Theta s : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
              x⟫_ℂ).re := by
  have hno := noInvariantVectors_of_kazhdanProjectionImageZero D hS Theta hzero
  have hbase := kappa_sq_mul_norm_sq_le_re_inner_unitaryGram hS Theta hno x
  have hnn : (0 : ℝ) ≤ (D.S.card : ℝ)⁻¹ := by positivity
  calc D.kappa ^ 2 / D.S.card * ‖x‖ ^ 2
      = (D.S.card : ℝ)⁻¹ * (D.kappa ^ 2 * ‖x‖ ^ 2) := by ring
    _ ≤ (D.S.card : ℝ)⁻¹ *
        (⟪x, unitaryGram D.S
            (fun s ↦ ((Theta s : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
              x⟫_ℂ).re := mul_le_mul_of_nonneg_left hbase hnn

/-! ## The surviving Kazhdan-set element -/

/-- **`thm:normal-kazhdan`, sentence `fafd069dd440`.**

> After passing to a subsequence, one fixed `s₀ ∈ S` then stays a positive
> Hilbert--Schmidt distance from `I_{r_n}`.

The hypothesis is the previous display — the averaged normalized
Hilbert--Schmidt masses of `W_n(s) - I_{r_n}` stay above a positive constant —
and the conclusion is the printed extraction: one element of the finite
Kazhdan set, fixed once and for all, together with a literal strictly
increasing subsequence on which its normalized Hilbert--Schmidt distance from
the corner identity stays above that positive constant. -/
theorem manuscriptSentence_fixedElementStaysPositiveDistance
    {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (Y : ℕ → FiniteModel) (W : ∀ n, ι → Matrix (Y n) (Y n) ℂ)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ n, c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq (Y n) (W n s - 1)) :
    ∃ s0 ∈ S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n, 0 < c ∧ c ≤ hsNormSq (Y (phi n)) (W (phi n) s0 - 1) := by
  obtain ⟨s0, hs0, phi, hphi, hbound⟩ :=
    manuscriptSentence182_fixedElementSubsequence S hS
      (fun n s ↦ hsNormSq (Y n) (W n s - 1)) c h
  exact ⟨s0, hs0, phi, hphi, fun n ↦ ⟨hc, hbound n⟩⟩

/-- **`thm:normal-kazhdan`, sentence `0e9c96749569`.**

> Thus every corona homomorphism kills `K`.

The conclusion of the printed proof, in the printed words: for every sequence
of positive matrix coordinates and every homomorphism of `G` into the unitary
group of the corresponding norm matrix corona, every element of `K` goes to
the identity. -/
theorem manuscriptSentence_everyCoronaHomomorphismKillsK
    {G : Type} [Group G] [Countable G] (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKR : K ≤ opToHSShadowResidual G)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (k : G) (hk : k ∈ K) :
    rho k = 1 := by
  have hres : K ≤ actualCoronaMFResidual G :=
    manuscriptNormalKazhdanRadical G K hK hKR
  exact (mem_actualCoronaMFResidual_iff).mp (hres hk) X hX rho

/-! ## Back to `thm:compression-criterion` -/

/-- **`thm:compression-criterion`, sentence `b7d7a6f48e59`.**

> So normality of `R_{∞→2}(G)` gives `𝔇_G(L) ≤ R_{∞→2}(G)`.

The three printed ingredients in the printed order: `R_{∞→2}(G)` is normal;
every displayed generator `[ucu⁻¹, ℓ]` of `𝔇_G(L)` lies in it, by
`cor:defect-hs`; and therefore so does the whole normal closure they
generate. -/
theorem manuscriptSentence_normalityGivesDefectInclusion
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    (opToHSShadowResidual G).Normal ∧
      (∀ u ∈ compressionSet L, ∀ c : G, (∀ l ∈ L, Commute c l) →
        ∀ l ∈ L, ⁅u * c * u⁻¹, l⁆ ∈ opToHSShadowResidual G) ∧
      printedDefect L ≤ opToHSShadowResidual G := by
  refine ⟨opToHSShadowResidual_normal, ?_,
    printedDefect_le_opToHSShadowResidual_direct L hL⟩
  intro u hu c hc l hl
  exact manuscriptCompressionDefectHSInvisible G L hL u hu c hc l hl

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
