import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefineStep
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the corner refinement at a bad corner (part 3, assembly)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `badCornerRefinement_of_monogonCorner`
proves `BadCornerRefinementStatement` (`Piece06/Doubling`, gap 5) from the strictly smaller
`MonogonCornerStatement` (`Piece06/CornerRefine`).

## Proof

Let `c = K.boundary.cycle`, `d₀ ∈ c`, `e₀ = next d₀`, `σ e₀ ≠ α d₀`.

1. **First corner.**  `e₀ ∈ c`, so `face (α e₀) ∉ K.faces`; (H2) holds by `hone_start`.
   `cornerDigon_of_monogonCorner` gives `R₁ : X → X₁`, `K₁` with `c₁ = c.map R₁`, `p₁ > m₁`, all
   intermediate darts of the lifted step `R₁ e₀ ↦ R₁ (σ e₀)` new, and the G-digon
   `g₁ = face₁ (α₁ x₁)`, `x₁ = σ₁^m₁ (R₁ e₀)`, whose old darts are among `α e₀`, `σ e₀`.
2. **Second corner** at `z = σ₁⁻¹ (R₁ (α d₀))`.  `face₁ (α₁ z) = face₁ (R₁ (α d₀)) =
   face₁ (α₁ (R₁ d₀))` and `R₁ d₀ ∈ c₁` (`notMem_faces_second`); (H2) by `hone_second`.  Get
   `R₂ : X₁ → X₂`, `K₂`, `p₂ > m₂`, `y = σ₂^m₂ (R₂ z)` with G-digon `g₂ = face₂ (α₂ y)`, old darts
   among `α₁ z`, `σ₁ z`, and every other G-face of `X₁` stays a G-face.
3. **The first digon survives** (`corner_faces_ne`): `g₁ ≠ face₁ (α₁ z)`, since otherwise
   `R₁ (α d₀)` lies on `g₁`, so `α d₀ = α e₀` (then `d₀ = e₀ = next d₀`, impossible as `|c| ≥ 2`)
   or `α d₀ = σ e₀` (excluded).  Hence `face₂ (R₂ (α₁ x₁))` is a G-face of `X₂`.
4. **Sector** for `R = R₁.comp R₂` (`refinedGoodSector_of_twoDigons`).  Lift `m₁` steps by
   `R₂.lift_pow`: `σ₂^K (R (e₀)) = R₂ x₁`; take `x = σ₂^K (R e₀)`, `m = K`, `q = p₂ - m₂`.
   New darts before `x`: an intermediate `b < K` pulls back to an intermediate `t < m₁ < p₁` of step
   1; at `b = K` the dart is `R₂ x₁` with `0 < m₁ < p₁` (`first_newDarts`).  The equation
   `σ₂^q y = σ₂^p₂ (R₂ z) = R₂ (σ₁ z) = R (α d₀)`, and new darts after `y` are intermediates
   `t + m₂ < p₂` of step 2.  `α₂ x = R₂ (α₁ x₁)`, so its face is a G-face; `face₂ (α₂ y) = g₂` is a
   G-face; they differ since an old dart `α₁ x₁` on `g₂` lies in `{α₁ z, σ₁ z}`, whose faces equal
   `face₁ (α₁ z) ≠ g₁`.  Repeated visits, `O`-equivalence, the invariants and `c₂ = c.map R`
   compose.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated Equiv
open scoped Classical

section Powers

variable (M : CombMap.{v})

theorem sigma_pow_add_apply (t m : ℕ) (x : M.Dart) :
    (M.sigma ^ (t + m)) x = (M.sigma ^ t) ((M.sigma ^ m) x) := by
  rw [pow_add, Perm.mul_apply]

theorem sigma_pow_sub_apply {p m : ℕ} (hmp : m < p) (x : M.Dart) :
    (M.sigma ^ (p - m)) ((M.sigma ^ m) x) = (M.sigma ^ p) x := by
  rw [← sigma_pow_add_apply, Nat.sub_add_cancel hmp.le]

end Powers

/-- **The darts up to the lifted first corner are new.** -/
theorem first_newDarts {M M₁ M₂ : CombMap.{v}} (R₁ : RotationRefinement M M₁)
    (R₂ : RotationRefinement M₁ M₂) {e : M.Dart} {p m Kl : ℕ} (hmp : m < p)
    (hpmid : ∀ t, 0 < t → t < p → ∀ w, (M₁.sigma ^ t) (R₁.map e) ≠ R₁.map w)
    (hKpos : 0 < Kl → 0 < m)
    (hKeq : (M₂.sigma ^ Kl) (R₂.map (R₁.map e)) = R₂.map ((M₁.sigma ^ m) (R₁.map e)))
    (hKmid : ∀ b, 0 < b → b < Kl → ∀ w, (M₂.sigma ^ b) (R₂.map (R₁.map e)) = R₂.map w →
      ∃ t, 0 < t ∧ t < m ∧ (M₁.sigma ^ t) (R₁.map e) = w) :
    ∀ t, 0 < t → t ≤ Kl → ∀ w, (M₂.sigma ^ t) ((R₁.comp R₂).map e) ≠ (R₁.comp R₂).map w := by
  intro t ht htK w hw
  have hw' : (M₂.sigma ^ t) (R₂.map (R₁.map e)) = R₂.map (R₁.map w) := hw
  rcases Nat.lt_or_ge t Kl with htlt | htge
  · obtain ⟨s, hs, hsm, hsw⟩ := hKmid t ht htlt (R₁.map w) hw'
    exact hpmid s hs (Nat.lt_trans hsm hmp) w hsw
  · have htK' : t = Kl := Nat.le_antisymm htK htge
    rw [htK'] at hw'
    exact hpmid m (hKpos (by omega)) hmp w (R₂.injective (hKeq.symm.trans hw'))

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- **The good refined sector from two corner digons.** -/
theorem refinedGoodSector_of_twoDigons {X X₁ X₂ : DiscDiagram.{u, w, v} W}
    (R₁ : RotationRefinement X.toCombMap X₁.toCombMap)
    (R₂ : RotationRefinement X₁.toCombMap X₂.toCombMap) {d₀ e₀ : X.toCombMap.Dart}
    {z : X₁.toCombMap.Dart} {p₁ m₁ Kl p₂ m₂ : ℕ} (hmp₁ : m₁ < p₁)
    (hpmid₁ : ∀ t, 0 < t → t < p₁ → ∀ w, (X₁.toCombMap.sigma ^ t) (R₁.map e₀) ≠ R₁.map w)
    (hKpos : 0 < Kl → 0 < m₁)
    (hKeq : (X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀)) =
      R₂.map ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀)))
    (hKmid : ∀ b, 0 < b → b < Kl → ∀ w,
      (X₂.toCombMap.sigma ^ b) (R₂.map (R₁.map e₀)) = R₂.map w →
        ∃ t, 0 < t ∧ t < m₁ ∧ (X₁.toCombMap.sigma ^ t) (R₁.map e₀) = w)
    (hmp₂ : m₂ < p₂) (hz : X₁.toCombMap.sigma z = R₁.map (X.toCombMap.alpha d₀))
    (hpz₂ : (X₂.toCombMap.sigma ^ p₂) (R₂.map z) = R₂.map (X₁.toCombMap.sigma z))
    (hpmid₂ : ∀ t, 0 < t → t < p₂ → ∀ w, (X₂.toCombMap.sigma ^ t) (R₂.map z) ≠ R₂.map w)
    (hG₂ : IsGFaceOf X₂
      (X₂.toCombMap.faceOf (X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ m₂) (R₂.map z)))))
    (honly₂ : ∀ w, X₂.toCombMap.faceOf (R₂.map w) =
        X₂.toCombMap.faceOf (X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ m₂) (R₂.map z))) →
      w = X₁.toCombMap.alpha z ∨ w = X₁.toCombMap.sigma z)
    (hGx : IsGFaceOf X₂ (X₂.toCombMap.faceOf
      (R₂.map (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))))))
    (hne' : X₁.toCombMap.faceOf (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))) ≠
      X₁.toCombMap.faceOf (X₁.toCombMap.alpha z)) :
    RefinedGoodSector X X₂ (R₁.comp R₂) d₀ e₀ := by
  have hax : X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀))) =
      R₂.map (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))) :=
    (congrArg X₂.toCombMap.alpha hKeq).trans (R₂.alpha_map _)
  have hfx := congrArg X₂.toCombMap.faceOf hax
  unfold RefinedGoodSector
  refine ⟨(X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀)),
    (X₂.toCombMap.sigma ^ m₂) (R₂.map z), Kl, p₂ - m₂, rfl,
    first_newDarts R₁ R₂ hmp₁ hpmid₁ hKpos hKeq hKmid, Nat.sub_pos_of_lt hmp₂,
    (sigma_pow_sub_apply _ hmp₂ _).trans (hpz₂.trans (congrArg R₂.map hz)),
    fun t ht htq w hw => hpmid₂ (t + m₂) (by omega) (by omega) (R₁.map w)
      ((sigma_pow_add_apply _ t m₂ _).trans hw),
    fun h => ?_, fun h => hGx.1 (hfx.symm.trans h), hG₂.1,
    fun C hC h => hGx.2 C hC (h.trans hfx), hG₂.2⟩
  rcases honly₂ _ (hfx.symm.trans h) with h1 | h1
  · exact hne' (congrArg X₁.toCombMap.faceOf h1)
  · exact hne' ((congrArg X₁.toCombMap.faceOf h1).trans (faceOf_sigma_eq_alpha _ z))

/-- (H1) at the second corner. -/
theorem notMem_faces_second {X X₁ : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    {K : CellPocketFaceSet D eps X i j} {i₁ j₁ : Fin X₁.rCellCount}
    {K₁ : CellPocketFaceSet D eps X₁ i₁ j₁} {R₁ : RotationRefinement X.toCombMap X₁.toCombMap}
    (hcyc₁ : K₁.boundary.cycle = K.boundary.cycle.map R₁.map) {d₀ : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) :
    X₁.toCombMap.faceOf (X₁.toCombMap.alpha
      (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀)))) ∉ K₁.faces := by
  have hd₁ : R₁.map d₀ ∈ K₁.boundary.cycle := by
    rw [hcyc₁]
    exact List.mem_map.mpr ⟨d₀, hd₀, rfl⟩
  obtain ⟨-, hout⟩ := (K₁.boundary.cycle_mem_iff _).mp hd₁
  rw [faceOf_alpha_sigma_symm, ← R₁.alpha_map]
  exact hout

/-- **The first digon is not the second corner face.** -/
theorem corner_faces_ne {X X₁ : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (R₁ : RotationRefinement X.toCombMap X₁.toCombMap)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hne : X.toCombMap.sigma e₀ ≠ X.toCombMap.alpha d₀) {x₁ : X₁.toCombMap.Dart}
    (honly₁ : ∀ w, X₁.toCombMap.faceOf (R₁.map w) =
        X₁.toCombMap.faceOf (X₁.toCombMap.alpha x₁) →
      w = X.toCombMap.alpha e₀ ∨ w = X.toCombMap.sigma e₀) :
    X₁.toCombMap.faceOf (X₁.toCombMap.alpha x₁) ≠ X₁.toCombMap.faceOf
      (X₁.toCombMap.alpha (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀)))) := by
  intro h
  rcases honly₁ (X.toCombMap.alpha d₀)
      ((faceOf_alpha_sigma_symm X₁.toCombMap _).symm.trans h.symm) with h1 | h1
  · exact next_ne_self_of_two_le K.boundary.cycle_nodup (two_le_cycle_length K) hd₀
      (hnext₀.trans (X.toCombMap.alpha.injective h1).symm)
  · exact hne h1.symm

/-- **Gap 5 from the monogon corner.**  `BadCornerRefinementStatement` follows from the strictly
smaller `MonogonCornerStatement`. -/
theorem badCornerRefinement_of_monogonCorner (hmono : MonogonCornerStatement.{u, w, v}) :
    BadCornerRefinementStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hlabel hK hij hfirst hsecond d₀ e₀ hd₀ hnext₀ hne
  have hinv : PocketInvariants K := ⟨hlabel, hK, hij, hfirst, hsecond⟩
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem _ _ hd₀
  obtain ⟨-, hs₁⟩ := (K.boundary.cycle_mem_iff e₀).mp he₀
  obtain ⟨X₁, i₁, j₁, K₁, R₁, ⟨E₁⟩, hinv₁, hvis₁, hcyc₁, p₁, m₁, hmp₁, hpz₁, hpmid₁, hG₁, honly₁,
      htr₁⟩ := cornerDigon_of_monogonCorner X hmono K e₀ hinv hs₁
    (hone_start K.boundary.cycle_nodup hd₀ hnext₀ hne)
  obtain ⟨X₂, i₂, j₂, K₂, R₂, ⟨E₂⟩, ⟨hlabel₂, hK₂, hij₂, hfirst₂, hsecond₂⟩, hvis₂, hcyc₂, p₂, m₂,
      hmp₂, hpz₂, hpmid₂, hG₂, honly₂, htr₂⟩ :=
    cornerDigon_of_monogonCorner X₁ hmono K₁
      (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀))) hinv₁
      (notMem_faces_second hcyc₁ hd₀)
      (hone_second R₁ hcyc₁ K.boundary.cycle_nodup hd₀ hnext₀ hne
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hmp₁) hpz₁ hpmid₁)
  have hne' := corner_faces_ne K R₁ hd₀ hnext₀ hne honly₁
  obtain ⟨Kl, -, hKpos, hKeq, hKmid⟩ := R₂.lift_pow (R₁.map e₀) m₁
  exact ⟨X₂, i₂, j₂, K₂, R₁.comp R₂, ⟨OEquivalentDiscDiagram.trans E₁ E₂⟩, hlabel₂, hij₂, hK₂,
    hfirst₂, hsecond₂, hvis₂.trans hvis₁,
    hcyc₂.trans ((congrArg (List.map R₂.map) hcyc₁).trans List.map_map),
    refinedGoodSector_of_twoDigons R₁ R₂ hmp₁ hpmid₁ hKpos hKeq hKmid hmp₂
      (Equiv.apply_symm_apply X₁.toCombMap.sigma (R₁.map (X.toCombMap.alpha d₀)))
      hpz₂ hpmid₂ hG₂ honly₂ (htr₂ _ hG₁ hne') hne'⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.first_newDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.refinedGoodSector_of_twoDigons
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.badCornerRefinement_of_monogonCorner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.sigma_pow_add_apply
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.sigma_pow_sub_apply
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.notMem_faces_second
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.corner_faces_ne
