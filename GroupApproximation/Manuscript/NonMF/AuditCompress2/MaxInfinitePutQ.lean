import GroupApproximation.Analysis.StrictCompressionFromPrinted
import GroupApproximation.Analysis.MaximalCStarProperCompression
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# `q = uPu^*` and the proper isometry `s` in the proof of `prop:max-infinite`

`non_mf_groups_exist.tex`, lines 759–763, inside the proof of
`prop:max-infinite`. Here `G` contains a property-(T) subgroup `Γ` and an
element `t` with `tΓt⁻¹ ⊊ Γ`, `P ∈ C*_max(G)` is the image of the Kazhdan
projection of `Γ`, and `u` is the canonical unitary of `t`:

> Put $q=uPu^*$, so that $P<q$, $Pq=qP=P$, $uP=qu$, and
> $Pu^*(1-q)=Pu^*-Pu^*uPu^*=0$, and put $s=Pu^*+(1-q)$.  Then
> \[ s^*s=uPu^*+(1-q)=1,\qquad ss^*=P+(1-q)=1-(q-P)\ne1, \]

The earlier row decls were fields of the abstract `ProperProjectionCompression`
carrier, and they omitted `uP = qu` and the displayed middle expressions. The
endpoint below starts from the printed hypotheses (`Γ` has property (T) and
`Γ.map (MulAut.conj t) < Γ`). It produces the concrete `P` and states every
printed equation, with `u` fixed as `maximalGroupCStarGenerator G t` and with
`q` and `s` fixed by their printed formulas.

`P` is pinned down as the Kazhdan projection of `Γ`: it is a self-adjoint
idempotent, it is fixed by every canonical unitary of `Γ`, and it absorbs
every element fixed by those unitaries. These properties determine `P`
uniquely.

`C*_max(G)` has no global order instance (the order is only local), so the
printed `P < q` is stated algebraically: `Pq = qP = P`, `q ≠ P`, and `q - P`
is a nonzero projection.

Proof route: the strict Kazhdan compression datum built from the printed
hypotheses, as in `MaximalCStarPrintedHypotheses.exists_strictKazhdanCompression`,
but also recording `iota = Γ.subtype`. That datum supplies the absorption
identities and properness. The printed equations then follow in any star ring
(`putQ_algebra`).
-/

namespace GroupApproximation.Manuscript.NonMF.AuditCompress2

open MaximalCStarProperCompression

universe u

/-- The strict Kazhdan compression datum from the printed hypotheses, also
recording that its source map is the subgroup inclusion. The construction is
the one in `MaximalCStarPrintedHypotheses.exists_strictKazhdanCompression`. -/
theorem exists_strictKazhdanCompression_subtype {G : Type u} [Group G]
    (Γ : Subgroup G) (t : G)
    (hT : HasKazhdanPropertyT.{u, u} ↥Γ)
    (hlt : Γ.map (MulAut.conj t).toMonoidHom < Γ) :
    ∃ D : StrictKazhdanCompression ↥Γ G, D.iota = Γ.subtype ∧ D.t = t := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset ↥Γ hT
  have hTup : HasKazhdanPropertyT.{u, u + 1} ↥Γ := hT.liftUniverse
  obtain ⟨δ, hδ⟩ :=
    KazhdanGenerators.exists_pair_on_generators hTup S hsymm hgen
  have hpos : 0 < min δ 1 := lt_min hδ.1 zero_lt_one
  have hcomp : ∀ γ : ↥Γ, ∃ ζ : ↥Γ, t * Γ.subtype γ * t⁻¹ = Γ.subtype ζ := by
    intro γ
    exact ⟨⟨t * (γ : G) * t⁻¹,
      hlt.le (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom γ.2)⟩, rfl⟩
  have hstrict : ∃ a : ↥Γ,
      Γ.subtype a ∉ (Γ.subtype).range.map (MulAut.conj t).toMonoidHom := by
    obtain ⟨x, hxΓ, hxnot⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨x, hxΓ⟩, ?_⟩
    show x ∉ (Γ.subtype).range.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.range_subtype]
    exact hxnot
  exact ⟨{ iota := Γ.subtype
           t := t
           Q := S
           ε := min δ 1
           kazhdan := IsKazhdanPair.shrink hδ hpos (min_le_left _ _)
           S := S
           QS := Finset.Subset.refl S
           one_mem := hone
           symm := hsymm
           eps_le := min_le_right _ _
           generates := hgen
           compresses := hcomp
           strict := hstrict }, rfl, rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditCompress2.exists_strictKazhdanCompression_subtype

/-- The printed equations for `q = uPu^*` and `s = Pu^* + (1 - q)`, in any
star ring. They follow from `P` being a projection, `u^*u = 1`, the absorption
`Pq = qP = P`, and `q ≠ P`. -/
theorem putQ_algebra {A : Type*} [Ring A] [StarRing A] (P u : A)
    (hPsa : star P = P) (hPP : P * P = P) (huu : star u * u = 1)
    (hPq : P * (u * P * star u) = P) (hqP : u * P * star u * P = P)
    (hne : u * P * star u ≠ P) (q s : A)
    (hq : q = u * P * star u) (hs : s = P * star u + (1 - q)) :
    (P * q = P ∧ q * P = P ∧ q ≠ P) ∧
      (star (q - P) = q - P ∧ (q - P) * (q - P) = q - P ∧ q - P ≠ 0) ∧
      u * P = q * u ∧
      (P * star u * (1 - q) = P * star u - P * star u * (u * P * star u) ∧
        P * star u - P * star u * (u * P * star u) = 0) ∧
      (star s * s = u * P * star u + (1 - q) ∧ u * P * star u + (1 - q) = 1) ∧
      (s * star s = P + (1 - q) ∧ P + (1 - q) = 1 - (q - P) ∧ 1 - (q - P) ≠ 1) := by
  subst hs
  subst hq
  have hqsa : star (u * P * star u) = u * P * star u := by
    rw [star_mul, star_mul, star_star, hPsa, mul_assoc]
  have hqq : u * P * star u * (u * P * star u) = u * P * star u := by
    calc u * P * star u * (u * P * star u) = u * P * (star u * u) * P * star u := by
          noncomm_ring
      _ = u * (P * P) * star u := by rw [huu]; noncomm_ring
      _ = u * P * star u := by rw [hPP]
  have hsub : u * P * star u - P ≠ 0 := sub_ne_zero.mpr hne
  have h4 : (1 - u * P * star u) * (1 - u * P * star u) = 1 - u * P * star u := by
    calc (1 - u * P * star u) * (1 - u * P * star u)
        = 1 - u * P * star u - u * P * star u + u * P * star u * (u * P * star u) := by
          noncomm_ring
      _ = 1 - u * P * star u := by rw [hqq]; abel
  have hqPsq : (u * P * star u - P) * (u * P * star u - P) = u * P * star u - P := by
    calc (u * P * star u - P) * (u * P * star u - P)
        = u * P * star u * (u * P * star u) - u * P * star u * P
            - P * (u * P * star u) + P * P := by noncomm_ring
      _ = u * P * star u - P := by rw [hqq, hqP, hPq, hPP]; abel
  have hqPsa : star (u * P * star u - P) = u * P * star u - P := by
    rw [star_sub, hqsa, hPsa]
  have huP : u * P = u * P * star u * u := by
    calc u * P = u * P * (star u * u) := by rw [huu, mul_one]
      _ = u * P * star u * u := by noncomm_ring
  have hsplit : P * star u * (1 - u * P * star u)
      = P * star u - P * star u * (u * P * star u) := by
    rw [mul_sub, mul_one]
  have hzero : P * star u - P * star u * (u * P * star u) = 0 := by
    calc P * star u - P * star u * (u * P * star u)
        = P * star u - P * (star u * u) * P * star u := by noncomm_ring
      _ = 0 := by rw [huu, mul_one, hPP, sub_self]
  have h0 : P * star u * (1 - u * P * star u) = 0 := hsplit.trans hzero
  have hs : star (P * star u + (1 - u * P * star u)) = u * P + (1 - u * P * star u) := by
    rw [star_add, star_sub, star_one, hqsa, star_mul, star_star, hPsa]
  have h1 : u * P * (P * star u) = u * P * star u := by
    calc u * P * (P * star u) = u * (P * P) * star u := by noncomm_ring
      _ = u * P * star u := by rw [hPP]
  have h2 : u * P * (1 - u * P * star u) = 0 := by
    calc u * P * (1 - u * P * star u) = u * P - u * (P * (u * P * star u)) := by
          noncomm_ring
      _ = 0 := by rw [hPq, sub_self]
  have h3 : (1 - u * P * star u) * (P * star u) = 0 := by
    calc (1 - u * P * star u) * (P * star u) = P * star u - u * P * star u * P * star u := by
          noncomm_ring
      _ = 0 := by rw [hqP, sub_self]
  have hss : star (P * star u + (1 - u * P * star u)) * (P * star u + (1 - u * P * star u))
      = u * P * star u + (1 - u * P * star u) := by
    rw [hs]
    calc (u * P + (1 - u * P * star u)) * (P * star u + (1 - u * P * star u))
        = u * P * (P * star u) + u * P * (1 - u * P * star u)
            + (1 - u * P * star u) * (P * star u)
            + (1 - u * P * star u) * (1 - u * P * star u) := by noncomm_ring
      _ = u * P * star u + (1 - u * P * star u) := by
          rw [h1, h2, h3, h4, add_zero, add_zero]
  have hq1 : u * P * star u + (1 - u * P * star u) = 1 := by abel
  have h5 : P * star u * (u * P) = P := by
    calc P * star u * (u * P) = P * (star u * u) * P := by noncomm_ring
      _ = P := by rw [huu, mul_one, hPP]
  have h7 : (1 - u * P * star u) * (u * P) = 0 := by
    calc (1 - u * P * star u) * (u * P) = u * P - u * (P * (star u * u) * P) := by
          noncomm_ring
      _ = 0 := by rw [huu, mul_one, hPP, sub_self]
  have hss' : (P * star u + (1 - u * P * star u)) * star (P * star u + (1 - u * P * star u))
      = P + (1 - u * P * star u) := by
    rw [hs]
    calc (P * star u + (1 - u * P * star u)) * (u * P + (1 - u * P * star u))
        = P * star u * (u * P) + P * star u * (1 - u * P * star u)
            + (1 - u * P * star u) * (u * P)
            + (1 - u * P * star u) * (1 - u * P * star u) := by noncomm_ring
      _ = P + (1 - u * P * star u) := by
          rw [h5, h0, h7, h4, add_zero, add_zero]
  have hP1 : P + (1 - u * P * star u) = 1 - (u * P * star u - P) := by abel
  have hne1 : 1 - (u * P * star u - P) ≠ 1 := by
    intro h
    apply hsub
    calc u * P * star u - P = 1 - (1 - (u * P * star u - P)) := by abel
      _ = 0 := by rw [h, sub_self]
  exact ⟨⟨hPq, hqP, hne⟩, ⟨hqPsa, hqPsq, hsub⟩, huP, ⟨hsplit, hzero⟩, ⟨hss, hq1⟩,
    ⟨hss', hP1, hne1⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditCompress2.putQ_algebra

/-- **tex 759–763.** Let `Γ ≤ G` have property (T), and let `tΓt⁻¹ ⊊ Γ`.
Let `P` be the Kazhdan projection of `Γ` in `C*_max(G)`: a self-adjoint
idempotent fixed by every canonical unitary of `Γ` that absorbs every element
those unitaries fix. Let `u` be the canonical unitary of `t`. Put `q = uPu^*`
and `s = Pu^* + (1 - q)`. Then `P < q` (that is, `Pq = qP = P` and `q - P` is
a nonzero projection), `uP = qu`, `Pu^*(1-q) = Pu^* - Pu^*uPu^* = 0`,
`s^*s = uPu^* + (1-q) = 1`, and `ss^* = P + (1-q) = 1 - (q-P) ≠ 1`. -/
theorem manuscriptSentence_putQSoThatPLtQAndProperIsometry {G : Type u} [Group G]
    (Γ : Subgroup G) (t : G)
    (hT : HasKazhdanPropertyT.{u, u} ↥Γ)
    (hlt : Γ.map (MulAut.conj t).toMonoidHom < Γ) :
    ∃ P u q s : MaximalGroupCStar G,
      (IsSelfAdjoint P ∧ P * P = P ∧
        (∀ γ : ↥Γ, maximalGroupCStarGenerator G (γ : G) * P = P) ∧
        ∀ x : MaximalGroupCStar G,
          (∀ γ : ↥Γ, maximalGroupCStarGenerator G (γ : G) * x = x) → P * x = x) ∧
      u = maximalGroupCStarGenerator G t ∧
      q = u * P * star u ∧
      s = P * star u + (1 - q) ∧
      (P * q = P ∧ q * P = P ∧ q ≠ P) ∧
      (star (q - P) = q - P ∧ (q - P) * (q - P) = q - P ∧ q - P ≠ 0) ∧
      u * P = q * u ∧
      (P * star u * (1 - q) = P * star u - P * star u * (u * P * star u) ∧
        P * star u - P * star u * (u * P * star u) = 0) ∧
      (star s * s = u * P * star u + (1 - q) ∧ u * P * star u + (1 - q) = 1) ∧
      (s * star s = P + (1 - q) ∧ P + (1 - q) = 1 - (q - P) ∧ 1 - (q - P) ≠ 1) := by
  obtain ⟨D, hiota, hDt⟩ := exists_strictKazhdanCompression_subtype Γ t hT hlt
  have hshift : D.shift = maximalGroupCStarGenerator G t := by
    show maximalGroupCStarGenerator G D.t = maximalGroupCStarGenerator G t
    rw [hDt]
  have hcoe : ∀ γ : ↥Γ,
      ((D.rep γ : unitary (MaximalGroupCStar G)) : MaximalGroupCStar G) =
        maximalGroupCStarGenerator G (γ : G) := fun γ ↦
    (congrArg (fun ι : ↥Γ →* G ↦
      ((maximalGroupCStarUnitaryHom G (ι γ) : unitary (MaximalGroupCStar G)) :
        MaximalGroupCStar G)) hiota).trans rfl
  have hfix : ∀ γ : ↥Γ, maximalGroupCStarGenerator G (γ : G) * D.proj = D.proj := by
    intro γ
    rw [← hcoe γ]
    exact D.rep_mul_proj γ
  have havg : ∀ x : MaximalGroupCStar G,
      (∀ γ : ↥Γ, maximalGroupCStarGenerator G (γ : G) * x = x) → D.avg * x = x := by
    intro x hx
    have hterm : ∀ γ ∈ D.S,
        ((D.rep γ : unitary (MaximalGroupCStar G)) : MaximalGroupCStar G) * x = x := by
      intro γ _
      rw [hcoe γ]
      exact hx γ
    have hcard : ((D.S.card : ℂ)) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩
    show AbstractSpectralGap.unitaryAverage D.rep D.S * x = x
    unfold AbstractSpectralGap.unitaryAverage
    rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ D.S.card x, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hmax : ∀ x : MaximalGroupCStar G,
      (∀ γ : ↥Γ, maximalGroupCStarGenerator G (γ : G) * x = x) → D.proj * x = x := by
    intro x hx
    have h := KazhdanProjectionAbsorption.conjugated_projection_absorbs
      (u := (1 : MaximalGroupCStar G)) (p := x) D.isSelfAdjoint_avg D.rate_lt_one D.gap
      (by rw [star_one, one_mul]) (by rw [star_one, one_mul])
      (by rw [star_one, one_mul, mul_one]; exact havg x hx)
    rw [star_one, one_mul, mul_one] at h
    exact h
  have hsa := D.isSelfAdjoint_proj
  refine ⟨D.proj, maximalGroupCStarGenerator G t,
    maximalGroupCStarGenerator G t * D.proj * star (maximalGroupCStarGenerator G t),
    D.proj * star (maximalGroupCStarGenerator G t) +
      (1 - maximalGroupCStarGenerator G t * D.proj * star (maximalGroupCStarGenerator G t)),
    ⟨hsa, D.proj_mul_proj, hfix, hmax⟩, rfl, rfl, rfl, ?_⟩
  have h := putQ_algebra D.proj D.shift hsa.star_eq D.proj_mul_proj D.shift_star_mul
    D.proj_mul_conjugate D.conjugate_mul_proj D.conjugate_ne_proj _ _ rfl rfl
  rw [hshift] at h
  exact h

#audit_axioms manuscriptSentence_putQSoThatPLtQAndProperIsometry

end GroupApproximation.Manuscript.NonMF.AuditCompress2
