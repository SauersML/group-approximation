import GroupApproximation.GGT.HullSCRelatorSeparation2Published
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactCount

/-!
# Bookkeeping for Hull's published Lemmas 4.4 and 4.9

This file proves parameter monotonicity, restriction from a symmetrized family
to the one-relator symmetrized subfamily, and the exact quotient-free kernel
form of no-new-torsion.  The canonical quotient assembly is in
`HullSCCanonicalQuotientPublished`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

/-! ## Monotonicity of every published small-cancellation clause -/

/-- An `eps'`-piece is an `eps`-piece when `eps' ≤ eps`. -/
theorem IsPiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a v : List (GGT.RelLetter G Λ)}
    (h : IsPiece D W eps' a v) (heps : eps' ≤ eps) :
    IsPiece D W eps a v := by
  obtain ⟨hv, hpre, v', hv', hne, a', s', hv'pre,
    y, z, hy, hz, hval, hexcl⟩ := h
  exact ⟨hv, hpre, v', hv', hne, a', s', hv'pre,
    y, z, le_trans hy heps, le_trans hz heps, hval, hexcl⟩

/-- A published `eps'`-piece is a published `eps`-piece when `eps' ≤ eps`. -/
theorem IsPublishedPiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a a' v : List (GGT.RelLetter G Λ)}
    (h : IsPublishedPiece D W eps' a a' v) (heps : eps' ≤ eps) :
    IsPublishedPiece D W eps a a' v := by
  obtain ⟨hv, hpre, v', hv', s', hv'pre,
    y, z, hy, hz, hval, hexcl⟩ := h
  exact ⟨hv, hpre, v', hv', s', hv'pre,
    y, z, le_trans hy heps, le_trans hz heps, hval, hexcl⟩

/-- A published `eps'`-primepiece is an `eps`-primepiece when
`eps' ≤ eps`. -/
theorem IsPrimePiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a a' v : List (GGT.RelLetter G Λ)}
    (h : IsPrimePiece D W eps' a a' v) (heps : eps' ≤ eps) :
    IsPrimePiece D W eps a a' v := by
  obtain ⟨hv, middle, tail, hsplit, y, z, hy, hz, hval⟩ := h
  exact ⟨hv, middle, tail, hsplit, y, z,
    le_trans hy heps, le_trans hz heps, hval⟩

/-- Hull's `C(eps,mu,rho)` condition becomes weaker when `eps` and `rho`
decrease and `mu` increases. -/
theorem IsSmallCancellation.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsSmallCancellation D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsSmallCancellation D W eps' mu' rho' where
  admissible := h.admissible
  inv_mem := h.inv_mem
  rotate_mem := h.rotate_mem
  long := fun v hv => le_trans hrho (h.long v hv)
  deep := by
    intro v hv a ha lam hcomp hball
    exact h.deep v hv a ha lam hcomp
      (GGT.OsinComponents.relBall_mono_radius D lam hrho hball)
  pieces_small := by
    intro a v hp
    have hlt := h.pieces_small a v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle

/-- The complete Lemma 4.4 input has the same parameter monotonicity. -/
theorem IsLemma44Input.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsLemma44Input D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsLemma44Input D W eps' mu' rho' where
  toIsSmallCancellation :=
    h.toIsSmallCancellation.mono_parameters heps hmu hrho
  quasiGeodesic := h.quasiGeodesic
  publishedPiecesSmall := by
    intro a a' v hp
    have hlt := h.publishedPiecesSmall a a' v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle
  stronglyBounded := h.stronglyBounded

/-- The complete Lemma 4.9 `C₁` input has the same parameter monotonicity. -/
theorem IsLemma49Input.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsLemma49Input D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsLemma49Input D W eps' mu' rho' where
  toIsLemma44Input := h.toIsLemma44Input.mono_parameters heps hmu hrho
  primePiecesSmall := by
    intro a a' v hp
    have hlt := h.primePiecesSmall a a' v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle

/-! ## Restriction to the one-relator symmetrized family -/

/-- A member of a small-cancellation family brings its whole symmetrized
closure with it. -/
theorem symmetrized_subset_of_mem
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps rho : ℕ} {mu : ℝ} (h : IsSmallCancellation D W eps mu rho)
    {v : List (GGT.RelLetter G Λ)} (hv : v ∈ W) :
    symmetrized v ⊆ W := by
  intro z hz
  rcases Sym.exists_rotate (mem_symmetrized.mp hz) with
    ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact h.rotate_mem v hv n
  · exact h.rotate_mem (revInv v) (h.inv_mem v hv) n

/-- Hull's complete `C₁` input restricts from a symmetrized family to the
symmetrized closure of one chosen member.  This is the bridge from a family
premise to the singleton normal closure used by Theorem 7.1. -/
theorem IsLemma49Input.restrict_symmetrized
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps rho : ℕ} {mu : ℝ} (h : IsLemma49Input D W eps mu rho)
    {v : List (GGT.RelLetter G Λ)} (hv : v ∈ W) :
    IsLemma49Input D (symmetrized v) eps mu rho := by
  let V := symmetrized v
  have hsub : V ⊆ W := symmetrized_subset_of_mem h.toIsSmallCancellation hv
  have piece_mono {a z : List (GGT.RelLetter G Λ)}
      (hp : IsPiece D V eps a z) : IsPiece D W eps a z := by
    obtain ⟨hz, hpre, z', hz', hne, a', s', hz'pre,
      y, t, hy, ht, hval, hexcl⟩ := hp
    exact ⟨hsub hz, hpre, z', hsub hz', hne, a', s', hz'pre,
      y, t, hy, ht, hval, hexcl⟩
  have published_mono {a a' z : List (GGT.RelLetter G Λ)}
      (hp : IsPublishedPiece D V eps a a' z) :
      IsPublishedPiece D W eps a a' z := by
    obtain ⟨hz, hpre, z', hz', s', hz'pre,
      y, t, hy, ht, hval, hexcl⟩ := hp
    exact ⟨hsub hz, hpre, z', hsub hz', s', hz'pre,
      y, t, hy, ht, hval, hexcl⟩
  have prime_mono {a a' z : List (GGT.RelLetter G Λ)}
      (hp : IsPrimePiece D V eps a a' z) :
      IsPrimePiece D W eps a a' z := by
    obtain ⟨hz, middle, tail, hsplit, y, t, hy, ht, hval⟩ := hp
    exact ⟨hsub hz, middle, tail, hsplit, y, t, hy, ht, hval⟩
  refine
    { toIsLemma44Input :=
        { toIsSmallCancellation :=
            { admissible := fun z hz => h.admissible z (hsub hz)
              inv_mem := fun z hz =>
                mem_symmetrized.mpr (Sym.inv (mem_symmetrized.mp hz))
              rotate_mem := fun z hz n =>
                mem_symmetrized.mpr (Sym.rot n (mem_symmetrized.mp hz))
              long := fun z hz => h.long z (hsub hz)
              deep := fun z hz a ha lam hcomp =>
                h.deep z (hsub hz) a ha lam hcomp
              pieces_small := fun a z hp => h.pieces_small a z (piece_mono hp) }
          quasiGeodesic := fun z hz => h.quasiGeodesic z (hsub hz)
          publishedPiecesSmall := fun a a' z hp =>
            h.publishedPiecesSmall a a' z (published_mono hp)
          stronglyBounded := h.stronglyBounded.subset (by
            rintro a ⟨hcomp, z, hz, ha⟩
            exact ⟨hcomp, z, hsub hz, ha⟩) }
      primePiecesSmall := fun a a' z hp =>
        h.primePiecesSmall a a' z (prime_mono hp) }

end RelWord

/-! ## The exact quotient-free kernel content of Lemma 4.9 -/

/-- Every positive power that lies in `N` can be corrected by an element of
`N` to an actual trivial power upstairs.  This is the quotient-free van
Kampen-diagram conclusion in Hull Lemma 4.9. -/
def KernelPowerCorrection {G : Type u} [Group G] (N : Subgroup G) : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ N →
    ∃ k ∈ N, (g * k) ^ n = 1

/-- For a surjection, kernel power correction is equivalent to Hull's
order-preserving finite-order lift.  Thus all quotient and `orderOf`
bookkeeping is discharged before the remaining diagram argument. -/
theorem kernelPowerCorrection_iff_finiteOrderLift
    {G : Type u} [Group G] {Q : Type w} [Group Q] (q : G →* Q)
    (hsurj : Function.Surjective q) :
    KernelPowerCorrection q.ker ↔
      ∀ y : Q, IsOfFinOrder y →
        ∃ g : G, q g = y ∧ orderOf g = orderOf y := by
  constructor
  · intro hcorrect y hy
    obtain ⟨g, rfl⟩ := hsurj y
    have hgpow : g ^ orderOf (q g) ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    obtain ⟨k, hk, hpow⟩ :=
      hcorrect g (orderOf (q g)) hy.orderOf_pos hgpow
    have hqk : q k = 1 := MonoidHom.mem_ker.mp hk
    have hmap : q (g * k) = q g := by simp [map_mul, hqk]
    refine ⟨g * k, hmap, Nat.dvd_antisymm ?_ ?_⟩
    · exact orderOf_dvd_of_pow_eq_one hpow
    · rw [← hmap]
      exact orderOf_map_dvd q (g * k)
  · intro hlift g n hn hgpow
    have hqpow : (q g) ^ n = 1 := by
      rw [← map_pow, ← MonoidHom.mem_ker]
      exact hgpow
    have hgfin : IsOfFinOrder (q g) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hqpow⟩
    obtain ⟨x, hxmap, hxord⟩ := hlift (q g) hgfin
    let k : G := g⁻¹ * x
    have hk : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxmap, inv_mul_cancel]
    refine ⟨k, hk, ?_⟩
    have hgk : g * k = x := by simp [k]
    rw [hgk, ← orderOf_dvd_iff_pow_eq_one, hxord]
    exact orderOf_dvd_of_pow_eq_one hqpow

end HullSC
end GroupApproximation
