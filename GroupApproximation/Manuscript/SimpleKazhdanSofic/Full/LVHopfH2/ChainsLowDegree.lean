import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Chains
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Hopf formula versus `groupHomology.H2`: the integral chains are Mathlib's (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
The integral inhomogeneous boundaries `hopfChainD`, `hopfChainD3` of `Chains.lean` are Mathlib's
`groupHomology.d₂₁`, `groupHomology.d₃₂` for the trivial representation `Rep.trivial ℤ G ℤ`.

* `hopfChainD_eq_d21`, `hopfChainD3_eq_d32`.
* `hopfChainD_cycles₂`: elements of `groupHomology.cycles₂` are killed by `hopfChainD`.
* `hopfChain_mem_boundaries₂_iff`: `groupHomology.boundaries₂` is the range of `hopfChainD3`.
-/

namespace GroupApproximation.Full.LVHopf

section ChainsLowDegree

variable {G : Type} [Group G]

/-- `hopfChainD` is `groupHomology.d₂₁` for trivial integral coefficients (l.733-735). -/
theorem hopfChainD_eq_d21 :
    (hopfChainD (G := G)) =
      LinearMap.toAddMonoidHom (groupHomology.d₂₁ (Rep.trivial ℤ G ℤ)).hom := by
  apply hopfChain_addHom_ext
  rintro ⟨g, h⟩
  exact (hopfChainD_single g h 1).trans
    (groupHomology.d₂₁_single (A := Rep.trivial ℤ G ℤ) (g, h) (1 : ℤ)).symm

/-- `hopfChainD3` is `groupHomology.d₃₂` for trivial integral coefficients (l.733-735). -/
theorem hopfChainD3_eq_d32 :
    (hopfChainD3 (G := G)) =
      LinearMap.toAddMonoidHom (groupHomology.d₃₂ (Rep.trivial ℤ G ℤ)).hom := by
  apply hopfChain_addHom_ext
  rintro ⟨g, h, k⟩
  exact (hopfChainD3_single g h k 1).trans
    (groupHomology.d₃₂_single (A := Rep.trivial ℤ G ℤ) (g, h, k) (1 : ℤ)).symm

theorem hopfChainD_apply_eq_d21 (c : G × G →₀ ℤ) :
    hopfChainD c = (groupHomology.d₂₁ (Rep.trivial ℤ G ℤ)).hom c :=
  DFunLike.congr_fun (hopfChainD_eq_d21 (G := G)) c

theorem hopfChainD3_apply_eq_d32 (c : G × G × G →₀ ℤ) :
    hopfChainD3 c = (groupHomology.d₃₂ (Rep.trivial ℤ G ℤ)).hom c :=
  DFunLike.congr_fun (hopfChainD3_eq_d32 (G := G)) c

/-- A Mathlib 2-cycle is killed by `hopfChainD`. -/
theorem hopfChainD_cycles₂ (x : ↥(groupHomology.cycles₂ (Rep.trivial ℤ G ℤ))) :
    hopfChainD (x.1 : G × G →₀ ℤ) = 0 :=
  (hopfChainD_apply_eq_d21 x.1).trans (LinearMap.mem_ker.mp x.2)

/-- A chain with `hopfChainD c = 0` is a Mathlib 2-cycle. -/
theorem hopfChain_mem_cycles₂ {c : G × G →₀ ℤ} (hc : hopfChainD c = 0) :
    c ∈ groupHomology.cycles₂ (Rep.trivial ℤ G ℤ) :=
  LinearMap.mem_ker.mpr ((hopfChainD_apply_eq_d21 c).symm.trans hc)

/-- Mathlib's 2-boundaries are the range of `hopfChainD3` (l.733-735). -/
theorem hopfChain_mem_boundaries₂_iff (c : G × G →₀ ℤ) :
    c ∈ groupHomology.boundaries₂ (Rep.trivial ℤ G ℤ) ↔ c ∈ (hopfChainD3 (G := G)).range := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp h
    exact AddMonoidHom.mem_range.mpr ⟨b, (hopfChainD3_apply_eq_d32 b).trans hb⟩
  · intro h
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp h
    exact LinearMap.mem_range.mpr ⟨b, (hopfChainD3_apply_eq_d32 b).symm.trans hb⟩

end ChainsLowDegree

end GroupApproximation.Full.LVHopf
