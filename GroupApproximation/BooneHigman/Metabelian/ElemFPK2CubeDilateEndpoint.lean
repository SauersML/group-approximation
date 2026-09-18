import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap `PolyK2CubeNilLocalStatement` from the local step and Tulenbaev dilation

Lane `bh-met-90c`, endpoint module.  Write `B = F_p[s_1..s_k]` and `ψ = finSuccEquiv`.

* `polyK2CubeNilLocal_of_k2CubeDilate (hL) (hD)`: the gap `hloc` follows from the local
  residual `hL` and the dilation residual `hD`.  Fix `u` and a maximal `m`.  `hL` gives
  `s₀ ∉ m` such that `w = ψ u` dies over `B[t]_{C s₀}`.  Put `g = v_1(w) ∈ St(N, B[t][y])`.
  - `g(y = 0) = 1` (`k2CubeDilate_evalZero_stDiff`).
  - The image of `g` over `B[t]_{C s₀}[y]` dies (`k2CubeDilate_stDies_loc_stDiff`).
  - `hD` at `s = C s₀` gives `r` such that `g((C s₀)^r y) = v_{s₀^r}(w)` dies
    (`k2CubeDilate_ringMap_scale_stDiff`).
  - `s₀^r ∉ m` because `m` is prime.
* `k2CubeDilate_local_of_polyK2CubeNil`, `k2CubeDilate_local_of_polyK2CubeNilLocal`: the local
  residual is implied by the cube gap, and so by `hloc`.  Take `s₀ = 1`: `u` dies, so `ψ u`
  and its image over any ring die.
* Wires to `PolyK2CubeNilStatement` and to the frontier item `PolyK2OneVarNilStatement`.

## LOUD: status of the residuals

This is **not** a single residual.  `hloc` is reduced to the conjunction of two statements.

* `k2CubeDilate_LocalStatement` (L) is **implied by `hloc`** (proved here), and `hloc` follows
  from L together with the dilation residual.  L is true: it follows from the cube gap with
  `s₀ = 1`, and the cube gap is `NK₂(F_p[s_1..s_k]) = 0` (Quillen).  Relative to `hloc`, L drops
  the whole Tulenbaev dilation calculation.  It asks only that `ψ u` die over `B_{s₀}[t]`, a
  localized homotopy-invariance statement with no Quillen difference and no second variable.
  Over the colimit `B_m[t]` it is `NK₂` vanishing for the regular local ring `B_m`.
* `k2CubeDilate_PolyDilationStatement` (D) contains no `K`-theory of regular rings.  It is the
  special case `A = B[t]`, `s = C s₀` of Tulenbaev's dilation lemma for Steinberg groups, which
  holds for every commutative ring in rank `≥ 5` (Tulenbaev 1982, used in the Steinberg
  local-global principle).  The padded form follows by padding to rank `max(M, 5)`.  It is
  **true**.  It is not implied by `hloc` and does not imply `hloc`.  Both sanity checks
  (nilpotent `s`, unit `s`) are proved.

Classically all these true statements are equivalent.  The split keeps the `K`-theoretic content
(L) apart from the pure Steinberg-word content (D).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Endpoint**: the cube gap `hloc` from the local residual and the dilation residual. -/
theorem polyK2CubeNilLocal_of_k2CubeDilate (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) : PolyK2CubeNilLocalStatement := by
  intro p hp k N hkN u hu m hm
  obtain ⟨s₀, hs₀, hloc⟩ := hL p hp k N hkN u hu m hm
  have hev := k2CubeDilate_evalZero_stDiff
    (SteinbergGroup.ringMap (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (u : SteinbergGroup (Fin N) (MvPolynomial (Fin (k + 1)) (ZMod p)))) 1
  have hlocg := k2CubeDilate_stDies_loc_stDiff
    (SteinbergGroup.ringMap (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (u : SteinbergGroup (Fin N) (MvPolynomial (Fin (k + 1)) (ZMod p)))) s₀ 1 hloc
  obtain ⟨r, hr⟩ := hD p k s₀ N _ hev hlocg
  refine ⟨s₀ ^ r, fun h ↦ hs₀ (hm.isPrime.mem_of_pow_mem r h), ?_⟩
  rw [k2CubeDilate_ringMap_scale_stDiff, mul_one] at hr
  rw [cubeDiagDilate_diesAfterPadding_iff, cubeDiagDilate_coe_quillenDiff, K2Map_apply]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilLocal_of_k2CubeDilate

/-- The endpoint with the full Tulenbaev dilation lemma in place of its special case. -/
theorem polyK2CubeNilLocal_of_k2CubeDilate_general (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_DilationStatement) : PolyK2CubeNilLocalStatement :=
  polyK2CubeNilLocal_of_k2CubeDilate hL (k2CubeDilate_polyDilation_of_dilation hD)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilLocal_of_k2CubeDilate_general

/-- The local residual follows from the cube gap `PolyK2CubeNilStatement`, with `s₀ = 1`. -/
theorem k2CubeDilate_local_of_polyK2CubeNil (h : PolyK2CubeNilStatement) :
    k2CubeDilate_LocalStatement := by
  intro p hp k N hkN u hu m hm
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  have hdie := diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
    (h p hp (k + 1) N (Nat.succ_pos k) (by omega) (by omega) u hu)
  rw [cubeDiagDilate_diesAfterPadding_iff, K2Map_apply] at hdie
  exact cubeDiagDilate_stDies_ringMap _ hdie

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_local_of_polyK2CubeNil

/-- **Converse**: the local residual is implied by the gap `PolyK2CubeNilLocalStatement`. -/
theorem k2CubeDilate_local_of_polyK2CubeNilLocal (h : PolyK2CubeNilLocalStatement) :
    k2CubeDilate_LocalStatement :=
  k2CubeDilate_local_of_polyK2CubeNil (polyK2CubeNil_of_cubeLocal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_local_of_polyK2CubeNilLocal

/-- **Wire**: the cube gap `PolyK2CubeNilStatement` from the two residuals. -/
theorem polyK2CubeNil_of_k2CubeDilate (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) : PolyK2CubeNilStatement :=
  polyK2CubeNil_of_cubeLocal (polyK2CubeNilLocal_of_k2CubeDilate hL hD)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNil_of_k2CubeDilate

/-- **Wire**: the frontier item `PolyK2OneVarNilStatement` from the two residuals. -/
theorem polyK2OneVarNil_of_k2CubeDilate (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) : PolyK2OneVarNilStatement :=
  polyK2OneVarNil_of_cubeLocal (polyK2CubeNilLocal_of_k2CubeDilate hL hD)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_k2CubeDilate

end GroupApproximation.BooneHigman.Metabelian.ElemFP
