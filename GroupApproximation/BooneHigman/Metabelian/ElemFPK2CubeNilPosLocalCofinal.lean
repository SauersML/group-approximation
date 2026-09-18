import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilPosLocalCone
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldPos
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap is needed only cofinally in the number of variables and in the rank

Lane `bh-met-78`.  Lane `bh-met-61c` (module `ElemFPK2CubeNilFieldPos`) isolated
`PolyK2CubeNilFieldPosStatement`: for every prime `p` and all `k ≥ 1`, `N ≥ k + 5`, an element
`u ∈ K₂(N, F_p[s_0..s_k])` killed by every `π_i : s_i ↦ 0` meets the local condition at every
maximal ideal `m` of `F_p[s_1..s_k]`: some `s ∉ m` makes `v_s(ψ u)` die after padding.

This module shows that the gap is needed only for *some* arbitrarily large `k` and, for each
such `k`, only for all sufficiently large `N`.  The rank bound `N ≥ k + 5` goes away.

* `CubeNilPosLocalDies R k N`: every `u ∈ K₂(N, R[s_0..s_k])` killed by every `π_i` dies after
  padding.
* `cubeNilPosLocalDies_of_succ`: `k + 1` variables give `k` variables.  This is the cone
  `s_0 ↦ s_0 s_{k+1}` of module `ElemFPK2CubeNilPosLocalCone`, for any `k`.
* `cubeNilPosLocalDies_of_add`: the same for `k + d` variables, by induction on `d`.
* `cubeNilPosLocalDies_of_le_rank`: rank `N' ≥ N` gives rank `N`.  Pad `u` to rank `N'`; the
  padded element is still killed by every `π_i`, so it dies, and so does `u`.
* `cubeNilPosLocalDies_of_local`: the local condition at rank `N` gives `CubeNilPosLocalDies`,
  by the per-element Quillen patching `cubeNilField_dies_of_local`.
* `CubeNilPosLocalCofinalStatement`: **the isolated gap**.
* `polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal`: **endpoint**, the gap gives
  `PolyK2CubeNilFieldPosStatement`.  Given `k`, `N` and `u`, take `k' ≥ k` and `N₀` from the
  gap.  Then `CubeNilPosLocalDies (F_p) k' (N + N₀)` holds; descend to `k` variables and to
  rank `N`.  So `u` dies, hence so do `ψ u` and `v_1(ψ u)`, and `s = 1 ∉ m`.
* `cubeNilPosLocalCofinal_of_polyK2CubeNilFieldPos`: the (trivial) converse.

## LOUD: truth check, and what is and is not removed

**LOUD: the gap is logically equivalent to `PolyK2CubeNilFieldPosStatement`**, and so also to
`PolyK2CubeNilLocalStatement` (both directions are proved here).  Each instance is weaker: one
instance of the gap, at a given `K`, asks for one `k ≥ K` and ranks `N ≥ N₀` with `N₀` of the
prover's choice.  An instance of the old gap asks for one fixed `k`, at every rank `N ≥ k + 5`.
The gap is smaller in proof content: it drops the rank bound `k + 5`, and it no longer asks
for every `k`.  Both are recovered here by the cone descent `k + 1 ⇒ k` (any `k`) and the rank
descent `N' ⇒ N`, proved outright.

**Not removed**: the core of the gap is still `NK₂ = 0` in unstable form over the regular rings
`F_p[s_1..s_k]` (Quillen homotopy invariance with the Tulenbaev dilation lemma, or Suslin's
dilation argument).  No elementary argument supplies it.  The outright target
`PolyK2CubeNilFieldPosStatement` is not proved here.

The gap is true: it follows from `PolyK2CubeNilFieldPosStatement` (take `k = K + 1`,
`N₀ = K + 6`), which is true by Quillen homotopy invariance for the regular ring
`F_p[s_0..s_k]` (see the truth check of module `ElemFPK2CubeNilLocal`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Descent

variable {R : Type*} [CommRing R]

variable (R) in
/-- Every `u ∈ K₂(N, R[s_0..s_k])` killed by every `π_i : s_i ↦ 0` dies after padding. -/
def CubeNilPosLocalDies (k N : ℕ) : Prop :=
  ∀ u : K2n N (MvPolynomial (Fin (k + 1)) R),
    (∀ i : Fin (k + 1), K2Map (cubeKill R i) u = 1) → K2DiesAfterPadding u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.CubeNilPosLocalDies

/-- **Cone descent.**  `k + 1` variables give `k` variables, at the same rank. -/
theorem cubeNilPosLocalDies_of_succ {k N : ℕ} (h : CubeNilPosLocalDies R (k + 1) N) :
    CubeNilPosLocalDies R k N :=
  fun u hu ↦ cubeNilPosLocal_dies_of_cone u (h _ (cubeNilPosLocal_cubeKill_cone hu))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalDies_of_succ

/-- `k + d` variables give `k` variables, at the same rank. -/
theorem cubeNilPosLocalDies_of_add {k N : ℕ} (d : ℕ) (h : CubeNilPosLocalDies R (k + d) N) :
    CubeNilPosLocalDies R k N := by
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [← Nat.add_assoc] at h
    exact ih (cubeNilPosLocalDies_of_succ h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalDies_of_add

/-- **Rank descent.**  Rank `N' ≥ N` gives rank `N`. -/
theorem cubeNilPosLocalDies_of_le_rank {k N N' : ℕ} (hN : N ≤ N')
    (h : CubeNilPosLocalDies R k N') : CubeNilPosLocalDies R k N := fun u hu ↦
  diesAfterPadding_of_diesAfterPadding_castLEEmb hN
    (h (K2IndexMap (R := MvPolynomial (Fin (k + 1)) R) (Fin.castLEEmb hN) u) fun i ↦ by
      rw [← K2IndexMap_K2Map (Fin.castLEEmb hN) (cubeKill R i) u, hu i, map_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalDies_of_le_rank

/-- **Patching.**  The local condition at every maximal ideal of `R[s_1..s_k]`, for every
`u ∈ K₂(N, R[s_0..s_k])` killed by every `π_i`, gives `CubeNilPosLocalDies R k N`. -/
theorem cubeNilPosLocalDies_of_local {k N : ℕ}
    (h : ∀ u : K2n N (MvPolynomial (Fin (k + 1)) R),
      (∀ i : Fin (k + 1), K2Map (cubeKill R i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) R), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) R, s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv R k).toRingEquiv.toRingHom u) s)) :
    CubeNilPosLocalDies R k N :=
  fun u hu ↦ cubeNilField_dies_of_local u (hu 0) (h u hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalDies_of_local

end Descent

/-- **The isolated gap**: for every prime `p` and every `K`, some `k ≥ K` and some `N₀` are such
that, for all `N ≥ N₀`, every `u ∈ K₂(N, F_p[s_0..s_k])` killed by every `π_i : s_i ↦ 0` meets
the local condition at every maximal ideal `m` of `F_p[s_1..s_k]`: some `s ∉ m` makes
`v_s(ψ u)` die after padding.

**LOUD: logically equivalent to `PolyK2CubeNilFieldPosStatement`** (both directions are proved
below).  It drops the rank bound `N ≥ k + 5` (replaced by an `N₀` of the prover's choice) and
asks only for cofinally many `k`; the core `NK₂ = 0` over `F_p[s_1..s_k]` is unchanged.  True,
since `PolyK2CubeNilFieldPosStatement` gives it (`k = K + 1`, `N₀ = K + 6`). -/
def CubeNilPosLocalCofinalStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ i : Fin (k + 1), K2Map (cubeKill (ZMod p) i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) (ZMod p)), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) (ZMod p), s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom u) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.CubeNilPosLocalCofinalStatement

/-- **Endpoint**: the cofinal gap gives `PolyK2CubeNilFieldPosStatement`.  Given `k`, `N` and
`u`, take `k + d ≥ k` and `N₀` from the gap; patching gives `CubeNilPosLocalDies` at `k + d`
variables and rank `N + N₀`, cone descent brings it to `k` variables, rank descent to rank
`N`.  So `u` dies, and `s = 1 ∉ m` works. -/
theorem polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal (h : CubeNilPosLocalCofinalStatement) :
    PolyK2CubeNilFieldPosStatement := by
  intro p hp k N _ _ u hu m hm
  obtain ⟨k', hkk', N₀, hN₀⟩ := h p hp k
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  have hD : CubeNilPosLocalDies (ZMod p) (k + d) (N + N₀) :=
    cubeNilPosLocalDies_of_local (hN₀ (N + N₀) (Nat.le_add_left N₀ N))
  have hk : CubeNilPosLocalDies (ZMod p) k N :=
    cubeNilPosLocalDies_of_le_rank (Nat.le_add_right N N₀) (cubeNilPosLocalDies_of_add d hD)
  have hdies : K2DiesAfterPadding u := hk u hu
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom hdies) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal

/-- Conversely (trivially), `PolyK2CubeNilFieldPosStatement` gives the cofinal gap: take
`k = K + 1` and `N₀ = K + 1 + 5`. -/
theorem cubeNilPosLocalCofinal_of_polyK2CubeNilFieldPos (h : PolyK2CubeNilFieldPosStatement) :
    CubeNilPosLocalCofinalStatement :=
  fun p hp K ↦ ⟨K + 1, Nat.le_succ K, K + 1 + 5, fun N hN ↦ h p hp (K + 1) N (Nat.succ_pos K) hN⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCofinal_of_polyK2CubeNilFieldPos

/-- **Endpoint**: the cofinal gap gives `PolyK2CubeNilLocalStatement`. -/
theorem polyK2CubeNilLocal_of_cubeNilPosLocalCofinal (h : CubeNilPosLocalCofinalStatement) :
    PolyK2CubeNilLocalStatement :=
  polyK2CubeNilLocal_of_cubeNilFieldPos (polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilLocal_of_cubeNilPosLocalCofinal

/-- **Endpoint**: the cofinal gap gives the frontier item `PolyK2OneVarNilStatement`. -/
theorem polyK2OneVarNil_of_cubeNilPosLocalCofinal (h : CubeNilPosLocalCofinalStatement) :
    PolyK2OneVarNilStatement :=
  polyK2OneVarNil_of_cubeNilFieldPos (polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_cubeNilPosLocalCofinal

end GroupApproximation.BooneHigman.Metabelian.ElemFP
