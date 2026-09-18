import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilPosLocalCofinal
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap is needed only at one rank per cofinal number of variables: the diagonal

Lane `bh-met-83`.  Lane `bh-met-78` (module `ElemFPK2CubeNilPosLocalCofinal`) isolated
`CubeNilPosLocalCofinalStatement`: for every prime `p` and every `K`, some `k ≥ K` and some `N₀`
are such that, for **all** ranks `N ≥ N₀`, every `u ∈ K₂(N, F_p[s_0..s_k])` killed by every
`π_i : s_i ↦ 0` meets the local condition at every maximal ideal `m` of `F_p[s_1..s_k]`.

This module shows that **one rank per instance** is enough, namely the rank `n` equal to the
cofinality parameter itself, which may lie far below the stable range `k + 5`.

* `CubeCofinalDiagStatement`: **the isolated gap**.  For every prime `p` and every `n`, some
  `k ≥ n` is such that every `u ∈ K₂(n, F_p[s_0..s_k])` killed by every `π_i` meets the local
  condition at every maximal ideal `m` of `F_p[s_1..s_k]`: some `s ∉ m` makes `v_s(ψ u)` die
  after padding.
* `cubeCofinalDiag_cubeNilPosLocalDies`: the gap gives `CubeNilPosLocalDies (F_p) k N` for all
  `k`, `N`.  Apply the gap at `n = k + N`, getting `k + d ≥ k + N`.  Patching
  (`cubeNilPosLocalDies_of_local`) gives `CubeNilPosLocalDies` at `k + d` variables and rank
  `k + N`; cone descent (`cubeNilPosLocalDies_of_add`) brings it to `k` variables, rank descent
  (`cubeNilPosLocalDies_of_le_rank`) to rank `N ≤ k + N`.
* `cubeNilPosLocalCofinal_of_cubeCofinalDiag`: **endpoint**, the gap gives
  `CubeNilPosLocalCofinalStatement` (take `k = K`, `N₀ = 0`, and `s = 1 ∉ m`).
* `cubeCofinalDiag_of_cubeNilPosLocalCofinal`: the converse, instance by instance: the instance
  of the gap at `n` is derived from the instance of `CubeNilPosLocalCofinalStatement` at `K = n`
  alone, by patching at rank `n + N₀` and rank descent to `n`.
* `polyK2CubeNilFieldPos_of_cubeCofinalDiag`, `polyK2CubeNilLocal_of_cubeCofinalDiag`,
  `polyK2OneVarNil_of_cubeCofinalDiag`: the gap wired to the earlier statements and to the
  frontier item `PolyK2OneVarNilStatement`.

## LOUD: truth check, and what is and is not removed

**LOUD: the gap is logically equivalent to `CubeNilPosLocalCofinalStatement`** (both directions
are proved here), hence to `PolyK2CubeNilFieldPosStatement` and `PolyK2CubeNilLocalStatement`.
What is removed is proof content per instance.  The instance at `n` asks for one `k ≥ n` and the
**single** rank `n`, whereas an instance of `CubeNilPosLocalCofinalStatement` asks for one `k`
and **every** rank `N ≥ N₀`.  By `cubeCofinalDiag_of_cubeNilPosLocalCofinal`, the instance of
the old gap at `K = n` implies the instance of the new gap at `n` (rank descent: low rank is the
weaker demand), while one instance of the new gap supplies only one rank, not a tail of ranks.
All rank bookkeeping (the tail `N ≥ N₀`, and the stable range `N ≥ k + 5` of the older gaps) is
now carried by the proved cone and rank descents of lane `bh-met-78`.

**Not removed**: the core is unchanged, `NK₂ = 0` in unstable form over the regular rings
`F_p[s_1..s_k]` (Quillen homotopy invariance plus a dilation lemma of Tulenbaev/Suslin type to
pass from the local rings `F_p[s_1..s_k]_m` to an element `s ∉ m` of the Quillen ideal).  No
elementary argument supplies it, and `CubeNilPosLocalCofinalStatement` is not proved here.

**Truth.**  The gap is true.  Formally it follows from `CubeNilPosLocalCofinalStatement` (proved
below), which is true by the truth check of module `ElemFPK2CubeNilPosLocalCofinal`.  Directly:
the ring `A = F_p[s_0..s_k]` is regular, so by Quillen homotopy invariance stable
`K₂(A) = K₂(F_p) = 0` (Steinberg: `K₂` of a finite field vanishes).  Stable
`K₂(A) = ker(St(A) → E(A))` is the filtered colimit of the unstable `K₂(n, A)` along padding, so
every `u ∈ K₂(n, A)`, at any rank `n`, dies after padding; then `s = 1 ∉ m` meets the local
condition (`diesAfterPadding_quillenDiff_of_diesAfterPadding`).  No rank bound is used, so the
rank `n ≤ k`, below the stable range, is harmless.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated gap (diagonal form)**: for every prime `p` and every `n`, some `k ≥ n` is
such that every `u ∈ K₂(n, F_p[s_0..s_k])` killed by every `π_i : s_i ↦ 0` meets the local
condition at every maximal ideal `m` of `F_p[s_1..s_k]`: some `s ∉ m` makes `v_s(ψ u)` die after
padding.

**LOUD: logically equivalent to `CubeNilPosLocalCofinalStatement`** (both directions proved
below), but each instance asks for a single rank `n` instead of a tail of ranks `N ≥ N₀`; the
instance at `n` follows from the old instance at `K = n`.  True (Quillen homotopy invariance for
`F_p[s_0..s_k]` and `K₂(F_p) = 0`; see the module docstring). -/
def CubeCofinalDiagStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
    ∀ u : K2n n (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ i : Fin (k + 1), K2Map (cubeKill (ZMod p) i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) (ZMod p)), m.IsMaximal →
          ∃ s : MvPolynomial (Fin k) (ZMod p), s ∉ m ∧
            K2DiesAfterPadding
              (quillenDiff (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom u) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.CubeCofinalDiagStatement

/-- The diagonal gap makes every cube element die, for every number `k + 1` of variables and
every rank `N`.  Apply the gap at `n = k + N`; patching, cone descent and rank descent. -/
theorem cubeCofinalDiag_cubeNilPosLocalDies (h : CubeCofinalDiagStatement) {p : ℕ}
    (hp : p.Prime) (k N : ℕ) : CubeNilPosLocalDies (ZMod p) k N := by
  obtain ⟨k', hk', hloc⟩ := h p hp (k + N)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right k N) hk')
  exact cubeNilPosLocalDies_of_le_rank (Nat.le_add_left N k)
    (cubeNilPosLocalDies_of_add d (cubeNilPosLocalDies_of_local hloc))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeCofinalDiag_cubeNilPosLocalDies

/-- **Endpoint**: the diagonal gap gives `CubeNilPosLocalCofinalStatement`, with `k = K`,
`N₀ = 0` and `s = 1 ∉ m`. -/
theorem cubeNilPosLocalCofinal_of_cubeCofinalDiag (h : CubeCofinalDiagStatement) :
    CubeNilPosLocalCofinalStatement := by
  intro p hp K
  refine ⟨K, le_rfl, 0, ?_⟩
  intro N _ u hu m hm
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv (ZMod p) K).toRingEquiv.toRingHom
      (cubeCofinalDiag_cubeNilPosLocalDies h hp K N u hu)) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCofinal_of_cubeCofinalDiag

/-- Conversely, instance by instance: the instance of `CubeNilPosLocalCofinalStatement` at
`K = n` gives the instance of the diagonal gap at `n` (patching at rank `n + N₀`, rank descent
to `n`, and `s = 1 ∉ m`). -/
theorem cubeCofinalDiag_of_cubeNilPosLocalCofinal (h : CubeNilPosLocalCofinalStatement) :
    CubeCofinalDiagStatement := by
  intro p hp n
  obtain ⟨k, hk, N₀, hN₀⟩ := h p hp n
  refine ⟨k, hk, ?_⟩
  intro u hu m hm
  have hD : CubeNilPosLocalDies (ZMod p) k n :=
    cubeNilPosLocalDies_of_le_rank (Nat.le_add_right n N₀)
      (cubeNilPosLocalDies_of_local (hN₀ (n + N₀) (Nat.le_add_left N₀ n)))
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hm.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (hD u hu)) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeCofinalDiag_of_cubeNilPosLocalCofinal

/-- **Endpoint**: the diagonal gap gives `PolyK2CubeNilFieldPosStatement`. -/
theorem polyK2CubeNilFieldPos_of_cubeCofinalDiag (h : CubeCofinalDiagStatement) :
    PolyK2CubeNilFieldPosStatement :=
  polyK2CubeNilFieldPos_of_cubeNilPosLocalCofinal (cubeNilPosLocalCofinal_of_cubeCofinalDiag h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilFieldPos_of_cubeCofinalDiag

/-- **Endpoint**: the diagonal gap gives `PolyK2CubeNilLocalStatement`. -/
theorem polyK2CubeNilLocal_of_cubeCofinalDiag (h : CubeCofinalDiagStatement) :
    PolyK2CubeNilLocalStatement :=
  polyK2CubeNilLocal_of_cubeNilPosLocalCofinal (cubeNilPosLocalCofinal_of_cubeCofinalDiag h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2CubeNilLocal_of_cubeCofinalDiag

/-- **Endpoint**: the diagonal gap gives the frontier item `PolyK2OneVarNilStatement`. -/
theorem polyK2OneVarNil_of_cubeCofinalDiag (h : CubeCofinalDiagStatement) :
    PolyK2OneVarNilStatement :=
  polyK2OneVarNil_of_cubeNilPosLocalCofinal (cubeNilPosLocalCofinal_of_cubeCofinalDiag h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_cubeCofinalDiag

end GroupApproximation.BooneHigman.Metabelian.ElemFP
