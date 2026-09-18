import GroupApproximation.BooneHigman.Metabelian.ElemFPEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SplitStab
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F_p[s_1..s_k]) = 0` split into stability, homotopy invariance and the field case

Lane `bh-met-14`.  Lane `bh-met-06` (`ElemFPEndpoint`) reduced the finite presentation of
`E_N(F_p[s_1..s_k])` to `PolynomialFpK2VanishingStatement`: `K2 (Fin N) R_k = ⊥` for `p` prime,
`N ≥ k + 4` and `N ≥ 5`, where `R_k = MvPolynomial (Fin k) (ZMod p)`.  The classical proof has
three independent inputs, stated here in the `SteinbergBasic` model.

* `PolyK2InjectiveStabilityStatement`: `K2Stab N R_k : K₂(N, R_k) →* K₂(N+1, R_k)` is injective
  for `N ≥ k + 4`, `N ≥ 5`.  Truth: `R_k` is noetherian of Krull dimension `k`, so its Bass
  stable rank is at most `k + 1`.  Van der Kallen (injective stability for `K₂`, 1976) gives
  injectivity for `N ≥ sr + 2 = k + 3`; even the older Dennis bound `N ≥ sr + 3 = k + 4` covers
  the range.  So the bound `k + 4` is safe with one step of margin.
* `PolyK2HomotopyStatement`: every `u ∈ K₂(N, R_k)` is, after padding to some rank `M ≥ N`, the
  image of some `v ∈ K₂(M, F_p)` under `MvPolynomial.C`.  Truth: stable `K₂` is the filtered
  colimit of the unstable `K₂(n, -)`, and Quillen's homotopy invariance for the regular ring
  `F_p` gives stable `K₂(R_k) = K₂(F_p)` via `C`.  The injective half is free: `C` has the
  retraction `constantCoeff` (`ElemFPK2Homotopy.K2Map_C_injective`).
* `FieldK2VanishingStatement`: `K2 (Fin N) (ZMod p) = ⊥` for `N ≥ 5` (lane `bh-met-15`).
  Truth: Matsumoto (`K₂(n, F) = K₂(F)` for `n ≥ 3`) and Steinberg (`K₂(F_q) = 0`).

`polynomialFpK2Vanishing_of_split` proves the target from the three.  Take `u ∈ K₂(N, R_k)`.
Homotopy gives `M ≥ N` and `v` with `pad u = C v`.  The field case makes `v = 1`, so `pad u = 1`.
Injective stability from rank `N` telescopes (`GroupApproximation.Full.LVH2GL3.
eq_one_of_indexMap_eq_one`), which gives `u = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Injective stability** for `K₂` of `F_p[s_1..s_k]` from rank `k + 4` (and `5`) on. -/
def PolyK2InjectiveStabilityStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 4 ≤ N → 5 ≤ N →
    Function.Injective (K2Stab N (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2InjectiveStabilityStatement

/-- **Homotopy invariance**, finite-stage form: every element of `K₂(N, F_p[s_1..s_k])` becomes,
after padding to some rank `M ≥ N`, a constant element `C v` with `v ∈ K₂(M, F_p)`. -/
def PolyK2HomotopyStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)), ∃ M : ℕ, ∃ hNM : N ≤ M,
      ∃ v : K2n M (ZMod p),
        K2IndexMap (R := MvPolynomial (Fin k) (ZMod p)) (Fin.castLEEmb hNM) u =
          K2Map (I := Fin M) (MvPolynomial.C : ZMod p →+* MvPolynomial (Fin k) (ZMod p)) v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2HomotopyStatement

/-- **The field case**: `K₂(N, F_p) = 0` for `p` prime and `N ≥ 5`. -/
def FieldK2VanishingStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N → K2 (Fin N) (ZMod p) = ⊥

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2VanishingStatement

/-- **The split.**  Injective stability, homotopy invariance and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_split (hstab : PolyK2InjectiveStabilityStatement)
    (hhom : PolyK2HomotopyStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement := by
  intro p hp k N hkN h5N
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
  obtain ⟨M, hNM, v, huv⟩ := hhom p hp k N hkN h5N ⟨g, hg⟩
  have hv : v = 1 := eq_one_of_K2_eq_bot (hfield p hp M (h5N.trans hNM)) v
  rw [hv, map_one] at huv
  refine GroupApproximation.Full.LVH2GL3.eq_one_of_indexMap_eq_one
    (fun m hm ↦ k2StabInjective_of_injective (hstab p hp k m (hkN.trans hm) (h5N.trans hm)))
    ((mem_K2_iff g).mp hg) M hNM ?_
  exact congrArg Subtype.val huv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_split

end GroupApproximation.BooneHigman.Metabelian.ElemFP
