import GroupApproximation.BooneHigman.Metabelian.VdKStabEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The instance of injective `K₂` stability that the metabelian chain actually consumes

Lane `bh-met-90n`.  Lane `bh-met-90f` proved
`vdkStab_specPos_of_sr_of_injStab (hA) (hB : vdkStab_InjStabStatement) :
VdKRowExtSpecPosStatement`, where (B) is injective stability `K₂(N, R) → K₂(N + 1, R)` for
**every** commutative ring `R` with `sr(R) ≤ r` and `N ≥ r + 3`.  Reading that proof: (B) is
applied only at `R = R_k := F_p[s_1, …, s_k]`, `k > 0`, `r = k + 1`, `N ≥ k + 4`, and only to
elements `u` with `K2Stab N u = 1` that also die under every ring map `R_k → R_j`, `j < k`.

## The needed statement

`vdkInj_NeededStatement`: for `p` prime, `k > 0`, **any** `r` with `sr(R_k) ≤ r`, and
`N ≥ r + 3`, an element `u ∈ K₂(N, R_k)` that dies under every specialization to fewer
variables and has `K2Stab N u = 1` is trivial.

* `vdkInj_needed_of_injStab`: (B) implies it (only the rings `R_k` and only the elements
  killed by specializations are kept).  So it is instancewise **strictly weaker** than (B).
* `vdkInj_specPos_of_sr_of_needed`: **the reduction**, (A) + needed ⟹
  `VdKRowExtSpecPosStatement`.  `vdkInj_vdkRowExt_of_high_needed`: (A, `k ≥ 2`) + needed ⟹
  `VdKRowExtensionStatement`.

## LOUD: the truly minimal instance is equivalent to the target

Specializing further to `r = k + 1` (the only `r` the proof uses) gives back
`VdKRowExtSpecPosStatement`, which is **logically equivalent** to `VdKRowExtensionStatement`
(`vdkRowExt_iff_specPos`, lane `bh-met-90b`).  So "only the instance actually used" is an
equivalent restatement.  The needed statement is not provably equivalent to the target
because it keeps the instances `r ≤ k`, at ranks `N ≥ r + 3` that may be below `k + 4`.
This is made exact here:

* `vdkInj_needed_high_of_vdkRowExt`: the target gives every instance with `k < r` (even without
  the stable-range hypothesis).
* `vdkInj_NeededLowStatement`: the instances with `r ≤ k`.
  `vdkInj_needed_of_vdkRowExt_of_low`: target + low part ⟹ needed statement, and
  `vdkInj_low_of_needed` is the converse.  So, given (A), needed ⟺ target ∧ low part.

The low part is where the needed statement exceeds the target.  It is vacuous when
`sr(R_k) = k + 1`.  For `k = 1` this is the case (paper check, not formalized:
`sr(F_p[s]) = 2`, since `s + b (1 + s³)` is never a nonzero constant, by degree, although the row
`(s, 1 + s³)` is unimodular).  For `k ≥ 2` it is not vacuous if
`sr(R_k) ≤ k` (literature remark, no Lean depends on it: Vaserstein–Suslin bound `sr ≤ max(2, d)`
for affine algebras over finite fields).  Whether the needed statement is strictly stronger than
the target therefore depends on `sr(R_k)` exactly; it is never weaker.

## Truth

The needed statement follows from (B) (`vdkInj_needed_of_injStab`), which is van der Kallen's
injective stability `n ≥ sr + 2`, used here with one step of margin.  So it is true.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The needed statement**: injective `K₂` stability for `R_k = F_p[s_1, …, s_k]`, `k > 0`, at
every rank `N ≥ r + 3` with `sr(R_k) ≤ r`, on elements that die under every specialization to
fewer variables.  Strictly weaker than `vdkStab_InjStabStatement`; true by van der Kallen. -/
def vdkInj_NeededStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r N : ℕ, 0 < k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r → r + 3 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      (∀ j : ℕ, j < k →
        ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p),
          K2Map ψ u = 1) →
      K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_NeededStatement

/-- (B) implies the needed statement: it is (B) at the rings `R_k`, on a subset of elements. -/
theorem vdkInj_needed_of_injStab (hB : vdkStab_InjStabStatement) : vdkInj_NeededStatement :=
  fun p _ k r N _ hsr hN u _ hu ↦
    hB (MvPolynomial (Fin k) (ZMod p)) r N hsr hN
      (hu.trans (map_one (K2Stab N (MvPolynomial (Fin k) (ZMod p)))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_needed_of_injStab

/-- **The reduction**: (A) and the needed statement give `VdKRowExtSpecPosStatement`
(take `r = k + 1`). -/
theorem vdkInj_specPos_of_sr_of_needed (hA : vdkStab_PolyStableRangeStatement)
    (h : vdkInj_NeededStatement) : VdKRowExtSpecPosStatement :=
  fun p hp k N hk hkN u hψ hu ↦ h p hp k (k + 1) N hk (hA p hp k) (by omega) u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_specPos_of_sr_of_needed

/-- **Endpoint**: (A) for `k ≥ 2` and the needed statement give `VdKRowExtensionStatement`. -/
theorem vdkInj_vdkRowExt_of_high_needed (hA : vdkStab_PolyStableRangeHighStatement)
    (h : vdkInj_NeededStatement) : VdKRowExtensionStatement :=
  vdkRowExt_of_specPos (vdkInj_specPos_of_sr_of_needed (vdkStab_polyStableRange_of_high hA) h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_vdkRowExt_of_high_needed

/-- The target gives every instance of the needed statement with `k < r`: then `N ≥ k + 4`.
The stable-range hypothesis is not even used. -/
theorem vdkInj_needed_high_of_vdkRowExt (h : VdKRowExtensionStatement) (p : ℕ) (hp : p.Prime)
    (k r N : ℕ) (hk : 0 < k) (hkr : k < r) (hN : r + 3 ≤ N)
    (u : K2n N (MvPolynomial (Fin k) (ZMod p)))
    (hψ : ∀ j : ℕ, j < k →
      ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p), K2Map ψ u = 1)
    (hu : K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1) : u = 1 :=
  vdkRowExt_specPos_of_vdkRowExtension h p hp k N hk (by omega) u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_needed_high_of_vdkRowExt

/-- The **low part** of the needed statement: the instances with `r ≤ k`.  This is exactly
where the needed statement can exceed the target (see the module docstring). -/
def vdkInj_NeededLowStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r N : ℕ, 0 < k → r ≤ k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r → r + 3 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      (∀ j : ℕ, j < k →
        ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p),
          K2Map ψ u = 1) →
      K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_NeededLowStatement

/-- The needed statement contains its low part. -/
theorem vdkInj_low_of_needed (h : vdkInj_NeededStatement) : vdkInj_NeededLowStatement :=
  fun p hp k r N hk _ hsr hN u hψ hu ↦ h p hp k r N hk hsr hN u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_low_of_needed

/-- LOUD equivalence check: the target and the low part give the needed statement back.
So, given (A), the needed statement is equivalent to the target together with its low part. -/
theorem vdkInj_needed_of_vdkRowExt_of_low (h : VdKRowExtensionStatement)
    (hl : vdkInj_NeededLowStatement) : vdkInj_NeededStatement := by
  intro p hp k r N hk hsr hN u hψ hu
  rcases Nat.lt_or_ge k r with hkr | hkr
  · exact vdkInj_needed_high_of_vdkRowExt h p hp k r N hk hkr hN u hψ hu
  · exact hl p hp k r N hk hkr hsr hN u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_needed_of_vdkRowExt_of_low

end GroupApproximation.BooneHigman.Metabelian.ElemFP
