import GroupApproximation.BooneHigman.Metabelian.VdKRowExtEndpoint
import GroupApproximation.BooneHigman.Metabelian.VdKStabPID
import GroupApproximation.Meta.AxiomGuard

/-!
# `VdKRowExtSpecPosStatement` from stable range plus injective stability

Lane `bh-met-90f`.  The core is split into two classical inputs that do not mention row
extension, specialization, or `PolyK2StabRangeDiag`:

* **(A)** `vdkStab_PolyStableRangeStatement`: `sr(𝔽_p[x₁, …, x_k]) ≤ k + 1` (Bass's stable range
  condition, `vdkStab_StableRangeLE`, defined concretely via unimodular / reducible rows).
  The cases `k = 0` (field) and `k = 1` (PID) are **proved** in `VdKStabPID.lean`; the remaining
  input is `vdkStab_PolyStableRangeHighStatement` (`k ≥ 2`), which is Bass–Vaserstein
  `sr(R) ≤ dim R + 1` for noetherian `R`.  TRUE (classical), and strictly smaller in proof
  content than the target: it is a statement about rows over a commutative ring only.
* **(B)** `vdkStab_InjStabStatement`: for every commutative `R` with `sr(R) ≤ r` and `N ≥ r + 3`,
  `K2Stab N R : K₂(N, R) → K₂(N + 1, R)` is injective.
  LOUD: **strictly stronger** than what the target needs (the target only asks for injectivity on
  elements killed by all specializations to fewer variables, and only for `𝔽_p[x₁, …, x_k]`).
  TRUE: van der Kallen / Suslin–Tulenbaev injective stability for `K₂` gives injectivity already
  for `N ≥ sr(R) + 2`; here one extra step of room is taken.  It is **not** a restatement of the
  target: it is a general theorem about all commutative rings of finite stable range, and it is
  not routed through `polyK2StabRangeDiag_of_vdkRowExtension`.

Endpoints: `vdkStab_specPos_of_stableRange_of_injStab : (A) → (B) → VdKRowExtSpecPosStatement`,
`vdkStab_vdkRowExtension_of_high_of_injStab : (A, k ≥ 2) → (B) → VdKRowExtensionStatement`, and
the `k = 1` corollary `vdkStab_K2Stab_injective_polyOne_of_injStab`, which needs (B) only.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **(A)**: `sr(𝔽_p[x₁, …, x_k]) ≤ k + 1` for every prime `p` and every `k`. -/
def vdkStab_PolyStableRangeStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) (k + 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_PolyStableRangeStatement

/-- **(A), remaining part**: the cases `k ≥ 2` of (A) (Bass–Vaserstein).  TRUE; `k = 0, 1` are
theorems (`vdkStab_stableRangeLE_polyZero`, `vdkStab_stableRangeLE_polyOne`). -/
def vdkStab_PolyStableRangeHighStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) (k + 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_PolyStableRangeHighStatement

/-- **(B)**: injective stability of `K₂` in the range `N ≥ sr(R) + 3`.  LOUD: strictly stronger
than the target's need (see the module docstring); TRUE by van der Kallen / Suslin–Tulenbaev. -/
def vdkStab_InjStabStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r N : ℕ), vdkStab_StableRangeLE R r → r + 3 ≤ N →
    Function.Injective (K2Stab N R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_InjStabStatement

/-- The low cases `k = 0, 1` are proved, so (A) reduces to its `k ≥ 2` part. -/
theorem vdkStab_polyStableRange_of_high (h : vdkStab_PolyStableRangeHighStatement) :
    vdkStab_PolyStableRangeStatement := by
  intro p hp k
  match k with
  | 0 => exact vdkStab_stableRangeLE_polyZero p hp
  | 1 => exact vdkStab_stableRangeLE_polyOne p hp
  | k + 2 => exact h p hp (k + 2) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_polyStableRange_of_high

/-- **Endpoint**: (A) and (B) give `VdKRowExtSpecPosStatement`.  The specialization hypothesis
of the target is not used (so (B) is used in a strictly stronger form than needed). -/
theorem vdkStab_specPos_of_stableRange_of_injStab (hA : vdkStab_PolyStableRangeStatement)
    (hB : vdkStab_InjStabStatement) : VdKRowExtSpecPosStatement := by
  intro p hp k N _ hkN u _ hu
  exact hB (MvPolynomial (Fin k) (ZMod p)) (k + 1) N (hA p hp k) (by omega)
    (hu.trans (map_one (K2Stab N (MvPolynomial (Fin k) (ZMod p)))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_specPos_of_stableRange_of_injStab

/-- **Endpoint**: (A) for `k ≥ 2` and (B) give `VdKRowExtSpecPosStatement`. -/
theorem vdkStab_specPos_of_high_of_injStab (hA : vdkStab_PolyStableRangeHighStatement)
    (hB : vdkStab_InjStabStatement) : VdKRowExtSpecPosStatement :=
  vdkStab_specPos_of_stableRange_of_injStab (vdkStab_polyStableRange_of_high hA) hB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_specPos_of_high_of_injStab

/-- **Endpoint**: (A) for `k ≥ 2` and (B) give `VdKRowExtensionStatement`. -/
theorem vdkStab_vdkRowExtension_of_high_of_injStab (hA : vdkStab_PolyStableRangeHighStatement)
    (hB : vdkStab_InjStabStatement) : VdKRowExtensionStatement :=
  vdkRowExt_of_specPos (vdkStab_specPos_of_high_of_injStab hA hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_vdkRowExtension_of_high_of_injStab

/-- The case `k = 1`, from (B) alone: `K2Stab N` is injective on `K₂(N, 𝔽_p[x₁])` for `N ≥ 5`,
because `sr(𝔽_p[x₁]) ≤ 2` is proved. -/
theorem vdkStab_K2Stab_injective_polyOne_of_injStab (hB : vdkStab_InjStabStatement) (p : ℕ)
    (hp : p.Prime) (N : ℕ) (hN : 5 ≤ N) :
    Function.Injective (K2Stab N (MvPolynomial (Fin 1) (ZMod p))) :=
  hB (MvPolynomial (Fin 1) (ZMod p)) 2 N (vdkStab_stableRangeLE_polyOne p hp) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_K2Stab_injective_polyOne_of_injStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
