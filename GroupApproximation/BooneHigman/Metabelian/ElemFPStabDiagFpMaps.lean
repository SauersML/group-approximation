import GroupApproximation.BooneHigman.Metabelian.ElemFPStabDiagFpSpec
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2InjStabSpecial
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal stability on `ker ev₀` over `F_p`: the per-prime specialization residual

Lane `bh-met-95a`, second module.  Target: `PolyK2StabRangeDiagStatementOver (ZMod p) 4`, the
second conjunct of `P1 = PolyK2NilGapStatementOver (ZMod p) 4`.  Write
`R_k = F_p[s_1..s_k]` (`MvPolynomial (Fin k) (ZMod p)`) and `cc = constantCoeff` (`ev₀`).

## The residual

`stabDiagFp_MapsStatementOver p`: for `k ≥ 0` and `N ≥ k + 5`, an element `u ∈ K₂(N, R_{k+1})`
with `K2Stab N u = 1` is trivial, provided `K2Map φ u = 1` for **every** ring map
`φ : R_{k+1} →+* R_k`.  Unlike `stabDiagFp_SpecStatementOver`, the maps need not be augmented,
and `cc u = 1` is not assumed.

## What is proved

* `stabDiagFp_inj_of_maps`: the residual gives full injective stability of `K₂(N, R_k)` for
  `N ≥ k + 4`, `N ≥ 5`.  The proof is by induction on `k`.  The base case `k = 0` is the
  unconditional field case `vdkRowExt_fieldStab`, via `K₂(N, F_p) = 0` (big Bruhat cell).  In the
  step, each `φ u` has trivial stabilization by naturality, so the induction hypothesis kills it.
  The field case is what removes the need to carry `cc u = 1`.
* The endpoints are `stabDiagFp_stabRangeDiagOver_of_maps`, `stabDiagFp_nilGapOver_of_maps`,
  `stabDiagFp_polyK2StabRangeDiag_of_maps` and `stabDiagFp_polyK2InjectiveStability_of_maps`.
* `stabDiagFp_maps_of_spec`: every instance of the Spec residual gives the corresponding
  instance here.  This one has more hypotheses on `u`, so it is instancewise weaker.
* `stabDiagFp_maps_of_specialization`: lane `bh-met-80`'s `K2InjStabSpecializationStatement`
  gives this residual.  A map `ψ : R_{k+1} → R_j` with `j ≤ k` factors through `R_k` after
  composing with `rename (Fin.castLE)`, and `rename` has the left inverse `killCompl`.
* `stabDiagFp_maps_of_stabRangeDiagOver`: the truth check.  The target gives this residual,
  because over `F_p` with `N ≥ 5` the condition `cc u = 1` is automatic (`K₂(N, F_p) = 0`).

## LOUD: strength

As a `Prop` the residual is **logically equivalent** to the target at each prime.  The two
directions are `stabDiagFp_stabRangeDiagOver_of_maps` and `stabDiagFp_maps_of_stabRangeDiagOver`.
Any true residual with a proved reduction is equivalent to its target in this sense.

It is weaker only instancewise:
* compared with the target and with the Spec residual, it has an extra hypothesis on `u`
  (killed by every map to `R_k`);
* compared with `bh-met-80`'s statement, it has only one level `j = k` of specializations to
  kill, and it asks for `k ≥ 1` only.

It is essentially the per-prime, `k ≥ 1` form of `K2InjStabSpecializationStatement`, sharpened
to one level of maps.  **No new progress on van der Kallen's theorem is made here.**

## Remaining gap

The remaining gap is van der Kallen injective stability for `F_p[s_1..s_{k+1}]` at `N ≥ k + 5`,
restricted to elements killed by every ring map to `F_p[s_1..s_k]`.  Its lowest instance
(`k = 0`) says: `u ∈ K₂(N, F_p[s])` with `N ≥ 5`, trivial stabilization, and `u` killed by
every evaluation `s ↦ a` (every map `F_p[s] → F_p`), is trivial.

## Truth check

The target is true.  Bass gives `sr(F_p[s_1..s_k]) ≤ k + 1`.  van der Kallen gives injective
stability for `K₂` at `n ≥ sr + 2`, and here `n ≥ k + 4`.  So the residual is true by
`stabDiagFp_maps_of_stabRangeDiagOver`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The residual** (lane `bh-met-95a`): for `k ≥ 0` and `N ≥ k + 5`, an element of
`K₂(N, F_p[s_0..s_k])` with trivial stabilization that is killed by every ring map
`F_p[s_0..s_k] → F_p[s_1..s_k]` is trivial.
LOUD: equivalent to `PolyK2StabRangeDiagStatementOver (ZMod p) 4` at each prime `p`
(`stabDiagFp_stabRangeDiagOver_of_maps`, `stabDiagFp_maps_of_stabRangeDiagOver`). -/
def stabDiagFp_MapsStatementOver (p : ℕ) : Prop :=
  ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ φ : MvPolynomial (Fin (k + 1)) (ZMod p) →+* MvPolynomial (Fin k) (ZMod p),
        K2Map φ u = 1) →
      K2Stab N (MvPolynomial (Fin (k + 1)) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_MapsStatementOver

/-- **Induction on the number of variables**: the residual gives injective stability of
`K₂(N, F_p[s_1..s_k])` for `N ≥ k + 4`, `N ≥ 5`.  The base case is the unconditional field
case `vdkRowExt_fieldStab`. -/
theorem stabDiagFp_inj_of_maps (p : ℕ) (hp : p.Prime) (h : stabDiagFp_MapsStatementOver p)
    (k : ℕ) :
    ∀ N : ℕ, k + 4 ≤ N → 5 ≤ N → ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1 := by
  induction k with
  | zero =>
    intro N _ h5 u hu
    exact (injective_iff_map_eq_one _).mp (vdkRowExt_fieldStab p hp N h5) u hu
  | succ k ih =>
    intro N hN _ u hu
    exact h k N (by omega) u
      (fun φ ↦ ih N (by omega) (by omega) (K2Map φ u) (stabDiagFp_K2Stab_K2Map_eq_one φ hu)) hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_inj_of_maps
