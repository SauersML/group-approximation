import GroupApproximation.BooneHigman.Metabelian.SuslinZHalfTwist
import GroupApproximation.Meta.AxiomGuard

/-!
# The `ℤ[1/m]` stable-local residual, minus the elementary-monic-witness cases

Lane `bh-met-93p`.  **The target
`SuslinBase3StabLocal (Chain.SIntPoly m k) 2` is NOT closed here.**

**LOUD: the lane's route is FALSE in its one-sided form.**  The lane wants an automorphism and
elementary moves that make the leading coefficient of the first entry prime to `p`.  Here is a
counterexample.  Take `k = 1` and `A = ℤ[1/m][s]` with `m` odd.  Let `a = 2sX`, `b = 4X` and
take Cohn's matrix `σ = [[1 + ab, a²], [-b², 1 - ab]]`.  Then `det σ = 1` and `σ(0) = 1`.  Its
first column is `f = 1 + 8sX²` and `g = -16X²`.  Take any ring automorphism `φ` of `A[X]` and
any `α, β ∈ A[X]`.

**Claim.**  The leading coefficient in `X` of `φ(αf + βg)` lies in `2A`, so it is never a unit.

**Proof sketch.**  Write `h = αf + βg = α + 8X²(sα - 2β)`.  Put `P = φX`, `Q = φs`, `α' = φα`
and `β' = φβ`, so `φh = α' + 8P²(Qα' - 2β')`.  Mod `2` the inner factor is `Q̄ᾱ'`, of degree at
least `deg ᾱ'`.  A leading coefficient outside `2A` therefore forces `deg_X P = 0` and
`deg_X Q̄ = 0`.  This contradicts the surjectivity of `φ̄` on `𝔽₂[1/m][s][X]`.

Hence `σ` has no elementary monic witness with `ε' = 1`.  Over `A_𝔪`, with `𝔪 = (2, s)` and
`φ = id`, the row version `(1 + 8sX², 4s²X²)` fails as well.  That argument uses `s ∤ lc α` and
the regular sequence `(2, s)`.  Whether two-sided witnesses exist is unknown.

**Truth check** (scratchpad `bh-met-93p/`).
* `truth2.py` runs a `p`-adic Euclid heuristic.  For `k = 0` every hard case is solved (`p = 2`:
  41 of 41, `p = 3`: 50 of 50).  For `k ≥ 1` many cases stay unsolved: `k = 1`: 11 of 58 and
  4 of 57; `k = 2`: 13 of 26 and 9 of 27 (for `p = 2` and `p = 3` respectively).
* `cohn.py` confirms that the Cohn column and the Cohn row are both unsolved after 400 random
  restarts.

**What is proved.**  `SuslinZHalfTwist.lean` proves `suslinZHalf_stab_of_witness`, using
`SL₃(A) = E₃(A)` from `hA` at level `k` only.  If `σ` has an elementary monic witness then
`diag(σ, 1) ∈ E₃(A[X])` GLOBALLY, and hence at every `A_𝔪`.

**The residual `suslinZHalf_BadStatement`** is the target with one extra hypothesis: `σ` has
NO elementary monic witness (`suslinZHalf_Witness`).
* **It is TRUE**, because it is implied by the target, which is true by Suslin's theorem.  That
  is a justification only, never an input.
* **It is strictly smaller in proof content.**  Every `σ` that is monic after an automorphism
  and `E₂` moves is already discharged.  The witness is a concrete algebraic condition that does
  not involve `E₃`, localizations or the conclusion, so the residual is not a restatement.
* **It is non-vacuous at least for one-sided witnesses**, by the Cohn counterexample above.

The endpoints follow.
* `suslinZHalf_stabLocal_sInt_of_bad`
* `suslinZHalf_global_of_bad : SuslinBase3GlobalStatement`
* `suslinZHalf_indBase_of_bad : SuslinR2IndBaseStatement`
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The residual.**  `SuslinBase3StabLocal (Chain.SIntPoly m k) 2`, restricted to those `σ`
with no elementary monic witness.  TRUE (implied by the target), strictly smaller in proof
content, and not a restatement; see the module docstring. -/
def suslinZHalf_BadStatement : Prop :=
  ∀ (m k : ℕ), (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
    ∀ σ : Matrix.GeneralLinearGroup (Fin 2) (Polynomial (Chain.SIntPoly m k)),
      Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial (Chain.SIntPoly m k))) = 1 →
      elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := Chain.SIntPoly m k))
          σ = 1 →
      ¬ suslinZHalf_Witness σ →
      ∀ (𝔪 : Ideal (Chain.SIntPoly m k)) (_ : 𝔪.IsMaximal),
        stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
            (elementaryMatrixUnitMap (ι := Fin 2)
              (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k)
                (Localization.AtPrime 𝔪))) σ) ∈
          elementaryGroup (Fin 2 ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_BadStatement

/-- **The target from the residual.**  Witnessed `σ` are handled by
`suslinZHalf_stab_of_witness`; the others by `hB`. -/
theorem suslinZHalf_stabLocal_sInt_of_bad (hB : suslinZHalf_BadStatement) (m k : ℕ)
    (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') :
    SuslinBase3StabLocal (Chain.SIntPoly m k) 2 := by
  intro σ hdet h0 𝔪 h𝔪
  by_cases hW : suslinZHalf_Witness σ
  · rw [← suslinBase3_map_stabilize (κ := Unit)]
    exact elementaryGroup_map_le
      (Polynomial.mapRingHom (algebraMap (Chain.SIntPoly m k) (Localization.AtPrime 𝔪)))
      (Subgroup.mem_map_of_mem _ (suslinZHalf_stab_of_witness (hA 3 le_rfl) σ hdet hW))
  · exact hB m k hA σ hdet h0 hW 𝔪 h𝔪

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_stabLocal_sInt_of_bad

/-- `SuslinBase3GlobalStatement` from the residual. -/
theorem suslinZHalf_global_of_bad (hB : suslinZHalf_BadStatement) :
    SuslinBase3GlobalStatement :=
  suslinMonicPatch_global (suslinZHalf_stabLocal_sInt_of_bad hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_global_of_bad

/-- `SuslinR2IndBaseStatement` from the residual. -/
theorem suslinZHalf_indBase_of_bad (hB : suslinZHalf_BadStatement) :
    SuslinR2IndBaseStatement :=
  suslinMonicPatch_indBase (suslinZHalf_stabLocal_sInt_of_bad hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_indBase_of_bad

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
