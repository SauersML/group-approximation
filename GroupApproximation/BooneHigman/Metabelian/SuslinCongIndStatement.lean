import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# The monic `SL₂`-block Statement (Suslin's `K₁`-Horrocks, rank-2 block form)

Lane `bh-met-93c`.  Target: `SuslinBase3CongPowStab A 2` (`SuslinBase3CongStatement.lean`) and
`SuslinBase3StabLocal A 2` (`SuslinBase3Statement.lean`), for `A = Chain.CharPPoly p k` and
`A = Chain.SIntPoly m k`, WITHOUT regularity of `A_𝔪` and WITHOUT `NK₁`.

**The residual.**  `suslinCongInd_MonicStab R`: for `τ ∈ SL₂(R[X])` whose `(0,0)` entry has a
UNIT leading coefficient, and whose constant term is stably elementary
(`diag(τ(0), 1) ∈ E₃(R)`), the stabilization `diag(τ, 1)` lies in `E₃(R[X])`.
`suslinCongInd_MonicStatement` asks this for EVERY commutative ring `R : Type`.

**Which step handles the `SL₂` block.**  The block is never row-reduced (row reduction would
lose the monic entry).  The only non-formal step is this Statement, applied to the whole
`2 × 2` block `ρ = φ(e σ)`, where `e ∈ E₂` makes the `(0,0)` entry nonzero and `φ` is Nagata's
automorphism of `A[X]` making that entry's leading coefficient a unit (`SuslinCongIndNagata`).

**Truth check (on paper only; not used as a hypothesis anywhere except as this residual).**
Let `R⟨X⟩` be `R[X]` localized at the monic polynomials.  If `f = τ₀₀` has leading coefficient
`u ∈ Rˣ`, then `u⁻¹ f` is monic, so `f ∈ R⟨X⟩ˣ` and
`τ = [[1,0],[τ₁₀ f⁻¹,1]] · diag(f, f⁻¹) · [[1, f⁻¹ τ₀₁],[0,1]]` over `R⟨X⟩`.  By the Whitehead
lemma `diag(f, f⁻¹, 1) ∈ E₃(R⟨X⟩)`, hence `diag(τ, 1) ∈ SL₃(R[X]) ∩ E₃(R⟨X⟩)`.  Suslin's
`K₁`-analogue of Horrocks' theorem (any commutative `R`, `n ≥ 3`:
`SL_n(R[X]) ∩ E_n(R⟨X⟩) ⊆ SL_n(R) · E_n(R[X])`) writes `diag(τ, 1) = s · ε`, and evaluating at
`X = 0` gives `s = diag(τ(0), 1) · ε(0)⁻¹ ∈ E₃(R)`.  So the Statement is TRUE.
Sanity checks: (i) the stabilization is essential: the rank-`2` analogue (`τ ∈ E₂(R[X])`) is
FALSE, since Cohn's `[[1 + yX, X²],[-y², 1 - yX]] ∉ E₂(k[y][X])`, and multiplying it by the
elementary Weyl element `[[0,1],[-1,0]]` on the right moves the monic entry `X²` to `(0,0)`
(its constant term is `[[0,1],[-1,0]] ∈ E₂(k[y])`); after stabilization it is in `E₃`, as the
Statement predicts (Suslin: `SL₃(k[y, X]) = E₃`); (ii) the constant-term hypothesis is
necessary: evaluating the conclusion at `X = 0` gives back `diag(τ(0), 1) ∈ E₃(R)`.

**LOUD: strength.**  This Statement is NOT an equivalent restatement of
`SuslinCongLocPowStab` / `SuslinBase3CongPowStab` / `SuslinBase3FamPowStab` /
`suslinCongPow_Statement`: it is quantified over ALL commutative rings (strictly STRONGER in
scope than any single instance of the targets), it has a GLOBAL conclusion over `R[X]` (not over
`R_𝔪[X]`), and it is not implied by the targets in this repository (going from the local
targets back to it would need Suslin's local-global principle, which is not formalized here).
What it removes from the target's proof content: Nagata's change of variables, the elementary
pre-move, the constant-term reduction to `SL₃(A) = E₃(A)`, the localization at `𝔪`, and the
congruence bookkeeping (all proved in `SuslinCongIndNagata` / `SuslinCongIndEndpoint`).
It does not mention regularity, `NK₁`, homotopy invariance, dilation or excision.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The monic `SL₂`-block Statement over one ring `R`.**  If `τ ∈ SL₂(R[X])` has a `(0,0)`
entry with unit leading coefficient and `diag(τ(0), 1) ∈ E₃(R)`, then `diag(τ, 1) ∈ E₃(R[X])`.
TRUE for every commutative ring (Suslin's `K₁`-Horrocks theorem; see the module docstring). -/
def suslinCongInd_MonicStab (R : Type*) [CommRing R] : Prop :=
  ∀ τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ,
    Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1 →
    IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff →
    stabilizeUnit (R := R) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := R)) τ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) R →
    stabilizeUnit (R := R[X]) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) R[X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_MonicStab

/-- **The residual Statement of lane `bh-met-93c`**: the monic `SL₂`-block Statement for every
commutative ring `R : Type`.  TRUE (module docstring); LOUD: stronger in scope than the target
instances, and not an equivalent restatement of any of the congruence residuals. -/
def suslinCongInd_MonicStatement : Prop :=
  ∀ (R : Type) [CommRing R], suslinCongInd_MonicStab R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_MonicStatement

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
