import GroupApproximation.BooneHigman.Metabelian.SuslinR1PrimeMonic
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicNagataLead
import GroupApproximation.Meta.AxiomGuard

/-!
# The monic Statement over `ℤ[1/m]`: the Nagata step

Lane `bh-met-91n`.  Target: `suslinR1Prime_MonicStatement` (`SuslinR1PrimeMonic.lean`).
NOT closed.  Proved here: the Nagata step.  The residual is `suslinMonic_ConstLeadStatement`,
the target restricted to ideals `J` that already contain an element whose leading coefficient
in `X` is a nonzero CONSTANT `C a`, `a ∈ ℤ[1/m]`.

**Reduction** (`suslinMonic_monic_of_constLead`).  `J ≠ 0` (else `J ⊆ (X)`, `X` prime); pick
`f ∈ J`, `f ≠ 0`; Nagata over the domain `ℤ[1/m]` (`suslinMonic_nagata`) gives `ψ` with
`lc(ψ f) = C a`, `a ≠ 0`.  The ideal `ψ(J) = ψ⁻¹*(J)` still lies in no principal prime (pull
a prime `π` back to the prime `ψ⁻¹ π`), so the residual gives `φ` and `q ∈ ψ(J)` with `φ q`
monic; then `ψ⁻¹ q ∈ J` and `(ψ ≫ φ)(ψ⁻¹ q) = φ q`.

**Truth check** (scratch `bh-met-91n/lexlc.py`, `run.py`).  The target is TRUE: it is the
`dim R = 1` case of Suslin's monic polynomial theorem, since `J` in no principal prime of the
UFD `ℤ[1/m][s,X]` means `ht J ≥ 2 > dim ℤ[1/m]`.  Checked the suggested test ideals
`(p, s)`, `(p, X)`, `(s, X)` in `ℤ[s][X]` and ~20 more (`(p², 1+pX)`, `(s, pX-1)`,
`(1+ps, 1+pX)`, `(ps-1, p²X-1)`, …, and ~250 random coprime pairs), for `m = 1, 2, 6`,
`k = 0, 1`: in EVERY case the lex leading-coefficient ideal (both variable orders) is the
unit ideal, i.e. a single Nagata change `s ↦ s + X^N` (`N ≫ 0`) already produces an element
of `J` with unit leading coefficient.  The principal control `(1+pX)` gives `(p)`, as it must.

**Why the residual is strictly weaker, and true.**  It is the target with one extra
hypothesis (a constant-leading-coefficient member), so the target implies it trivially, and it
is true because the target is.  It is strictly smaller in proof content: the Nagata change of
variables over `ℤ[1/m]` (weights `up^i`, distinct `X`-degrees of monomials) is proved here.
What remains is the prime-killing step: for the finitely many primes `p ∤ m` dividing `a`, find
one automorphism making some member of `J` have leading coefficient coprime to each `p`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual Statement**: the monic Statement for ideals that already contain a member
whose leading coefficient in `X` is a nonzero constant. -/
def suslinMonic_ConstLeadStatement : Prop :=
  ∀ (m k : ℕ), m ≠ 0 → ∀ J : Ideal (Polynomial (Chain.SIntPoly m k)),
    (∀ π : Polynomial (Chain.SIntPoly m k), Prime π → ¬J ≤ Ideal.span {π}) →
    (∃ f ∈ J, ∃ a : Localization.Away (m : ℤ), a ≠ 0 ∧
      f.leadingCoeff = MvPolynomial.C a) →
      ∃ φ : Polynomial (Chain.SIntPoly m k) ≃+* Polynomial (Chain.SIntPoly m k),
        ∃ q ∈ J, (φ q).Monic

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_ConstLeadStatement

/-- The target implies the residual (it only adds a hypothesis). -/
theorem suslinMonic_constLead_of_monic (h : suslinR1Prime_MonicStatement) :
    suslinMonic_ConstLeadStatement :=
  fun m k hm J hJ _ ↦ h m k hm J hJ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_constLead_of_monic

/-- Transport along a ring automorphism: if `J` lies in no principal prime, neither does its
image `ψ(J) = (ψ⁻¹)⁻¹(J)`. -/
theorem suslinMonic_comap_symm_avoid {B : Type*} [CommRing B] (ψ : B ≃+* B) {J : Ideal B}
    (hJ : ∀ π : B, Prime π → ¬J ≤ Ideal.span {π}) :
    ∀ π : B, Prime π → ¬J.comap ψ.symm ≤ Ideal.span {π} := by
  intro π hπ hle
  have hπ' : Prime (ψ.symm π) := (MulEquiv.prime_iff ψ.symm).2 hπ
  refine hJ (ψ.symm π) hπ' fun x hx ↦ ?_
  have hψx : ψ x ∈ J.comap ψ.symm := by
    rw [Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact hx
  have hd : π ∣ ψ x := Ideal.mem_span_singleton.1 (hle hψx)
  have hd' := map_dvd ψ.symm hd
  rw [RingEquiv.symm_apply_apply] at hd'
  exact Ideal.mem_span_singleton.2 hd'

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_comap_symm_avoid

/-- **The reduction**: the residual gives the monic Statement (Nagata step proved). -/
theorem suslinMonic_monic_of_constLead (h : suslinMonic_ConstLeadStatement) :
    suslinR1Prime_MonicStatement := by
  intro m k hm J hJ
  haveI : IsDomain (Localization.Away (m : ℤ)) := CharZeroHost.isDomain_away hm
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hJ Polynomial.X Polynomial.prime_X bot_le
  obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
  obtain ⟨ψ, a, ha, hlc⟩ := suslinMonic_nagata f hf0
  have hψf : ψ f ∈ J.comap ψ.symm := by
    rw [Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact hfJ
  obtain ⟨φ, q, hq, hqm⟩ :=
    h m k hm (J.comap ψ.symm) (suslinMonic_comap_symm_avoid ψ hJ) ⟨ψ f, hψf, a, ha, hlc⟩
  refine ⟨ψ.trans φ, ψ.symm q, hq, ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact hqm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_monic_of_constLead

/-- The residual gives the `ℤ` coordinate Statement `SuslinR1FinIntCoordStatement`. -/
theorem suslinMonic_intCoord_of_constLead (h : suslinMonic_ConstLeadStatement) :
    SuslinR1FinIntCoordStatement :=
  suslinR1Prime_intCoord_of_monic (suslinMonic_monic_of_constLead h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_intCoord_of_constLead

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
