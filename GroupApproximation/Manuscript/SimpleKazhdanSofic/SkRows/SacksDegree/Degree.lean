import Mathlib.Computability.TuringDegree
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Fintype.EquivFin
import GroupApproximation.Meta.AxiomGuard

/-!
# Mathlib's poset of Turing degrees: the degree of an oracle

`simple_kazhdan_sofic_group.tex`, proof of `cor:wp`, tex l.719–721:

> By a construction of Sacks, the Turing degrees contain an antichain of size
> continuum~\cite[Chapter~V]{Odifreddi}, and the groups $G_{X_\alpha}$ with $\alpha$ of these
> degrees are as claimed.

The corpus states the Sacks antichain over oracles `ℕ →. ℕ` and Mathlib's `TuringReducible`
(`OracleUse.exists_turing_antichain_continuum`, `printedTuringAntichainContinuum`). This module
supplies the bridge to Mathlib's partial order `TuringDegree` (`Computability/TuringDegree.lean`),
which is the antisymmetrization of `TuringReducible`, so that the antichain can be stated as a set of
degrees, as in Odifreddi, Chapter V.

* `turingDegreeOf f`: the degree of the oracle `f`;
* `turingDegreeOf_le_iff`, `turingDegreeOf_eq_iff`: the order and the equality of degrees are
  Turing reducibility and Turing equivalence;
* `turingDegreeOf_surjective`: every degree is the degree of an oracle;
* `mk_pfun_nat`, `mk_turingDegree_le`: there are at most continuum many degrees.

The corpus `TuringReducible` is Mathlib's (the corpus has no definition of its own under that name),
so the bridge is definitional.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SacksDegree

/-- The Turing degree of an oracle, in Mathlib's `TuringDegree`. -/
def turingDegreeOf (f : ℕ →. ℕ) : TuringDegree :=
  toAntisymmetrization TuringReducible f

/-- The order of Turing degrees is Turing reducibility of representatives. -/
theorem turingDegreeOf_le_iff (f g : ℕ →. ℕ) :
    turingDegreeOf f ≤ turingDegreeOf g ↔ TuringReducible f g :=
  Iff.rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.turingDegreeOf_le_iff

/-- Two oracles have the same degree exactly when they are Turing equivalent. -/
theorem turingDegreeOf_eq_iff (f g : ℕ →. ℕ) :
    turingDegreeOf f = turingDegreeOf g ↔ TuringEquivalent f g :=
  ⟨fun h => ⟨(turingDegreeOf_le_iff f g).1 h.le, (turingDegreeOf_le_iff g f).1 h.ge⟩,
    fun h => le_antisymm ((turingDegreeOf_le_iff f g).2 h.1) ((turingDegreeOf_le_iff g f).2 h.2)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.turingDegreeOf_eq_iff

/-- Every Turing degree is the degree of some oracle. -/
theorem turingDegreeOf_surjective : Function.Surjective turingDegreeOf :=
  fun d => ⟨ofAntisymmetrization TuringReducible d,
    toAntisymmetrization_ofAntisymmetrization TuringReducible d⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.turingDegreeOf_surjective

/-- There are continuum many oracles `ℕ →. ℕ`: `Part ℕ` is classically `Option ℕ`, which is
countably infinite, and `ℵ₀ ^ ℵ₀ = 𝔠`. -/
theorem mk_pfun_nat : Cardinal.mk (ℕ →. ℕ) = Cardinal.continuum := by
  have e : (ℕ →. ℕ) ≃ (ℕ → Option ℕ) :=
    Equiv.piCongrRight (fun _ : ℕ => (Part.equivOption : Part ℕ ≃ Option ℕ))
  rw [Cardinal.mk_congr e, ← Cardinal.power_def, Cardinal.mk_eq_aleph0 (Option ℕ),
    Cardinal.mk_nat, Cardinal.aleph0_power_aleph0]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.mk_pfun_nat

/-- There are at most continuum many Turing degrees. -/
theorem mk_turingDegree_le : Cardinal.mk TuringDegree ≤ Cardinal.continuum := by
  rw [← mk_pfun_nat]
  exact Cardinal.mk_le_of_surjective turingDegreeOf_surjective

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.mk_turingDegree_le

end SacksDegree
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
