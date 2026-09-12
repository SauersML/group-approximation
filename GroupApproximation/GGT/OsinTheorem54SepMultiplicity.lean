/-
Copyright (c) 2026 the GroupApproximation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.GGT.HullSCRelatorSeparation2Cross

/-!
# Osin's Theorem 5.4: the multiplicity hypothesis is a theorem

The assembly `GGT/OsinTheorem54SepAssembleFull.lean` carries a binder `hmult`:
an element lying in two distinct members of the family is `d̂`-close to the
identity in one of them.  That is not a constraint on the choice of the
family after all: `HullSC.mem_relBall_one_of_mem_fam_ne` puts such an element
in the radius-one ball of either index — its one-letter spelling at the OTHER
index traverses no edge of the first index's coset graph — and the ball grows
with the radius.  So the binder is discharged at every radius `1 ≤ Dc`, on
the left disjunct uniformly.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The multiplicity hypothesis of the full assembly, discharged.**  An
element of two distinct members of the family lies in the radius-`Dc` ball
of the first, for every `1 ≤ Dc`. -/
theorem mult_of_relBall_one (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc) :
    ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc :=
  fun lam _ hne _ hxlam hxmu =>
    Or.inl (relBall_mono_radius D lam hDc
      (HullSC.mem_relBall_one_of_mem_fam_ne (Ne.symm hne) hxmu hxlam))

end OsinComponents
end GGT
end GroupApproximation
