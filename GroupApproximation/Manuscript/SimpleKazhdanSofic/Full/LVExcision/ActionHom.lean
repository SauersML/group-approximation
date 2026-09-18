import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVExcision.ActionRel

/-!
# The action of `St_N(R)` on the relative Steinberg subgroup (lane LVExcision)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Stable `K₂`
excision (Suslin–Wodzicki, Ann. Math. 136 (1992), Thm A; Keune, J. Algebra 54 (1978); ABC
thm:skewyao, `yaoseq6.tex` l.558-640).

The automorphisms `actAut … k l hkl r` of `rel I A N` satisfy the Steinberg relations
(`act_add`, `act_comm`, `act_adj`), so they define a homomorphism
`actHom : St_N(R) →* MulAut (rel I A N)` with `actHom (x_{kl}(r)) = actAut … k l hkl r`.
-/

namespace GroupApproximation.Full.LVExcision

noncomputable section

open SteinbergGroup
open scoped commutatorElement

variable {R : Type*} [Ring R] {I : TwoSidedIdeal R} {A : Subring R} {N : ℕ}

/-- `(actAut … r).symm y` is `act … (-r) y`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actAut_symm_apply (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) (y : rel I A N) :
    (actAut hN hI hIA k l hkl r).symm y = act hI hIA k l hkl (-r) y :=
  rfl

/-- The automorphism attached to a Steinberg generator.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def actGen (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A)
    (g : SteinbergGenerator (Fin N) R) : MulAut (rel I A N) :=
  actAut hN hI hIA g.row g.column g.row_ne_column g.coefficient

/-- The generator automorphisms kill the Steinberg relators.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actGen_relation (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A)
    (w : FreeGroup (SteinbergGenerator (Fin N) R))
    (hw : w ∈ relations (I := Fin N) (R := R)) :
    FreeGroup.lift (actGen hN hI hIA) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, actGen]
      change actAut hN hI hIA i j hij a * actAut hN hI hIA i j hij b *
        (actAut hN hI hIA i j hij (a + b))⁻¹ = 1
      rw [mul_inv_eq_one]
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.mul_apply, actAut_apply]
      exact act_add hN hI hIA i j hij a b y
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, actGen]
      change ⁅actAut hN hI hIA i j hij a, actAut hN hI hIA k l hkl b⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.mul_apply, actAut_apply]
      exact act_comm hN hI hIA i j k l hij hkl hjk hli a b y
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of, actGen]
      change ⁅actAut hN hI hIA i j hij a, actAut hN hI hIA j k hjk b⁆ *
        (actAut hN hI hIA i k hik (a * b))⁻¹ = 1
      rw [mul_inv_eq_one, commutatorElement_def]
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.mul_apply, MulAut.inv_apply, actAut_symm_apply, actAut_apply]
      exact act_adj hN hI hIA i j k hij hjk hik a b y

/-- The action `St_N(R) →* MulAut (rel I A N)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
def actHom (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) :
    SteinbergGroup (Fin N) R →* MulAut (rel I A N) :=
  PresentedGroup.toGroup (f := actGen hN hI hIA) (actGen_relation hN hI hIA)

/-- `actHom` on generators.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actHom_x (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) : actHom hN hI hIA (x k l hkl r) = actAut hN hI hIA k l hkl r := by
  exact PresentedGroup.toGroup.of _

/-- `actHom (x_{kl}(r))` acts on `y` by `act … r y`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii; Suslin–Wodzicki 1992, Thm A.) -/
theorem actHom_x_apply (hN : 3 ≤ N) (hI : IsSUnital I) (hIA : ∀ a ∈ I, a ∈ A) (k l : Fin N)
    (hkl : k ≠ l) (r : R) (y : rel I A N) :
    actHom hN hI hIA (x k l hkl r) y = act hI hIA k l hkl r y := by
  rw [actHom_x, actAut_apply]

end

end GroupApproximation.Full.LVExcision
