import GroupApproximation.CharClass.OddPGroupRing

/-!
# The group ring has characteristic `p`, and `(T − 1)^p = 0`

Separated from `OddPGroupRing.lean` on purpose.  The periodic resolution needs
only the telescoping identity `grNorm_mul_grS`, so nothing that builds the
resolution, the source functor or the tuple complex should be able to be blocked
by the characteristic argument, which is the one step in this corner of the
development that depends on how Mathlib currently presents `MonoidAlgebra`.

At the pin `81a5d257` a `MonoidAlgebra` is a **structure** wrapping its
coefficient `Finsupp`, not the `Finsupp` itself, so the injectivity of the
constants `r ↦ single 1 r` is `MonoidAlgebra.single_right_injective` and **not**
`Finsupp.single_injective`; the latter typechecks nowhere here and was the one
error in this file's first probe.

`grS_pow_card` is used where the norm has to be recognised as a multiple of
`grS` — every `N e_j` is a boundary in `W`, which is what makes the reduced
powers additive.
-/

namespace GroupApproximation.CharClass

/-- The group ring has characteristic `p`: the coefficient ring embeds in it as
the constants, by `single 1`, and that map is injective. -/
instance charP_groupRingZMod (p : ℕ) : CharP (GroupRingZMod p) p := by
  have hinj : Function.Injective
      (MonoidAlgebra.singleOneRingHom : ZMod p →+* GroupRingZMod p) := by
    intro a b h
    have h' : MonoidAlgebra.single (1 : Multiplicative (ZMod p)) a
        = MonoidAlgebra.single (1 : Multiplicative (ZMod p)) b := h
    exact MonoidAlgebra.single_right_injective h'
  exact charP_of_injective_ringHom hinj p

/-- **Frobenius**: `(T − 1)^p = T^p − 1 = 0`. -/
theorem grS_pow_card (p : ℕ) [Fact p.Prime] : grS p ^ p = 0 := by
  unfold grS
  rw [sub_pow_char, one_pow, grGen_pow_card, sub_self]

end GroupApproximation.CharClass
