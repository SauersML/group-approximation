import Mathlib.Data.Matrix.Basis
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.Relations

/-!
# The linear action of `St_N(𝔽₂)` on `𝔽₂^N`

`St_N(𝔽₂)` acts on column vectors through the canonical projection to `E_N(𝔽₂)`; this is the
action used in the Schreier coset argument for Steinberg's theorem `K₂(𝔽₂) = 0`
(Steinberg 1962; Milnor, *Introduction to algebraic K-theory*, §9-10), towards
`simple_kazhdan_sofic_group.tex` l.733-735 (leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup
open scoped Matrix

variable {N : ℕ}

/-- The matrix of an element of `St_N(𝔽₂)`. -/
noncomputable def M : St N →* Matrix (Fin N) (Fin N) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin N) (Fin N) (ZMod 2))).comp
    ((elementaryGroup (Fin N) (ZMod 2)).subtype.comp (projection (I := Fin N) (R := ZMod 2)))

/-- The action of `St_N(𝔽₂)` on column vectors. -/
noncomputable def act (g : St N) (v : Fin N → ZMod 2) : Fin N → ZMod 2 := M g *ᵥ v

theorem M_X (i j : Fin N) (h : i ≠ j) : M (X i j h) = 1 + Matrix.single i j (1 : ZMod 2) := by
  have hp : projection (X i j h) = elementaryRoot i j h (1 : ZMod 2) :=
    projection_x (R := ZMod 2) i j h 1
  calc M (X i j h)
      = (((projection (X i j h) : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)) :
          Matrix (Fin N) (Fin N) (ZMod 2)) := rfl
    _ = (((elementaryRoot i j h (1 : ZMod 2) : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)) :
          Matrix (Fin N) (Fin N) (ZMod 2)) := by rw [hp]
    _ = 1 + Matrix.single i j (1 : ZMod 2) := rfl

theorem M_eq_one_of_projection {g : St N} (hg : projection g = 1) : M g = 1 := by
  calc M g = ((Units.coeHom (Matrix (Fin N) (Fin N) (ZMod 2))).comp
        (elementaryGroup (Fin N) (ZMod 2)).subtype) (projection g) := rfl
    _ = 1 := by rw [hg, map_one]

theorem act_mul (g h : St N) (v : Fin N → ZMod 2) : act (g * h) v = act g (act h v) := by
  simp only [act, map_mul, Matrix.mulVec_mulVec]

theorem act_one (v : Fin N → ZMod 2) : act (1 : St N) v = v := by
  simp only [act, map_one, Matrix.one_mulVec]

theorem act_eq_self_of_projection {g : St N} (hg : projection g = 1) (v : Fin N → ZMod 2) :
    act g v = v := by
  rw [act, M_eq_one_of_projection hg, Matrix.one_mulVec]

theorem act_inv_act (g : St N) (v : Fin N → ZMod 2) : act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_X_apply (i j : Fin N) (h : i ≠ j) (v : Fin N → ZMod 2) (k : Fin N) :
    act (X i j h) v k = v k + if k = i then v j else 0 := by
  rw [act, M_X, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul]
  exact congrArg (fun t => v k + t) (Function.update_apply (0 : Fin N → ZMod 2) i (v j) k)

theorem act_X_apply_of_ne (i j : Fin N) (h : i ≠ j) (v : Fin N → ZMod 2) {k : Fin N}
    (hk : k ≠ i) : act (X i j h) v k = v k := by
  rw [act_X_apply, if_neg hk, add_zero]

theorem act_X_apply_self (i j : Fin N) (h : i ≠ j) (v : Fin N → ZMod 2) :
    act (X i j h) v i = v i + v j := by
  rw [act_X_apply, if_pos rfl]

/-- The Weyl element `w_{ab}` permutes coordinates by the transposition `(a b)`. -/
theorem act_w_apply (a b : Fin N) (hab : a ≠ b) (u : Fin N → ZMod 2) (k : Fin N) :
    act (w a b hab) u k = u (Equiv.swap a b k) := by
  have key : ∀ s t : ZMod 2, s + t + s = t := by decide
  have key2 : ∀ s t : ZMod 2, t + (s + t) = s := by decide
  have h1a : act (X a b hab) u a = u a + u b := act_X_apply_self a b hab u
  have h1b : act (X a b hab) u b = u b := act_X_apply_of_ne a b hab u hab.symm
  have h2a : act (X b a hab.symm) (act (X a b hab) u) a = u a + u b := by
    rw [act_X_apply_of_ne b a hab.symm _ hab, h1a]
  have h2b : act (X b a hab.symm) (act (X a b hab) u) b = u a := by
    rw [act_X_apply_self, h1a, h1b, key2]
  have h2k : ∀ l, l ≠ a → l ≠ b → act (X b a hab.symm) (act (X a b hab) u) l = u l :=
    fun l hla hlb => by
      rw [act_X_apply_of_ne b a hab.symm _ hlb, act_X_apply_of_ne a b hab u hla]
  rw [w, act_mul, act_mul, act_X_apply]
  by_cases hka : k = a
  · rw [if_pos hka, hka, h2a, h2b, Equiv.swap_apply_left, key]
  · rw [if_neg hka, add_zero]
    by_cases hkb : k = b
    · rw [hkb, h2b, Equiv.swap_apply_right]
    · rw [h2k k hka hkb, Equiv.swap_apply_of_ne_of_ne hka hkb]

/-- The standard basis vector `e_q`. -/
noncomputable def e (q : Fin N) : Fin N → ZMod 2 := Pi.single q 1

theorem e_self (q : Fin N) : e q q = 1 := Pi.single_eq_same q (1 : ZMod 2)

theorem e_ne {q k : Fin N} (h : k ≠ q) : e q k = 0 := Pi.single_eq_of_ne h (1 : ZMod 2)

end GroupApproximation.Full.LVFieldK2
