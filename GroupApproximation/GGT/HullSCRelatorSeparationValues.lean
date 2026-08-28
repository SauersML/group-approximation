import GroupApproximation.GGT.HullSCRelatorWord

/-!
# What the symmetrized closure of a relator names

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii.

`HullSC.RelatorSeparation` is a statement about the *values* of the members of
`RelWord.Sym v` and of their prefixes, so before anything geometric is said the
values themselves should be pinned down.  They are:

> every member of `Sym v` names a conjugate of what `v` names, or a conjugate of
> its inverse.

That is `RelWord.Sym.exists_conj`, and it rests on two facts already in the
repository: a cyclic permutation names the conjugate of what the word names by
the prefix it moves (`RelWord.listVal_rotate`), and the formal inverse names the
inverse (`RelWord.listVal_revInv`).  `RelWord.Sym.exists_rotate` identifies the
members as lists; this identifies what they name.

Two consequences are recorded.

* `RelWord.Sym.listVal_eq_one` -- if the relator names the identity then so does
  every member of its symmetrized closure, the conjugacy class of `1` being
  `{1}`.
* `RelWord.longMatch_of_listVal_eq_one` -- for such a relator the separation
  clause of `HullSC.RelatorSeparation` holds outright, at every constant `B`,
  every `eps` and every pair `y, z`.  So the clause is not self-contradictory:
  it has models, and any refutation of it has to use a relator naming something
  other than the identity.  Hull's relator names `t⁻¹ h^{Σ mᵢ}`
  (`HullSC.listVal_relatorWord`), so this case is the one where `t` is the
  corresponding power of `h`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u w

namespace RelWord

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The value of a cyclic permutation, with no bound on the index -/

/-- **A cyclic permutation names a conjugate**, for every index.

`listVal_rotate` needs `n ≤ |w|`; reducing the index modulo the length removes
that hypothesis, which is what an induction over `Sym` needs, since the
constructor `Sym.rot` carries an unrestricted natural number. -/
theorem exists_conj_listVal_rotate (w : List (GGT.RelLetter G Λ)) (n : ℕ) :
    ∃ c : G, GGT.RelLetter.listVal (w.rotate n)
      = c⁻¹ * GGT.RelLetter.listVal w * c := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · have hw : w = [] := List.length_eq_zero_iff.mp h0
    subst hw
    refine ⟨1, ?_⟩
    rw [List.rotate_nil, inv_one, one_mul, mul_one]
  · refine ⟨GGT.RelLetter.listVal (w.take (n % w.length)), ?_⟩
    have hle : n % w.length ≤ w.length := le_of_lt (Nat.mod_lt _ hpos)
    have hrot : w.rotate n = w.rotate (n % w.length) := (List.rotate_mod w n).symm
    rw [hrot]
    exact listVal_rotate w hle

/-! ## The values of the symmetrized closure -/

/-- **Every member of the symmetrized closure names a conjugate of what the
relator names, or a conjugate of its inverse.**

`RelWord.Sym.exists_rotate` identifies the members as lists -- the rotations of
`v` and the rotations of `revInv v` -- so there are two cases and each is one
application of `exists_conj_listVal_rotate`, the second composed with
`listVal_revInv`.  No induction over `Sym` is needed. -/
theorem Sym.exists_conj {v w : List (GGT.RelLetter G Λ)} (h : Sym v w) :
    ∃ c : G, GGT.RelLetter.listVal w = c⁻¹ * GGT.RelLetter.listVal v * c ∨
      GGT.RelLetter.listVal w = c⁻¹ * (GGT.RelLetter.listVal v)⁻¹ * c := by
  rcases h.exists_rotate with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · obtain ⟨d, hd⟩ := exists_conj_listVal_rotate v n
    exact ⟨d, Or.inl hd⟩
  · obtain ⟨d, hd⟩ := exists_conj_listVal_rotate (revInv v) n
    refine ⟨d, Or.inr ?_⟩
    rw [hd, listVal_revInv]

/-- **A relator naming the identity has a symmetrized closure of words naming
the identity.**  The conjugacy class of `1` is `{1}`. -/
theorem Sym.listVal_eq_one {v w : List (GGT.RelLetter G Λ)}
    (hv : GGT.RelLetter.listVal v = 1) (h : Sym v w) :
    GGT.RelLetter.listVal w = 1 := by
  obtain ⟨c, hc | hc⟩ := h.exists_conj
  · rw [hc, hv, mul_one, inv_mul_cancel]
  · rw [hc, hv, inv_one, mul_one, inv_mul_cancel]

/-! ## The separation clause has models -/

/-- **Olshanskii's separation holds outright for a relator naming the
identity.**

Every member of the symmetrized closure then names `1`
(`Sym.listVal_eq_one`), and `1 = y · 1 · y⁻¹`, so the conclusion is met with no
hypothesis on the match at all: no constant, no bound on the prefix, no bound on
the conjugators.

This is the statement that keeps the separation clause of
`HullSC.RelatorSeparation` from being read as vacuous or as
self-contradictory.  Hull's relator names `t⁻¹ h^{Σ mᵢ}`, so the case covered
here is the one in which the target `t` is that power of `h`; the content of §6
is the remaining case, and it is a statement about matches. -/
theorem longMatch_of_listVal_eq_one {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} (hv : GGT.RelLetter.listVal v = 1)
    (eps B : ℕ) :
    ∀ w w' u u' : List (GGT.RelLetter G Λ), Sym v w → Sym v w' →
      (∃ s, w = u ++ s) → (∃ s', w' = u' ++ s') → B < u.length →
        ∀ y z : G, wordNorm D.base y ≤ eps → wordNorm D.base z ≤ eps →
          GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z →
            GGT.RelLetter.listVal w'
              = y * GGT.RelLetter.listVal w * y⁻¹ := by
  intro w w' _u _u' hw hw' _ _ _ y _z _ _ _
  rw [Sym.listVal_eq_one hv hw, Sym.listVal_eq_one hv hw', mul_one,
    mul_inv_cancel]

end RelWord

end HullSC
end GroupApproximation
