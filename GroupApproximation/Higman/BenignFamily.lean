import GroupApproximation.Higman.BenignJoin

/-!
# Finite families of benign subgroups, and conjugation

With Higman's Lemma 3.2 proved in both halves --- intersections in
`Higman.Benign` and joins in `Higman.BenignJoin` --- the statements for finite
families follow by induction, and conjugation follows from transport along an
inner automorphism.  This file is those consequences, so that the later
sections of Higman's argument, which combine benign subgroups many at a time,
can use them without repeating the induction.

Nothing here is conditional.
-/

namespace GroupApproximation
namespace Higman

variable {G : Type} [Group G]

/-! ## 1.  Finite joins -/

/-- Benign subgroups are closed under the join of a nonempty finite family. -/
theorem Benign.iSup_fin [Group.FG G] {r : ℕ} (A : Fin (r + 1) → Subgroup G)
    (hA : ∀ i, Benign (A i)) : Benign (⨆ i, A i) := by
  induction r with
  | zero =>
      have hsingle : (⨆ i : Fin 1, A i) = A 0 := by
        refine le_antisymm ?_ ?_
        · refine iSup_le fun i => ?_
          have : i = 0 := Subsingleton.elim i 0
          rw [this]
        · exact le_iSup _ 0
      rw [hsingle]
      exact hA 0
  | succ n ih =>
      have hsplit : (⨆ i : Fin (n + 2), A i) = A 0 ⊔ ⨆ i : Fin (n + 1), A i.succ := by
        refine le_antisymm ?_ ?_
        · refine iSup_le fun i => ?_
          refine Fin.cases ?_ ?_ i
          · exact le_sup_left
          · intro j
            exact le_trans (le_iSup (fun k : Fin (n + 1) => A k.succ) j) le_sup_right
        · refine sup_le (le_iSup _ 0) (iSup_le fun j => le_iSup _ j.succ)
      rw [hsplit]
      exact Benign.sup (hA 0) (ih (fun i => A i.succ) (fun i => hA i.succ))

/-! ## 2.  Conjugation -/

/-- The inner automorphism of `G` at `g`. -/
def innerAut (g : G) : G ≃* G := MulAut.conj g

/-- **A conjugate of a benign subgroup is benign.**  Transport along the inner
automorphism; no construction is involved. -/
theorem Benign.comap_innerAut {H : Subgroup G} (g : G) (h : Benign H) :
    Benign (H.comap (innerAut g).toMonoidHom) :=
  Benign.congr (innerAut g) h

/-! ## 3.  What Higman's Section 3.1 now amounts to

For a group with a finitely presented overgroup, the benign subgroups form a
family closed under

* finite intersections --- `Benign.inf`, `Benign.iInf_fin`;
* finite joins --- `Benign.sup`, `Benign.iSup_fin`;
* preimages along any homomorphism --- `Benign.comap`;
* transport along isomorphisms, in particular conjugation ---
  `Benign.congr`, `Benign.comap_innerAut`;

and containing every finitely generated subgroup (`benign_of_fg`) and every
kernel of a map to a finitely presented group (`benign_ker`).  That is
Higman's Lemma 3.2 and Lemma 3.3, and it is what his Section 4 consumes. -/

end Higman
end GroupApproximation
