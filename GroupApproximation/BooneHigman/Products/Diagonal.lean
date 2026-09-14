import GroupApproximation.BooneHigman.Products.ProductTree

/-!
# Zaremsky's `m`-fold representation of a self-similar group

In the proof of Theorem 1.1 of Zaremsky (arXiv:2405.09722), a self-similar group `G ≤ Aut(T_d)` is
re-embedded in `Aut(T_{md})` through the wreath recursion
`g ↦ σ^{⊕m}(g_1, …, g_d, g_1, …, g_d, …, g_1, …, g_d)`, where `σ^{⊕m}` acts like `σ` on each of the
`m` blocks of letters.  With the alphabet `m × X` this is the product action of `{1} × G`:
`diagonalHom m X g = prodAut 1 g`.  It is faithful, its root permutation acts blockwise
(`rootPerm_diagonalHom`), its states are the images of the states of `g` (`state_diagonalHom`), and
it carries self-similar groups to self-similar groups (`isSelfSimilar_map_diagonalHom`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Products

open Trees

variable {m X : Type*}

variable (m X) in
/-- Zaremsky's `m`-fold representation `Aut(T_X) →* Aut(T_{m × X})`: `g` acts on the second
coordinates of a word and fixes the block labels. -/
def diagonalHom : TreeAut X →* TreeAut (m × X) :=
  prodHom.comp (MonoidHom.inr (TreeAut m) (TreeAut X))

theorem diagonalHom_apply (g : TreeAut X) : diagonalHom m X g = prodAut 1 g := rfl

theorem diagonalHom_smul (g : TreeAut X) (w : List (m × X)) :
    diagonalHom m X g • w = List.zip (w.map Prod.fst) (g • w.map Prod.snd) := by
  show List.zip ((1 : TreeAut m) • w.map Prod.fst) (g • w.map Prod.snd) = _
  rw [one_smul]

theorem diagonalHom_injective [Nonempty m] [Nonempty X] :
    Function.Injective (diagonalHom m X) :=
  prodHom_injective.comp fun _ _ h => (Prod.ext_iff.1 h).2

/-- The first level of the `m`-fold representation acts like `rootPerm g` on every block. -/
theorem rootPerm_diagonalHom (g : TreeAut X) (k : m) (x : X) :
    TreeAut.rootPerm (diagonalHom m X g) (k, x) = (k, TreeAut.rootPerm g x) := by
  have h : diagonalHom m X g • [(k, x)] = [(k, TreeAut.rootFun g x)] := by
    rw [diagonalHom_smul]
    show List.zip [k] (g • [x]) = [(k, TreeAut.rootFun g x)]
    simp [TreeAut.smul_singleton]
  rw [TreeAut.smul_singleton] at h
  exact List.singleton_inj.1 h

/-- The states of the `m`-fold representation are the images of the states of `g`. -/
theorem state_diagonalHom (g : TreeAut X) (w : List (m × X)) :
    TreeAut.state (diagonalHom m X g) w = diagonalHom m X (TreeAut.state g (w.map Prod.snd)) := by
  show TreeAut.state (prodAut 1 g) w = prodAut 1 (TreeAut.state g (w.map Prod.snd))
  rw [state_prodAut, TreeAut.state_one]

/-- The `m`-fold representation of a self-similar group is self-similar. -/
theorem isSelfSimilar_map_diagonalHom {G : Subgroup (TreeAut X)} (hG : IsSelfSimilar G) :
    IsSelfSimilar (G.map (diagonalHom m X)) := by
  rintro _ ⟨g, hg, rfl⟩ ⟨k, x⟩
  exact ⟨TreeAut.state g [x], hG g hg x, (state_diagonalHom g [(k, x)]).symm⟩

/-- A subgroup is isomorphic to its `m`-fold representation. -/
noncomputable def mapDiagonalHomEquiv [Nonempty m] [Nonempty X] (G : Subgroup (TreeAut X)) :
    G ≃* G.map (diagonalHom m X) :=
  G.equivMapOfInjective (diagonalHom m X) diagonalHom_injective

end Products
end BooneHigman
end GroupApproximation
