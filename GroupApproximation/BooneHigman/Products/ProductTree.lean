import GroupApproximation.BooneHigman.Trees.TreeAut

/-!
# Products of self-similar groups on product alphabets

For alphabets `X` and `Y`, the group `Aut(T_X) × Aut(T_Y)` acts on the tree over the product
alphabet `X × Y` coordinatewise: a word over `X × Y` is a pair of words of the same length, and
`(g, h)` acts by `g` on the first coordinates and by `h` on the second.  The state of `(g, h)` at a
vertex `w` is the pair of states at the two coordinate words of `w`, so the image of a product of
self-similar groups is self-similar (Zaremsky, arXiv:2405.09722, Definition 2.1).  For nonempty
alphabets the action is faithful.

Zaremsky's proof of Theorem 1.1 assumes only that the group is a finitely presented self-similar
subgroup of `Aut(T_d)` with `d ≥ 2`.  The product of two such groups is therefore again an input
to the theorem, on the alphabet `X × Y`.  The special case `{1} × G` on `Fin m × X` is the `m`-fold
representation with wreath recursion `σ^{⊕m}(g_1, …, g_d, …, g_1, …, g_d)` used in his proof.

* `prodFun g h w`, the words of the product automorphism, and `prodFun_append`, its recursion.
* `prodAut g h : TreeAut (X × Y)` and the homomorphism `prodHom`, injective for nonempty alphabets
  (`prodHom_injective`).
* `state_prodAut`: `state (prodAut g h) w = prodAut (state g (w.map Prod.fst)) (state h (w.map Prod.snd))`.
* `isSelfSimilar_map_prodHom`: the image of `G.prod K` is self-similar when `G` and `K` are.
* `mapProdHomEquiv`: that image is isomorphic to `G × K`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Products

open Trees

variable {X Y : Type*}

/-- The words of the product automorphism: `g` acts on the first coordinates of a word over
`X × Y` and `h` on the second. -/
def prodFun (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) : List (X × Y) :=
  List.zip (g • w.map Prod.fst) (h • w.map Prod.snd)

theorem map_fst_prodFun (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) :
    (prodFun g h w).map Prod.fst = g • w.map Prod.fst :=
  List.map_fst_zip (by simp only [TreeAut.length_smul, List.length_map, le_refl])

theorem map_snd_prodFun (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) :
    (prodFun g h w).map Prod.snd = h • w.map Prod.snd :=
  List.map_snd_zip (by simp only [TreeAut.length_smul, List.length_map, le_refl])

theorem prodFun_prodFun (g g' : TreeAut X) (h h' : TreeAut Y) (w : List (X × Y)) :
    prodFun g h (prodFun g' h' w) = prodFun (g * g') (h * h') w := by
  show List.zip (g • (prodFun g' h' w).map Prod.fst) (h • (prodFun g' h' w).map Prod.snd) = _
  rw [map_fst_prodFun, map_snd_prodFun, prodFun, mul_smul, mul_smul]

theorem prodFun_one (w : List (X × Y)) : prodFun (1 : TreeAut X) (1 : TreeAut Y) w = w := by
  rw [prodFun, one_smul, one_smul, ← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]

theorem length_prodFun (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) :
    (prodFun g h w).length = w.length := by
  simp only [prodFun, List.length_zip, TreeAut.length_smul, List.length_map, min_self]

/-- The recursion of the product automorphism: after a vertex `w`, the pair of states acts. -/
theorem prodFun_append (g : TreeAut X) (h : TreeAut Y) (w v : List (X × Y)) :
    prodFun g h (w ++ v) =
      prodFun g h w ++ prodFun (TreeAut.state g (w.map Prod.fst)) (TreeAut.state h (w.map Prod.snd)) v := by
  simp only [prodFun, List.map_append, TreeAut.smul_append]
  exact List.zip_append (by simp only [TreeAut.length_smul, List.length_map])

theorem isTreeMap_prodFun (g : TreeAut X) (h : TreeAut Y) : IsTreeMap (prodFun g h) :=
  ⟨length_prodFun g h, fun w v => by rw [prodFun_append]; exact List.prefix_append _ _⟩

/-- The product automorphism as a permutation of words over `X × Y`. -/
def prodPerm (g : TreeAut X) (h : TreeAut Y) : Equiv.Perm (List (X × Y)) where
  toFun := prodFun g h
  invFun := prodFun g⁻¹ h⁻¹
  left_inv w := by
    show prodFun g⁻¹ h⁻¹ (prodFun g h w) = w
    rw [prodFun_prodFun, inv_mul_cancel, inv_mul_cancel, prodFun_one]
  right_inv w := by
    show prodFun g h (prodFun g⁻¹ h⁻¹ w) = w
    rw [prodFun_prodFun, mul_inv_cancel, mul_inv_cancel, prodFun_one]

/-- The automorphism of the tree over `X × Y` acting by `g` and `h` coordinatewise. -/
def prodAut (g : TreeAut X) (h : TreeAut Y) : TreeAut (X × Y) :=
  ⟨prodPerm g h, isTreeMap_prodFun g h⟩

theorem prodAut_smul (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) :
    prodAut g h • w = prodFun g h w := rfl

/-- The coordinatewise action `Aut(T_X) × Aut(T_Y) →* Aut(T_{X × Y})`. -/
def prodHom : TreeAut X × TreeAut Y →* TreeAut (X × Y) where
  toFun p := prodAut p.1 p.2
  map_one' := TreeAut.ext fun w => by
    rw [one_smul]
    exact prodFun_one w
  map_mul' p q := TreeAut.ext fun w => by
    rw [mul_smul]
    exact (prodFun_prodFun p.1 q.1 p.2 q.2 w).symm

theorem prodHom_apply (p : TreeAut X × TreeAut Y) : prodHom p = prodAut p.1 p.2 := rfl

/-- For nonempty alphabets the coordinatewise action is faithful. -/
theorem prodHom_injective [Nonempty X] [Nonempty Y] :
    Function.Injective (prodHom : TreeAut X × TreeAut Y →* TreeAut (X × Y)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, h⟩ hgh
  have key : ∀ w : List (X × Y), prodFun g h w = w := fun w => by
    have hw := congrArg (fun k : TreeAut (X × Y) => k • w) hgh
    simp only [one_smul] at hw
    exact hw
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨y0⟩ := ‹Nonempty Y›
  refine Prod.ext (TreeAut.ext fun u => ?_) (TreeAut.ext fun v => ?_)
  · have e := congrArg (List.map Prod.fst) (key (List.zip u (List.replicate u.length y0)))
    rw [map_fst_prodFun,
      List.map_fst_zip (l₁ := u) (l₂ := List.replicate u.length y0) (by simp)] at e
    show g • u = (1 : TreeAut X) • u
    rw [one_smul]
    exact e
  · have e := congrArg (List.map Prod.snd) (key (List.zip (List.replicate v.length x0) v))
    rw [map_snd_prodFun,
      List.map_snd_zip (l₁ := List.replicate v.length x0) (l₂ := v) (by simp)] at e
    show h • v = (1 : TreeAut Y) • v
    rw [one_smul]
    exact e

/-- The state of a product automorphism is the product of the coordinate states. -/
theorem state_prodAut (g : TreeAut X) (h : TreeAut Y) (w : List (X × Y)) :
    TreeAut.state (prodAut g h) w =
      prodAut (TreeAut.state g (w.map Prod.fst)) (TreeAut.state h (w.map Prod.snd)) :=
  TreeAut.ext fun v =>
    TreeAut.state_smul_eq_of_smul_append (prodAut g h) (w := w) (x := v)
      (y := prodFun (TreeAut.state g (w.map Prod.fst)) (TreeAut.state h (w.map Prod.snd)) v)
      (prodFun_append g h w v)

/-- **Products of self-similar groups are self-similar** on the product alphabet. -/
theorem isSelfSimilar_map_prodHom {G : Subgroup (TreeAut X)} {K : Subgroup (TreeAut Y)}
    (hG : IsSelfSimilar G) (hK : IsSelfSimilar K) : IsSelfSimilar ((G.prod K).map prodHom) := by
  rintro _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩ ⟨x, y⟩
  exact ⟨(TreeAut.state g [x], TreeAut.state h [y]), ⟨hG g hg x, hK h hh y⟩,
    (state_prodAut g h [(x, y)]).symm⟩

/-- The image of `G.prod K` under the coordinatewise action is isomorphic to `G × K`. -/
noncomputable def mapProdHomEquiv [Nonempty X] [Nonempty Y] (G : Subgroup (TreeAut X))
    (K : Subgroup (TreeAut Y)) : G × K ≃* (G.prod K).map prodHom :=
  (G.prodEquiv K).symm.trans ((G.prod K).equivMapOfInjective prodHom prodHom_injective)

end Products
end BooneHigman
end GroupApproximation
