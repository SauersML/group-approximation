import GroupApproximation.GGT.VanKampen.DiscDiagram

/-!
# Reducedness of a subdiagram cut out of a reduced diagram

Osin's Lemma 6.5 cuts the subdiagram enclosed by a four-arc closed walk out of a
reduced diagram and needs the piece to be reduced again.  Reducedness compares
one relator cell with a later one across the product of the cells between them,
so it does not pass to an arbitrary sublist of the ordered cells: a sublist can
see a smaller between-product than the one the source diagram constrains.

Two conditions make it pass.  The kept cells are an infix of the ordered list of
the source diagram, so every split of the piece is a split of the source with the
same list between the two cells, and every kept cell is rebased by one fixed
group element `c`, so its value is `c⁻¹ * value * c`.  Then the piece's
expression is the source's expression conjugated by `c`, and conjugation does not
create the identity.

The rebasing is what a cut actually does: `c` is the value of the path from the
basepoint of the source diagram to the basepoint on the enclosing walk, and each
kept cell keeps its word and takes conjugator `c⁻¹ * conjugator`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-! ## Conjugation of ordered cell values -/

/-- Rebasing every cell by one element conjugates the product of their
values. -/
theorem prod_map_value_conj {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {M N : CombMap.{v}} {outerM : M.Face} {outerN : N.Face} (c : G)
    (phi : RelatorCell M outerM W → RelatorCell N outerN W)
    (hvalue : ∀ C : RelatorCell M outerM W,
      (phi C).value = c⁻¹ * C.value * c)
    (l : List (RelatorCell M outerM W)) :
    ((l.map phi).map RelatorCell.value).prod =
      c⁻¹ * (l.map RelatorCell.value).prod * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, hvalue]
      group

/-- The rebased no-cancellation expression is the conjugate of the original
one. -/
theorem cellValue_conj_expression {G : Type u} [Group G] (c b x y : G) :
    (c⁻¹ * b * c)⁻¹ * (c⁻¹ * x * c) * (c⁻¹ * b * c) * (c⁻¹ * y * c) =
      c⁻¹ * (b⁻¹ * x * b * y) * c := by
  group

/-- A conjugate of a nonidentity element is not the identity. -/
theorem conj_ne_one_of_ne_one {G : Type u} [Group G] (c x : G) (h : x ≠ 1) :
    c⁻¹ * x * c ≠ 1 := by
  intro hcon
  apply h
  calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    _ = c * 1 * c⁻¹ := by rw [hcon]
    _ = 1 := by group

/-! ## The transport -/

/-- A diagram whose ordered relator cells are an infix of a reduced diagram's,
rebased by one fixed element, is reduced.  This is the reducedness half of the
Lemma 6.5 cut. -/
theorem reduced_of_infix_of_conj
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta Xi : DiscDiagram.{u, w, v} W) (c : G)
    (phi : RelatorCell Delta.toCombMap Delta.outerFace W →
      RelatorCell Xi.toCombMap Xi.outerFace W)
    (hvalue : ∀ C : RelatorCell Delta.toCombMap Delta.outerFace W,
      (phi C).value = c⁻¹ * C.value * c)
    (pre enclosed suf :
      List (RelatorCell Delta.toCombMap Delta.outerFace W))
    (hinfix : Delta.relatorCells = pre ++ enclosed ++ suf)
    (hcells : Xi.relatorCells = enclosed.map phi)
    (hred : Delta.Reduced) : Xi.Reduced := by
  intro pre' between' suf' D₁ D₂ hsplit
  rw [hcells] at hsplit
  obtain ⟨e1, rest, hrestsplit, _, hrest⟩ := List.map_eq_append_iff.1 hsplit
  obtain ⟨X₁, rest2, hrest2, hX₁, hrest2map⟩ := List.map_eq_cons_iff.1 hrest
  obtain ⟨e2, rest3, hsplit3, hbetween, hrest3⟩ :=
    List.map_eq_append_iff.1 hrest2map
  obtain ⟨X₂, rest4, hrest4, hX₂, _⟩ := List.map_eq_cons_iff.1 hrest3
  have hdelta : Delta.relatorCells =
      (pre ++ e1) ++ X₁ :: (e2 ++ X₂ :: (rest4 ++ suf)) := by
    rw [hinfix, hrestsplit, hrest2, hsplit3, hrest4]
    simp
  have hne := hred (pre ++ e1) e2 (rest4 ++ suf) X₁ X₂ hdelta
  rw [← hbetween, ← hX₁, ← hX₂, prod_map_value_conj c phi hvalue e2,
    hvalue X₁, hvalue X₂, cellValue_conj_expression]
  exact conj_ne_one_of_ne_one c _ hne

end VanKampen
end GGT
end GroupApproximation
