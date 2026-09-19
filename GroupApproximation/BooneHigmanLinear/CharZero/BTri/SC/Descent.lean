import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Building
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Simple connectivity by descent (Z1-base, piece Z.4, part 1: the combinatorial engine)

A discrete Morse argument for the clique 2-complex of a simple graph `G`, in the vocabulary of
`BTri.Building` (`TriStep`, `TriSimplyConnected`). Let `f : V → ℕ` be a height with base vertex
`v₀`, and assume:
* `ne_of_adj`: adjacent vertices have different heights (no horizontal edges);
* `down`: every vertex other than `v₀` has a strictly lower neighbour;
* `link`: descending links are connected. Any two neighbours `u, w` of `v` that lie below `v`
  are joined by a path of edges whose vertices are all neighbours of `v` below `v`.

Then `G` is connected, and every closed edge path at `v₀` reduces to `[v₀]` by backtracks and
triangles (`triSimplyConnected_of_descent`).

Proof: take a vertex `v` of maximal height on the path. Its two path neighbours `u, w` are
below it, so they lie in the descending link of `v`. Push the path `u v w` across the triangles
`(aᵢ, aᵢ₊₁, v)` of a descending-link path `u = a₀, …, a_k = w`, then cancel the final backtrack.
One occurrence of `f v` is replaced by finitely many strictly smaller heights, so the multiset of
heights decreases in the Dershowitz–Manna order, which is well founded.

`BuildingDescentStatement` is the building-specific input (piece Z.4, part 2): a height on the
Ã₂ lattice building with these three properties. The plan is on board `k2-poly.md`: the height of
the class of `diag(p^a, p^b, 1)` is `a² + b`, and its descending link is a single point
(`b = 0`) or the closed star of one line of `PG(2, A/p)` (`b ≥ 1`). With it,
`buildingSimplyConnected_of_descent` gives `BuildingSimplyConnectedStatement`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri
namespace SC

section Engine

variable {V : Type*}

/-- Adjacency inside the descending link of `v` for the height `f`: an edge `a b` of `G` whose
ends are both neighbours of `v` strictly below `v`. -/
def DescAdj (G : SimpleGraph V) (f : V → ℕ) (v a b : V) : Prop :=
  G.Adj a b ∧ G.Adj a v ∧ G.Adj b v ∧ f a < f v ∧ f b < f v

/-- **Descent data** for a height `f : V → ℕ` with base vertex `v₀`. -/
structure DescentData (G : SimpleGraph V) (f : V → ℕ) (v₀ : V) : Prop where
  /-- No horizontal edges. -/
  ne_of_adj : ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v
  /-- Every vertex except the base has a strictly lower neighbour. -/
  down : ∀ v, v ≠ v₀ → ∃ u, G.Adj u v ∧ f u < f v
  /-- Descending links are connected. -/
  link : ∀ ⦃v u w : V⦄, G.Adj u v → G.Adj w v → f u < f v → f w < f v →
    Relation.ReflTransGen (DescAdj G f v) u w

variable {G : SimpleGraph V} {f : V → ℕ} {v₀ : V}

/-- The base vertex is the unique minimum of the height. -/
theorem DescentData.base_lt (hD : DescentData G f v₀) {z : V} (hz : z ≠ v₀) : f v₀ < f z := by
  suffices H : ∀ n, ∀ z, f z = n → z ≠ v₀ → f v₀ < f z from H (f z) z rfl hz
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih z hzn hne
  obtain ⟨u, hu, hfu⟩ := hD.down z hne
  by_cases huv : u = v₀
  · subst huv
    exact hfu
  · exact lt_trans (ih (f u) (hzn ▸ hfu) u rfl huv) hfu

/-- Every vertex is reachable from the base. -/
theorem DescentData.reachable (hD : DescentData G f v₀) (z : V) : G.Reachable v₀ z := by
  suffices H : ∀ n, ∀ z, f z = n → G.Reachable v₀ z from H (f z) z rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih z hzn
  by_cases h : z = v₀
  · subst h
    exact SimpleGraph.Reachable.refl _
  · obtain ⟨u, hu, hfu⟩ := hD.down z h
    exact (ih (f u) (hzn ▸ hfu) u rfl).trans hu.reachable

/-! ### List bookkeeping -/

theorem head?_append_of_ne_nil {α : Type*} {l : List α} (l' : List α) (h : l ≠ []) :
    (l ++ l').head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

theorem nil_or_append_singleton {α : Type*} : ∀ l : List α, l = [] ∨ ∃ L b, l = L ++ [b]
  | [] => Or.inl rfl
  | a :: l => Or.inr <| by
      rcases nil_or_append_singleton l with rfl | ⟨L, b, rfl⟩
      · exact ⟨[], a, rfl⟩
      · exact ⟨a :: L, b, rfl⟩

theorem exists_max_mem {α : Type*} (g : α → ℕ) :
    ∀ l : List α, l ≠ [] → ∃ v ∈ l, ∀ x ∈ l, g x ≤ g v
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun x hx => by
      rw [List.mem_singleton] at hx
      subst hx
      exact le_rfl⟩
  | a :: b :: l, _ => by
      obtain ⟨v, hv, hmax⟩ := exists_max_mem g (b :: l) (List.cons_ne_nil _ _)
      by_cases hav : g v ≤ g a
      · refine ⟨a, by simp, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact (hmax x hx).trans hav
      · refine ⟨v, List.mem_cons_of_mem _ hv, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact hmax x hx

/-- A vertex that is neither the first nor the last entry of a list sits strictly inside it. -/
theorem exists_decomp {α : Type*} {F : List α} {v : α} (hv : v ∈ F) (h0 : F.head? ≠ some v)
    (h1 : F.reverse.head? ≠ some v) : ∃ A u w B, F = A ++ u :: v :: w :: B := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hv
  rcases nil_or_append_singleton L₁ with rfl | ⟨A, u, rfl⟩
  · exact (h0 rfl).elim
  · cases L₂ with
    | nil => exact (h1 (by simp)).elim
    | cons w B => exact ⟨A, u, w, B, by simp⟩

/-- Replacing a nonempty middle block by another with the same first and last entries keeps
the first and last entries of the whole list. -/
theorem ends_eq {α : Type*} {A B X Y : List α} (hX : X ≠ []) (hY : Y ≠ [])
    (h0 : X.head? = Y.head?) (h1 : X.reverse.head? = Y.reverse.head?) :
    (A ++ X ++ B).head? = (A ++ Y ++ B).head? ∧
      (A ++ X ++ B).reverse.head? = (A ++ Y ++ B).reverse.head? := by
  constructor
  · cases A with
    | nil =>
      simp only [List.nil_append]
      rw [head?_append_of_ne_nil B hX, head?_append_of_ne_nil B hY, h0]
    | cons a A => rfl
  · simp only [List.reverse_append]
    rcases hB : B.reverse with _ | ⟨b, B'⟩
    · simp only [List.nil_append]
      rw [head?_append_of_ne_nil (l := X.reverse) _ (by simpa using hX),
        head?_append_of_ne_nil (l := Y.reverse) _ (by simpa using hY), h1]
    · rfl

/-! ### Pushing a peak across its descending link -/

/-- A path `u v w` whose ends lie in the descending link of `v`, and are joined there, is
equivalent (in any context) to a path `P` from `u` to `w` inside the descending link. -/
theorem push_peak (G : SimpleGraph V) (f : V → ℕ) {v w : V} (hwv : G.Adj w v)
    (hfw : f w < f v) {u : V} (h : Relation.ReflTransGen (DescAdj G f v) u w)
    (huv : G.Adj u v) (hfu : f u < f v) :
    ∃ P : List V, P.head? = some u ∧ P.reverse.head? = some w ∧ List.IsChain G.Adj P ∧
      (∀ x ∈ P, f x < f v) ∧
      ∀ A B : List V, Relation.EqvGen (TriStep G) (A ++ u :: v :: w :: B) (A ++ P ++ B) := by
  revert huv hfu
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ _
    refine ⟨[w], rfl, rfl, List.IsChain.singleton w, ?_, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      rw [hx]
      exact hfw
    · intro A B
      have hstep := TriStep.backtrack (G := G) A B w v hwv
      have e : A ++ [w] ++ B = A ++ w :: B := by simp
      rw [e]
      exact Relation.EqvGen.rel _ _ hstep
  | @head a c hac hcw ih =>
    intro hav hfa
    obtain ⟨hac', -, hcv, -, hfc⟩ :
        G.Adj a c ∧ G.Adj a v ∧ G.Adj c v ∧ f a < f v ∧ f c < f v := hac
    obtain ⟨P, hPc, hPw, hPchain, hPf, hPhom⟩ := ih hcv hfc
    refine ⟨a :: P, rfl, ?_, ?_, ?_, ?_⟩
    · have hne : P.reverse ≠ [] := by
        intro hnil
        rw [hnil] at hPw
        exact absurd hPw (by simp)
      rw [List.reverse_cons, head?_append_of_ne_nil _ hne]
      exact hPw
    · cases P with
      | nil => exact absurd hPc (by simp)
      | cons c' P' =>
        simp only [List.head?_cons, Option.some.injEq] at hPc
        subst hPc
        exact List.IsChain.cons_cons hac' hPchain
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hfa
      · exact hPf x hx
    · intro A B
      have h1 : Relation.EqvGen (TriStep G) (A ++ a :: v :: w :: B)
          (A ++ a :: c :: v :: w :: B) :=
        Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (TriStep.triangle A (w :: B) a c v hac' hcv hav))
      have h2 := hPhom (A ++ [a]) B
      have e1 : A ++ [a] ++ c :: v :: w :: B = A ++ a :: c :: v :: w :: B := by simp
      have e2 : A ++ [a] ++ P ++ B = A ++ a :: P ++ B := by simp
      rw [e1, e2] at h2
      exact Relation.EqvGen.trans _ _ _ h1 h2

/-! ### The descent -/

/-- **Descent.** Every closed edge path at the base (as a vertex list) reduces to `[v₀]`. -/
theorem homotopic_of_descent (hD : DescentData G f v₀) :
    ∀ F : List V, List.IsChain G.Adj F → F.head? = some v₀ → F.reverse.head? = some v₀ →
      Relation.EqvGen (TriStep G) F [v₀] := by
  suffices H : ∀ m : Multiset ℕ, ∀ F : List V, ((F.map f : List ℕ) : Multiset ℕ) = m →
      List.IsChain G.Adj F → F.head? = some v₀ → F.reverse.head? = some v₀ →
      Relation.EqvGen (TriStep G) F [v₀] from fun F => H _ F rfl
  intro m
  refine (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction
    (C := fun m => ∀ F : List V, ((F.map f : List ℕ) : Multiset ℕ) = m →
      List.IsChain G.Adj F → F.head? = some v₀ → F.reverse.head? = some v₀ →
      Relation.EqvGen (TriStep G) F [v₀]) m ?_
  intro m ih F hFm hF h0 h1
  by_cases hF1 : F = [v₀]
  · subst hF1
    exact Relation.EqvGen.refl _
  -- Some vertex of the path lies above the base.
  obtain ⟨z, hzF, hz⟩ : ∃ z ∈ F, f v₀ < f z := by
    rcases F with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp at h0
    · simp only [List.head?_cons, Option.some.injEq] at h0
      subst h0
      exact absurd rfl hF1
    · simp only [List.head?_cons, Option.some.injEq] at h0
      subst h0
      have hxy : G.Adj x y := (List.isChain_cons_cons.1 hF).1
      exact ⟨y, by simp, hD.base_lt hxy.ne.symm⟩
  -- A highest vertex `v` of the path sits strictly inside it.
  obtain ⟨v, hvF, hvmax⟩ := exists_max_mem f F (List.ne_nil_of_mem hzF)
  have hfv : f v₀ < f v := lt_of_lt_of_le hz (hvmax z hzF)
  have hvne : v ≠ v₀ := by
    rintro rfl
    exact lt_irrefl _ hfv
  have h0' : F.head? ≠ some v := by
    rw [h0]
    exact fun h => hvne (Option.some.inj h).symm
  have h1' : F.reverse.head? ≠ some v := by
    rw [h1]
    exact fun h => hvne (Option.some.inj h).symm
  obtain ⟨A, u, w, B, rfl⟩ := exists_decomp hvF h0' h1'
  obtain ⟨hA, huvwB⟩ := List.isChain_split.1 hF
  obtain ⟨huv, hvwB⟩ := List.isChain_cons_cons.1 huvwB
  obtain ⟨hvw, hwB⟩ := List.isChain_cons_cons.1 hvwB
  have hfu : f u < f v := lt_of_le_of_ne (hvmax u (by simp)) (hD.ne_of_adj huv)
  have hfw : f w < f v := lt_of_le_of_ne (hvmax w (by simp)) (hD.ne_of_adj hvw.symm)
  obtain ⟨P, hPu, hPw, hPchain, hPf, hPhom⟩ :=
    push_peak G f hvw.symm hfw (hD.link huv hvw.symm hfu hfw) huv hfu
  -- Normalize `P` as `u :: P₁ = P₂ ++ [w]`.
  obtain ⟨P₁, rfl⟩ : ∃ P₁, P = u :: P₁ := by
    cases P with
    | nil => exact absurd hPu (by simp)
    | cons a P₁ =>
      simp only [List.head?_cons, Option.some.injEq] at hPu
      exact ⟨P₁, by rw [hPu]⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, u :: P₁ = P₂ ++ [w] := by
    rcases nil_or_append_singleton (u :: P₁) with h | ⟨P₂, b, h⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · have hb : b = w := by
        rw [h] at hPw
        simpa using hPw
      exact ⟨P₂, by rw [h, hb]⟩
  -- The new path is a closed edge path at the base.
  have hchainPB : List.IsChain G.Adj (u :: P₁ ++ B) := by
    rw [show u :: P₁ ++ B = P₂ ++ w :: B by rw [hP₂]; simp]
    exact List.isChain_split.2 ⟨hP₂ ▸ hPchain, hwB⟩
  have hchain' : List.IsChain G.Adj (A ++ (u :: P₁) ++ B) := by
    rw [List.append_assoc]
    exact List.isChain_split.2 ⟨hA, hchainPB⟩
  have e : A ++ [u, v, w] ++ B = A ++ u :: v :: w :: B := by simp
  obtain ⟨h0'', h1''⟩ := ends_eq (A := A) (B := B) (X := [u, v, w]) (Y := u :: P₁)
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) rfl (by rw [hPw]; simp)
  rw [e] at h0'' h1''
  have hh0 : (A ++ (u :: P₁) ++ B).head? = some v₀ := h0''.symm.trans h0
  have hh1 : (A ++ (u :: P₁) ++ B).reverse.head? = some v₀ := h1''.symm.trans h1
  -- The multiset of heights drops: one `f v` is replaced by heights below `f v`.
  have hdm : Multiset.IsDershowitzMannaLT
      (((A ++ (u :: P₁) ++ B).map f : List ℕ) : Multiset ℕ) m := by
    rw [← hFm]
    refine ⟨((A.map f ++ B.map f : List ℕ) : Multiset ℕ),
      (((u :: P₁).map f : List ℕ) : Multiset ℕ), (([u, v, w].map f : List ℕ) : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
    · simp
    · simp only [List.map_append, ← Multiset.coe_add]
      exact add_right_comm _ _ _
    · rw [← e]
      simp only [List.map_append, ← Multiset.coe_add]
      exact add_right_comm _ _ _
    · intro y hy
      rw [Multiset.mem_coe, List.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨f v, by simp, hPf x hx⟩
  exact Relation.EqvGen.trans _ _ _ (hPhom A B)
    (ih _ hdm (A ++ (u :: P₁) ++ B) rfl hchain' hh0 hh1)

/-- **The engine, in the interface's form.** -/
theorem triSimplyConnected_of_descent (hD : DescentData G f v₀) : TriSimplyConnected G v₀ := by
  intro l hl hlast
  refine homotopic_of_descent hD (v₀ :: l) hl rfl ?_
  rw [List.head?_reverse, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast]

theorem connected_of_descent (hD : DescentData G f v₀) : G.Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).2 ⟨v₀, hD.reachable⟩

#audit_axioms triSimplyConnected_of_descent
#audit_axioms connected_of_descent

end Engine

/-! ### Piece Z.4 reduced to building descent data -/

/-- **Piece Z.4, part 2 (open).** The Ã₂ lattice building carries descent data at the standard
vertex. The planned height is `a² + b` on the class of `diag(p^a, p^b, 1)` (`a ≥ b ≥ 0`, Cartan
coordinates relative to `A³`). Its descending link is one point when `b = 0` and the closed
star of one line of `PG(2, A/p)` when `b ≥ 1`. See board `k2-poly.md`. -/
def BuildingDescentStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] (p : A), Prime p →
    ∃ f : Vertex A (Localization.Away p) p → ℕ,
      DescentData (buildingGraph A (Localization.Away p) p) f
        (baseVertex A (Localization.Away p) p)

/-- **Piece Z.4 from building descent data.** -/
theorem buildingSimplyConnected_of_descent (h : BuildingDescentStatement) :
    BuildingSimplyConnectedStatement := by
  intro A iA iD iP p hp
  obtain ⟨f, hD⟩ := h A p hp
  exact ⟨connected_of_descent hD, triSimplyConnected_of_descent hD⟩

#audit_axioms buildingSimplyConnected_of_descent

end SC
end BTri
end BooneHigmanLinear
end GroupApproximation
