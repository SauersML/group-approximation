import GroupApproximation.GGT.DGOProposition435FiniteLetters
import GroupApproximation.GGT.HullEeSplice

/-!
# The isolated witness, by word surgery

`GGT.RelHyp.DGOProposition435IsolatedWitnessStatement` says that every element
of a joint relative ball is spelled by a joint word of the same length whose
auxiliary letters are maximal isolated components of the cycle closed by the
original peripheral edge.  This module proves it.

The argument is purely combinatorial and uses no hyperbolic geometry.  Take a
spelling of minimal length.  If two of its auxiliary letters carry the same
index `i` and their initial vertices lie in the same left coset of `E i`, the
whole stretch between them can be replaced by a single `i`-letter: the
replacement spells the same element, uses admissible letters, and is strictly
shorter.  It also still avoids `Γ_{H_lam}`, because an auxiliary letter is
never an edge of that graph and the two halves outside the replaced stretch are
read from the same vertices as before.  Minimality therefore forbids such a
pair, and forbidding it is exactly maximality and isolation of every auxiliary
component.

`spliceAux` is that replacement and `spliceAux_shorter` is the contradiction it
produces.  Adjacent auxiliary letters of one index are the special case where
the stretch has length two, so the same surgery merges them; that is what makes
each component maximal, and the general case is what makes it isolated.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G] {Λ : Type v} {I : Type w}

/-! ## Vertices of the auxiliary reading -/

/-- Reading a joint word in the auxiliary alphabet does not move any vertex. -/
theorem vertex_map_auxOfJoint :
    ∀ (w : List (RelLetter G (Sum Λ I))) (v : G) (p : ℕ),
      OsinComponents.vertex v (w.map RelLetter.auxOfJoint) p
        = OsinComponents.vertex v w p := by
  intro w
  induction w with
  | nil => intro v p; cases p <;> rfl
  | cons a t ih =>
      intro v p
      cases p with
      | zero => rfl
      | succ p' =>
          show OsinComponents.vertex (v * (RelLetter.auxOfJoint a).val)
              (t.map RelLetter.auxOfJoint) p'
            = OsinComponents.vertex (v * a.val) t p'
          rw [RelLetter.auxOfJoint_val]
          exact ih _ p'

/-- The cycle and the word have the same vertices up to the closing edge. -/
theorem vertex_auxCycle (w : List (RelLetter G (Sum Λ I))) (h : G) {p : ℕ}
    (hp : p ≤ w.length) :
    OsinComponents.vertex (1 : G) (auxCycle w h) p
      = OsinComponents.vertex (1 : G) w p := by
  have hmap : p ≤ (w.map RelLetter.auxOfJoint).length := by
    rw [List.length_map]
    exact hp
  rw [auxCycle, OsinComponents.vertex_append_left _ _ _ hmap,
    vertex_map_auxOfJoint]

/-- The closing edge of the cycle is a base letter, so it is no component. -/
theorem not_isCompOf_auxCycle_last (w : List (RelLetter G (Sum Λ I))) (h : G)
    (i : I) (hlen : w.length < (auxCycle w h).length) :
    ¬ ((auxCycle w h)[w.length]'hlen).IsCompOf i := by
  have hmap : (w.map RelLetter.auxOfJoint).length = w.length := List.length_map _
  have hget : (auxCycle w h)[w.length]'hlen = RelLetter.base h⁻¹ := by
    show (w.map RelLetter.auxOfJoint ++ [RelLetter.base h⁻¹])[w.length]'hlen = _
    rw [List.getElem_append_right (by omega)]
    simp [hmap]
  rw [hget]
  exact fun hc => hc

/-- A component of the cycle sits at a position of the word. -/
theorem lt_length_of_isCompOf_auxCycle {w : List (RelLetter G (Sum Λ I))}
    {h : G} {i : I} {j : ℕ} (hj : j < (auxCycle w h).length)
    (hc : ((auxCycle w h)[j]'hj).IsCompOf i) : j < w.length := by
  have hj' : j < w.length + 1 := by
    have hcopy := hj
    rw [auxCycle_length] at hcopy
    exact hcopy
  rcases Nat.lt_or_ge j w.length with hlt | hge
  · exact hlt
  · have hje : j = w.length := by omega
    subst hje
    exact absurd hc (not_isCompOf_auxCycle_last w h i hj)

/-- A component of the cycle comes from an auxiliary letter of the word. -/
theorem exists_comp_of_isCompOf_auxCycle {w : List (RelLetter G (Sum Λ I))}
    {h : G} {i : I} {j : ℕ} (hj : j < (auxCycle w h).length)
    (hc : ((auxCycle w h)[j]'hj).IsCompOf i) :
    ∃ (hjw : j < w.length) (e : G),
      (w[j]'hjw) = RelLetter.comp (Sum.inr i) e := by
  have hjw : j < w.length := lt_length_of_isCompOf_auxCycle hj hc
  refine ⟨hjw, ?_⟩
  rw [getElem_auxCycle_of_lt w h hjw hj] at hc
  cases hw : w[j]'hjw with
  | base x =>
      rw [hw] at hc
      exact absurd hc (fun hcc => hcc)
  | comp s e =>
      cases s with
      | inl mu =>
          rw [hw] at hc
          exact absurd hc (fun hcc => hcc)
      | inr j' =>
          rw [hw] at hc
          have hji : j' = i := hc
          rw [hji]
          exact ⟨e, rfl⟩

/-! ## The splice -/

/-- **The splice.**  Positions `p` through `q` of a joint word are replaced by
a single auxiliary `i`-letter spelling the same stretch. -/
def spliceAux (w : List (RelLetter G (Sum Λ I))) (i : I) (p q : ℕ) :
    List (RelLetter G (Sum Λ I)) :=
  w.take p ++
    RelLetter.comp (Sum.inr i)
      ((OsinComponents.vertex (1 : G) w p)⁻¹ *
        OsinComponents.vertex (1 : G) w (q + 1)) :: w.drop (q + 1)

theorem spliceAux_length (w : List (RelLetter G (Sum Λ I))) (i : I) {p q : ℕ}
    (hp : p ≤ q) (hq : q < w.length) :
    (spliceAux w i p q).length = w.length - (q - p) := by
  have hpl : p ≤ w.length := by omega
  simp only [spliceAux, List.length_append, List.length_cons, List.length_take,
    List.length_drop]
  omega

theorem spliceAux_shorter (w : List (RelLetter G (Sum Λ I))) (i : I) {p q : ℕ}
    (hpq : p < q) (hq : q < w.length) :
    (spliceAux w i p q).length < w.length := by
  rw [spliceAux_length w i (le_of_lt hpq) hq]
  omega

theorem listVal_spliceAux (w : List (RelLetter G (Sum Λ I))) (i : I) {p q : ℕ}
    (hq : q < w.length) :
    RelLetter.listVal (spliceAux w i p q) = RelLetter.listVal w := by
  have hq1 : q + 1 ≤ w.length := hq
  have hdrop := OsinComponents.vertex_mul_listVal_drop w hq1
  show RelLetter.listVal (w.take p ++ _ :: w.drop (q + 1)) = _
  rw [OsinComponents.listVal_append, OsinComponents.listVal_take_eq_vertex]
  show OsinComponents.vertex (1 : G) w p *
      ((OsinComponents.vertex (1 : G) w p)⁻¹ *
        OsinComponents.vertex (1 : G) w (q + 1) *
          RelLetter.listVal (w.drop (q + 1))) = RelLetter.listVal w
  rw [← mul_assoc, mul_inv_cancel_left, hdrop]

theorem isLetter_spliceAux {J : RelGenSet G (Sum Λ I)}
    {w : List (RelLetter G (Sum Λ I))} (hlet : ∀ a ∈ w, J.IsLetter a) {i : I}
    {p q : ℕ}
    (hg : ((OsinComponents.vertex (1 : G) w p)⁻¹ *
      OsinComponents.vertex (1 : G) w (q + 1)) ∈ J.fam (Sum.inr i)) :
    ∀ a ∈ spliceAux w i p q, J.IsLetter a := by
  intro a ha
  rw [spliceAux, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | ha | ha
  · exact hlet a (List.mem_of_mem_take ha)
  · rw [ha]
    exact hg
  · exact hlet a (List.mem_of_mem_drop ha)

theorem avoidsFrom_spliceAux {J : RelGenSet G (Sum Λ I)} {lam : Λ}
    {w : List (RelLetter G (Sum Λ I))}
    (hav : AvoidsFrom J.fam (Sum.inl lam) w 1) (i : I) (p q : ℕ) :
    AvoidsFrom J.fam (Sum.inl lam) (spliceAux w i p q) 1 := by
  refine (OsinComponents.avoidsFrom_append J.fam (Sum.inl lam) (w.take p) _
    1).mpr ⟨OsinComponents.avoidsFrom_take J.fam (Sum.inl lam) 1 w p hav, ?_⟩
  rw [OsinComponents.listVal_take_eq_vertex, one_mul]
  refine ⟨?_, ?_⟩
  · rintro ⟨hc, -⟩
    exact absurd hc (fun hcc => Sum.inr_ne_inl hcc)
  · show AvoidsFrom J.fam (Sum.inl lam) (w.drop (q + 1))
      (OsinComponents.vertex (1 : G) w p *
        ((OsinComponents.vertex (1 : G) w p)⁻¹ *
          OsinComponents.vertex (1 : G) w (q + 1)))
    rw [mul_inv_cancel_left]
    exact OsinComponents.avoidsFrom_drop J.fam (Sum.inl lam) 1 w (q + 1) hav

end RelHyp
end GGT
end GroupApproximation
