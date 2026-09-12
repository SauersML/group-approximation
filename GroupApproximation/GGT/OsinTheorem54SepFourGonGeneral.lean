import GroupApproximation.GGT.OsinTheorem54SepFourGonSide
import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# The quadrilateral with no base-only side, for Osin's Lemma 4.9

`GGT/OsinTheorem54SepFourGon.lean` assumes the two short sides `p` and `r` are
spelled by base letters, which is the configuration a relator-separation
argument presents: two long sides joined by two short `X`-paths.  Osin's
Lemma 4.9 presents a different one.  It is a statement about a geodesic
*triangle* `(f,g,h)`, so all of its sides are geodesics and every one of them
can carry `H_λ`-components; in the format of this development the triangle is
the quadrilateral with `p = []`, and `r` is a full side.

So this module drops the base-only hypotheses.  What is left is the honest
content: a non-isolated component of `q` is connected to *some* component of the
quadrilateral, the index of that component lies in one of the four blocks
(`fourGon_index_cases`, which never needed the hypotheses), and the connector
is named.  Which of the four branches can be excluded is then the caller's
business, and depends on what its sides are.

## Two conditionality notices

Nothing in this module is unconditional beyond what it says.  The two leaves
the surrounding chain rests on, and which every consumer inherits:

* `OsinComponents.IsolatedComponentBound` --- Osin's Lemma 4.2, this
  repository's statement of Dahmani--Guirardel--Osin's Proposition 4.13.  It is
  not proved here or anywhere in this repository.  Nothing *in this module*
  consumes it, but the results here are only useful downstream of it: it is what
  turns "deep" into "not isolated", and without it the hypothesis `hnot` below
  has no supply.
* `OsinComponents.LemmaFourEight` --- Osin's Lemma 4.8.  It is an unproved
  `def … : Prop`, consumed as a binder by `OsinGeodesicWord` and
  `OsinPenetration` and never discharged, so `sepSet_finite` --- and therefore
  the finiteness of `sepCard`, and therefore the very existence of the `sep`
  field of `SepDataFam` --- is conditional on it.  It is a debt in its own
  right, not bookkeeping.

## What proving Lemma 4.8 would take

Unfolded, `LemmaFourEight D lam Dc` says that the set of essentially penetrated
cosets does not depend on which geodesic from `f` to `g` is used: `sepSet` is
defined by "some geodesic", and 4.8 upgrades that to "every geodesic".

It is **not an independent debt**.  Two geodesics `w`, `w'` from `f` to `g`
form a geodesic bigon, which in this development is the quadrilateral with
`p = r = []` --- and both base-only hypotheses of
`exists_other_component_fourGon` then hold vacuously, so the *landed* two-branch
form already applies to it.  A coset essentially penetrated by `w` has a
component whose span escapes `D.relBall lam Dc`, so for `Dc` past the constant
of `IsolatedComponentBound` at `n = 2` that component is not isolated in the
bigon; `not_connected_of_isCompStart_of_geodesic` below rules out its being
connected to another component of `w` itself, since `w` is geodesic; so it is
connected to a component of `w'`, and connected components name the same coset
by `mk_eq_mk_of_connected`.  That gives penetration of the same coset by `w'`.

What is left after that is one estimate and not more: that the penetration by
`w'` is *essential* too, i.e. that the span of the connected component on the
other side also escapes the ball.  The two spans differ by the two connecting
elements, so this is a comparison, not a new geometric input.

So Lemma 4.8 sits downstream of the same leaf `IsolatedComponentBound` that
Lemma 4.2 is, plus that comparison --- which is worth knowing before anyone
budgets it as a separate piece of work.

## A warning about the index type, for whoever proves Lemma 4.9

Osin's `S(f,g;D)` is the set of separating cosets over **all** `λ` at once,
while `OsinComponents.sepSet` and `sepCard` are stated per `λ`.  The `sep` field
of `SepDataFam` is a single natural number, so it has to be the sum
`∑ λ, sepCard D λ Dc f g`, finite exactly because `Λ` is finite.

**So Lemma 4.9 must be proved in its global form** --- at most two exceptional
cosets across all `λ` together.  A per-`λ` Lemma 4.9 summed over `Λ` gives
defect `2|Λ|`, not `2`, and the field `sep_triangle` would then be false at
`|Λ| ≥ 2`.  The finiteness of `Λ` is doing two jobs here: it is Osin's own
hypothesis on the collection, and it is what makes `sep` a number at all.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The two remaining side addresses -/

/-- **A vertex of the quadrilateral in the first block is a vertex of `p`.** -/
theorem vertex_fourGon_first (p q r s : List (RelLetter G Λ)) (v : G) {n : ℕ}
    (hn : n ≤ p.length) :
    vertex v (p ++ q ++ r ++ revWord s) n = vertex v p n := by
  have h1 : n ≤ (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : n ≤ (p ++ q).length := by
    rw [List.length_append]
    omega
  rw [vertex_append_of_le _ _ _ _ h1, vertex_append_of_le _ _ _ _ h2,
    vertex_append_of_le _ _ _ _ hn]

/-- **A vertex of the quadrilateral in the third block is a vertex of `r`**,
read from the endpoint of `p ++ q`. -/
theorem vertex_fourGon_third (p q r s : List (RelLetter G Λ)) (v : G) {m : ℕ}
    (hm : m ≤ r.length) :
    vertex v (p ++ q ++ r ++ revWord s) (p.length + q.length + m)
      = v * RelLetter.listVal p * RelLetter.listVal q * vertex (1 : G) r m := by
  have hlen : (p ++ q).length = p.length + q.length := List.length_append
  have h1 : p.length + q.length + m ≤ (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  rw [vertex_append_of_le _ _ _ _ h1, ← hlen,
    vertex_append_add (p ++ q) r v m, listVal_append,
    vertex_eq_mul_vertex_one r (v * (RelLetter.listVal p * RelLetter.listVal q))
      m]
  group

/-! ## The connector, at an arbitrary index -/

/-- **The connector between a component of `q` and anything else in the
quadrilateral.**

One statement covers all four sides: the vertex of `q`, translated into the
polygon by `listVal p`, reaches the polygon vertex at the other index by an
element of `H_λ`.  A caller who knows which block the other index lies in
rewrites the right-hand side with `vertex_fourGon_first`,
`vertex_fourGon_side`, `vertex_fourGon_third` or
`vertex_fourGon_opposite_closed` to read it in that side's own coordinates.

No bound on `h` is asserted. -/
theorem exists_connector_fourGon_index (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ)) {i n : ℕ} (hi : i ≤ q.length)
    (hconn : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
      (p.length + i) n) :
    ∃ h : G, h ∈ D.fam lam ∧
      RelLetter.listVal p * vertex (1 : G) q i * h
        = vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
  have hv : vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i)
      = RelLetter.listVal p * vertex (1 : G) q i := by
    rw [vertex_fourGon_side p q r s 1 hi, one_mul]
  have hc : (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) n ∈ D.fam lam := hconn
  rw [hv] at hc
  exact ⟨_, hc, by group⟩

/-! ## The isolated-component form with no hypothesis on the sides -/

/-- **A non-isolated component of `q` is connected to some component of the
quadrilateral, wherever that component sits.**

This is `exists_other_component_fourGon` with the base-only hypotheses on `p`
and `r` removed.  Nothing else changes: the two hypotheses were only ever used
to empty two of the four branches of `fourGon_index_cases`, and a caller whose
short sides *are* base-spelled still gets that from
`not_isCompStart_fourGon_first` and `not_isCompStart_fourGon_third`.

For Osin's Lemma 4.9 the polygon is a geodesic triangle, which is this
statement with `p = []`: the first branch is then empty because no index is
below `0`, and the surviving three are the three sides.  Which of those can be
excluded is the caller's business --- see
`not_connected_of_isCompStart_of_geodesic` for the one that closes on its own.

The hypothesis `hnot` is supplied by `IsolatedComponentBound`, which is not
proved in this repository; this theorem does not consume it, but has no other
source for its hypothesis. -/
theorem exists_other_component_fourGon_general (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ)) {i : ℕ} (hi : i ≤ q.length)
    (hstart : IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i))
    (hnot : ¬ IsIsolated D.fam lam 1 (p ++ q ++ r ++ revWord s)
      (p.length + i)) :
    ∃ n : ℕ, n ≠ p.length + i ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s) n ∧
      (n < p.length ∨ (∃ i' : ℕ, i' ≤ q.length ∧ n = p.length + i') ∨
        (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
        (∃ j : ℕ, j ≤ s.length ∧
          n = p.length + q.length + r.length + (s.length - j))) ∧
      ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q i * h
          = vertex (1 : G) (p ++ q ++ r ++ revWord s) n := by
  have hB : ¬ ∀ n : ℕ, n ≠ p.length + i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) n →
        ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
          (p.length + i) n := by
    intro hall
    exact hnot ⟨hstart, hall⟩
  push Not at hB
  obtain ⟨n, hne, hnstart, hnconn⟩ := hB
  obtain ⟨hnlt, -⟩ := isCompOf_getElem_of_isCompStart hnstart
  exact ⟨n, hne, hnstart, fourGon_index_cases p q r s (le_of_lt hnlt),
    exists_connector_fourGon_index D lam p q r s hi hnconn⟩

/-! ## A geodesic side never connects two of its own components -/

/-- **An element of `H_λ` is one letter away.** -/
theorem wordDist_le_one_of_mem_fam (D : RelGenSet G Λ) {lam : Λ} {x y : G}
    (h : x⁻¹ * y ∈ D.fam lam) :
    wordDist D.alphabet.carrier x y ≤ 1 := by
  have hlet : ∀ a ∈ [RelLetter.comp lam (x⁻¹ * y)], D.IsLetter a := by
    intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact h
  have hle := wordNorm_listVal_le D [RelLetter.comp lam (x⁻¹ * y)] hlet
  have hval : RelLetter.listVal [RelLetter.comp lam (x⁻¹ * y)] = x⁻¹ * y := by
    simp [listVal_singleton, RelLetter.val]
  rw [hval] at hle
  show wordNorm D.alphabet.carrier (x⁻¹ * y) ≤ 1
  exact hle

omit [Group G] in
/-- **Two distinct component starts are at least two apart.**  A component is a
maximal run, so the letter just before a component start is not a component
letter, while the letter at a component start is. -/
theorem two_le_of_isCompStart {lam : Λ} {w : List (RelLetter G Λ)} {i j : ℕ}
    (hi : IsCompStart lam w i) (hj : IsCompStart lam w j) (hij : i < j) :
    i + 2 ≤ j := by
  by_contra hcon
  have hji : j = i + 1 := by omega
  obtain ⟨hn, hcomp⟩ := isCompOf_getElem_of_isCompStart hi
  obtain ⟨k, -, -, -, hpre, -⟩ := hj
  exact hpre i hji hn hcomp

/-- **No two distinct components of a geodesic word are connected.**

Two connected components have their initial vertices in one coset of `H_λ`, so
one letter apart; but they are at least two apart along the word, and a
geodesic word realises that separation as distance.  So the same-side branch of
`exists_other_component_fourGon_general` closes for a geodesic side --- via
`connected_fourGon_side_iff`, which identifies connectedness across the
`q`-block of the quadrilateral with connectedness inside `q` at basepoint `1`.

This is the exact point at which "geodesic" is stronger than
"`(μ,b)`-quasi-geodesic": for `μ(1 + b) ≥ 2` the two-apart estimate no longer
beats the one-letter bound, and the side `[comp λ h₁, base x, comp λ h₂]` with
`x ∈ X ∩ H_λ` is a `(3,0)`-quasi-geodesic whose two components *are*
connected. -/
theorem not_connected_of_isCompStart_of_geodesic (D : RelGenSet G Λ) {lam : Λ}
    {f g : G} {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {i j : ℕ}
    (hi : IsCompStart lam w i) (hj : IsCompStart lam w j) (hne : i ≠ j) :
    ¬ Connected D.fam lam f w i j := by
  have key : ∀ a b : ℕ, a < b → IsCompStart lam w a → IsCompStart lam w b →
      Connected D.fam lam f w a b → False := by
    intro a b hab ha hb hcon
    have hcon' : (vertex f w a)⁻¹ * vertex f w b ∈ D.fam lam := hcon
    have h2 : a + 2 ≤ b := two_le_of_isCompStart ha hb hab
    have hbw : b ≤ w.length := by
      obtain ⟨k, hbk, hkw, -, -, -⟩ := hb
      omega
    have h1 : wordDist D.alphabet.carrier (vertex f w a) (vertex f w b) ≤ 1 :=
      wordDist_le_one_of_mem_fam D hcon'
    have h3 := sub_le_wordDist_vertex D hw a b (le_of_lt hab) hbw
    omega
  intro hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key i j hlt hi hj hc
  · exact key j i hgt hj hi (connected_symm hc)

end OsinComponents
end GGT
end GroupApproximation
