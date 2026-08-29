import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# Cutting a polygon between two connected components

Dahmani--Guirardel--Osin's companion to the isolated-component bound (their
Lemma 4.21, named in prose at `GGT/WPDDGOReduction.lean`) is the statement that a
*connector* between two components of a quasi-geodesic polygon is `d̂_lam`-bounded.
The separating-coset construction needs it because the connectors it produces are
non-isolated by construction, so `OsinComponents.IsolatedComponentBound` does not
apply to them directly.

This module fixes which connector is bounded.  Concept grep before writing:
`connector` and `cut` across the tree (`OsinTheorem54SepFourGonPinning`,
`OsinTheorem54SepFourGonGeneral`, `HullSCRelatorSeparationConnector`,
`WPDDGOReduction`) --- what exists there is `index_le_of_connector` and
`exists_connector_fourGon_run`, which locate a connector inside a quadrilateral;
nothing bounds one in `d̂_lam`, and no cut of a polygon is formed anywhere.  The
list and vertex arithmetic is reused rather than restated: `listVal_take_split`
(SepFourGonPinning), `vertex_append_of_le`, `vertex_append_add`,
`vertex_eq_mul_vertex_one` (SepPolygonVertex), `vertex_take_eq` (SepFinite),
`vertex_drop_eq` (DGOIsolatedComponentBridge), `connected_pair`
(DGOIsolatedComponentCoset).

## What is false: the start-to-start form

`not_connectedPairSpan_of_infinite` refutes

    IsComp lam w i k → IsComp lam w i' k' → i ≠ i' → Connected D.fam lam v w i i'
      → (vertex v w i)⁻¹ * vertex v w i' ∈ D.relBall lam (C * n) ,

for `(μ,b) = (1,0)` and `n = 4`.  The witness is the word already in the tree as
`connected_pair`, read from `1`:

    w = [comp lam h, base x, base x⁻¹, comp lam h⁻¹] ,   h ∈ H lam, x ∈ X .

It is closed, its components at `0` and at `3` are connected (the vertex at `3` is
`h`), and with the cut function `c s = s` every side is a single edge, so the
polygon hypothesis reduces to `1 ≤ d(vertex s, vertex (s+1))`, i.e. to no letter
being trivial.  The conclusion would put *every* `h ∈ H lam` into the single ball
`D.relBall lam (4C)`, against `IsHyperbolicallyEmbedded.locallyFinite` --- the
mechanism of `not_isHyperbolicallyEmbedded_of_fam_subset_base`.

The failure is structural, not an artefact of the witness.  The element
`(vertex v w i)⁻¹ * vertex v w i'` crosses the first component, whose span
`(vertex v w i)⁻¹ * vertex v w k` is unbounded: that component is *not* isolated,
being connected to the second one, which is the hypothesis itself.  Cutting the
polygon between the two components bounds the closing edge and nothing else.

## What is true: the end-to-start form, at an innermost pair

`connector_mem_relBall`: from the isolated-component bound at `n ≤ 6` sides, for a
connected pair with no component start between them connected to the first,

    (vertex v w i')⁻¹ * vertex v w k ∈ D.relBall lam (C * n) ,   n ≤ 5 ,

where `[i,k)` is the first component and `i'` the start of the second.  Writing
`i' = k + m` --- which the proof derives, `k ≤ i'` being forced by maximality ---
it cuts the polygon at `k` and at `k + m` and closes it with the single letter
`comp lam z`, `z = (vertex v w (k+m))⁻¹ * vertex v w k`:

    cutWord w lam k m z = (w.drop k).take m ++ [comp lam z] ,

read from `vertex v w k`.  Its cut function is the given one clipped to
`[k, k+m]` and shifted, with the closing edge as the last of `n + 1` sides; the
closing edge is a component of the cut word because the letters at `k` and at
`k + m - 1` are not `lam`-letters, and it is *isolated* exactly because no
component start strictly between `k` and `k + m` is connected to `i`.  The
degenerate case `z = 1` is disposed of first by `one_mem_relBall`, which is also
what keeps the last side quasi-geodesic in the surviving case: `z ≠ 1` gives
`1 ≤ d`, and `1/μ - b ≤ 1` since `μ ≥ 1` and `b ≥ 0`.

The innermost hypothesis cannot be dropped.  At `(μ,b) = (1,2)`, with four sides
of lengths `2,2,2,1` --- for which the quasi-geodesic clause is vacuous, every
index gap inside a side being at most `b` --- the word

    [comp lam m, base x, base x⁻¹, comp lam m, base x, base x⁻¹, comp lam m⁻²]

read from `1` has vertices `1, m, mx, m, m², m²x, m², 1` and components at `0`,
`3` and `6`, pairwise connected.  For the pair `(0, 6)`, which is not innermost,
the end-to-start element is `(vertex 1)⁻¹ * vertex 6 = m`, unbounded as `m` runs
over `H lam`.  That configuration is recorded here in prose; the formal content of
this module is the two theorems above.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  A nontrivial letter moves the vertex -/

/-- **A letter with nontrivial value moves the vertex.**  The dual of
`wordDist_vertex_le` (SepFourGonPinning), which bounds the distance from above:
here the letter's value is the difference of the two vertices, so the distance is
its word norm, which is positive exactly when the value is not `1`. -/
theorem one_le_wordDist_vertex_succ (D : RelGenSet G Λ) (v : G)
    (w : List (RelLetter G Λ)) (j : ℕ) (hj : j < w.length)
    (hne : (w[j]'hj).val ≠ 1) :
    1 ≤ wordDist D.alphabet.carrier (vertex v w j) (vertex v w (j + 1)) := by
  have hd : wordDist D.alphabet.carrier (vertex v w j) (vertex v w (j + 1))
      = wordNorm D.alphabet.carrier ((vertex v w j)⁻¹ * vertex v w (j + 1)) := rfl
  rw [hd, vertex_succ w v j hj, inv_mul_cancel_left]
  exact one_le_wordNorm D.alphabet.symmetricGenerating hne

/-! ## 2.  The four-letter witness is a `(1,0)`-quasi-geodesic `4`-gon -/

/-- The first letter of `connected_pair`'s word is an `H lam`-component. -/
theorem isComp_pairWord_zero (lam : Λ) (x a : G) :
    IsComp lam
      [RelLetter.comp lam a, RelLetter.base x, RelLetter.base x⁻¹,
        RelLetter.comp lam a⁻¹] 0 1 := by
  refine ⟨Nat.zero_lt_one, by simp, ?_, ?_, ?_⟩
  · intro j _ hj1 hjw
    have hj0 : j = 0 := by omega
    subst hj0
    exact rfl
  · intro j hj
    exact absurd hj (by omega)
  · intro _ hc
    exact hc

/-- The last letter of `connected_pair`'s word is an `H lam`-component. -/
theorem isComp_pairWord_three (lam : Λ) (x a : G) :
    IsComp lam
      [RelLetter.comp lam a, RelLetter.base x, RelLetter.base x⁻¹,
        RelLetter.comp lam a⁻¹] 3 4 := by
  refine ⟨by omega, by simp, ?_, ?_, ?_⟩
  · intro j hj3 hj4 hjw
    have hj : j = 3 := by omega
    subst hj
    exact rfl
  · intro j hj hjw hc
    have hj2 : j = 2 := by omega
    subst hj2
    exact hc
  · intro hk
    exact absurd hk (by simp)

/-- **`connected_pair`'s word is a `(1,0)`-quasi-geodesic `4`-gon.**  Its cut
function is the identity, so each side is a single edge and the quasi-geodesic
clause asks only that no letter has value `1`. -/
theorem isQuasiGeodesicPolygon_pairWord (D : RelGenSet G Λ) (lam : Λ) {x h : G}
    (hh : h ∈ D.fam lam) (hx : x ∈ D.base) (hxinv : x⁻¹ ∈ D.base)
    (hh1 : h ≠ 1) (hx1 : x ≠ 1) :
    IsQuasiGeodesicPolygon D 1 0 4 1
      [RelLetter.comp lam h, RelLetter.base x, RelLetter.base x⁻¹,
        RelLetter.comp lam h⁻¹] := by
  set w : List (RelLetter G Λ) :=
    [RelLetter.comp lam h, RelLetter.base x, RelLetter.base x⁻¹,
      RelLetter.comp lam h⁻¹] with hw
  have hlen : w.length = 4 := by simp [hw]
  have hval : ∀ (j : ℕ) (hj : j < w.length), (w[j]'hj).val ≠ 1 := by
    intro j hj
    have hj4 : j < 4 := by omega
    interval_cases j
    · exact hh1
    · exact hx1
    · exact inv_ne_one.mpr hx1
    · exact inv_ne_one.mpr hh1
  refine ⟨?_, ?_, fun s => s, rfl, hlen.symm, fun s => Nat.le_succ s, ?_⟩
  · intro a ha
    have ha4 : a = RelLetter.comp lam h ∨ a = RelLetter.base x ∨
        a = RelLetter.base x⁻¹ ∨ a = RelLetter.comp lam h⁻¹ := by
      rw [hw] at ha
      simpa using ha
    rcases ha4 with rfl | rfl | rfl | rfl
    · exact hh
    · exact hx
    · exact hxinv
    · exact inv_mem hh
  · rw [hw]
    simp only [RelLetter.listVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, RelLetter.val]
    group
  · intro s hs p q hp hpq hq
    have hp' : s ≤ p := hp
    have hq' : q ≤ s + 1 := hq
    rw [div_one, sub_zero]
    have key : q - p
        ≤ wordDist D.alphabet.carrier (vertex (1 : G) w p) (vertex (1 : G) w q) := by
      rcases Nat.eq_or_lt_of_le hpq with heq | hlt
      · rw [heq, Nat.sub_self]
        exact Nat.zero_le _
      · have hq1 : q = p + 1 := by omega
        subst hq1
        have hpw : p < w.length := by omega
        have hstep := one_le_wordDist_vertex_succ D 1 w p hpw (hval p hpw)
        omega
    exact_mod_cast key

/-! ## 3.  The start-to-start form of Lemma 4.21 is false -/

/-- **No bound on the element between two connected component *starts*.**

The conclusion of the start-to-start form, applied to the four-letter word of
`connected_pair` at every `h ∈ H lam`, puts the whole family inside one relative
ball; local finiteness then makes the family finite.  So the statement fails for
every hyperbolically embedded family with an infinite member, given one
nontrivial letter of `X` whose inverse is again a letter --- which
`OsinTheorem54SepSymmetric.exists_symmetric_base` supplies for the base.

What the cut of a polygon does bound is the element from the END of one component
to the START of the next: see `connector_mem_relBall`. -/
theorem not_connectedPairSpan_of_infinite (D : RelGenSet G Λ) (lam : Λ)
    (hD : D.IsHyperbolicallyEmbedded) (hinf : (D.fam lam : Set G).Infinite)
    {x : G} (hx : x ∈ D.base) (hxinv : x⁻¹ ∈ D.base) (hx1 : x ≠ 1) :
    ¬ (∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
        ∀ (n : ℕ), n ≤ 4 → ∀ (v : G) (u : List (RelLetter G Λ)),
          IsQuasiGeodesicPolygon D mu b n v u →
          ∀ (nu : Λ) (i k i' k' : ℕ), IsComp nu u i k → IsComp nu u i' k' →
            i ≠ i' → Connected D.fam nu v u i i' →
            (vertex v u i)⁻¹ * vertex v u i' ∈ D.relBall nu (C * n)) := by
  intro hstat
  obtain ⟨C, -, hC⟩ := hstat 1 0 le_rfl le_rfl
  refine hinf (Set.Finite.subset
    ((hD.locallyFinite lam (C * 4)).union (Set.finite_singleton (1 : G))) ?_)
  intro h hh
  have hh' : h ∈ D.fam lam := hh
  rcases eq_or_ne h 1 with rfl | hne
  · exact Set.mem_union_right _ rfl
  refine Set.mem_union_left _ ?_
  have hmem := hC 4 le_rfl 1
    [RelLetter.comp lam h, RelLetter.base x, RelLetter.base x⁻¹,
      RelLetter.comp lam h⁻¹]
    (isQuasiGeodesicPolygon_pairWord D lam hh' hx hxinv hne hx1)
    lam 0 1 3 4 (isComp_pairWord_zero lam x h) (isComp_pairWord_three lam x h)
    (by omega) (connected_pair D lam x hh')
  have hspan : (vertex (1 : G)
        [RelLetter.comp lam h, RelLetter.base x, RelLetter.base x⁻¹,
          RelLetter.comp lam h⁻¹] 0)⁻¹ *
      vertex (1 : G)
        [RelLetter.comp lam h, RelLetter.base x, RelLetter.base x⁻¹,
          RelLetter.comp lam h⁻¹] 3 = h := by
    show ((1 : G))⁻¹ * ((1 : G) * h * x * x⁻¹) = h
    group
  rwa [hspan] at hmem

/-! ## 4.  The cut word -/

/-- **The polygon cut out between two components.**  The letters of `w` from `k`
to `k + m`, closed by a single `lam`-letter of value `z`.  It is read from
`vertex v w k`, and it is closed when `z = (vertex v w (k+m))⁻¹ * vertex v w k`. -/
def cutWord (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ) (z : G) :
    List (RelLetter G Λ) :=
  (w.drop k).take m ++ [RelLetter.comp lam z]

omit [Group G] in
/-- The cut word has `m + 1` letters. -/
theorem length_cutWord (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ) (z : G)
    (hm : k + m ≤ w.length) : (cutWord w lam k m z).length = m + 1 := by
  have hlen : ((w.drop k).take m).length = m := by
    have hdr : m ≤ (w.drop k).length := by
      rw [List.length_drop]
      omega
    exact List.length_take_of_le hdr
  show ((w.drop k).take m ++ [RelLetter.comp lam z]).length = m + 1
  rw [List.length_append, hlen]
  simp

omit [Group G] in
/-- The letters of the cut word before the last are letters of `w`. -/
theorem getElem_cutWord_lt (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ) (z : G)
    (hm : k + m ≤ w.length) (p : ℕ) (hp : p < (cutWord w lam k m z).length)
    (hq : k + p < w.length) (hpm : p < m) :
    (cutWord w lam k m z)[p]'hp = w[k + p]'hq := by
  have hlen : ((w.drop k).take m).length = m := by
    have hdr : m ≤ (w.drop k).length := by
      rw [List.length_drop]
      omega
    exact List.length_take_of_le hdr
  show ((w.drop k).take m ++ [RelLetter.comp lam z])[p]'hp = w[k + p]'hq
  rw [List.getElem_append_left (show p < ((w.drop k).take m).length by omega)]
  simp

omit [Group G] in
/-- The last letter of the cut word is the closing letter.  The index is taken as
a parameter with an equation rather than as `m` itself, so that a caller holding
an index it only knows to *equal* `m` need not rewrite under `getElem`. -/
theorem getElem_cutWord_last (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ) (z : G)
    (hm : k + m ≤ w.length) (p : ℕ) (hpm : p = m)
    (hp : p < (cutWord w lam k m z).length) :
    (cutWord w lam k m z)[p]'hp = RelLetter.comp lam z := by
  have hlen : ((w.drop k).take m).length = m := by
    have hdr : m ≤ (w.drop k).length := by
      rw [List.length_drop]
      omega
    exact List.length_take_of_le hdr
  show ((w.drop k).take m ++ [RelLetter.comp lam z])[p]'hp = RelLetter.comp lam z
  rw [List.getElem_append_right (show ((w.drop k).take m).length ≤ p by omega)]
  simp [hlen, hpm]

/-- Every letter of the cut word is admissible. -/
theorem letters_cutWord (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (lam : Λ) (k m : ℕ) {z : G}
    (hz : z ∈ D.fam lam) : ∀ a ∈ cutWord w lam k m z, D.IsLetter a := by
  intro a ha
  have ha' : a ∈ (w.drop k).take m ++ [RelLetter.comp lam z] := ha
  rcases List.mem_append.mp ha' with hau | haz
  · exact hlet a (List.drop_subset k w (List.take_subset m (w.drop k) hau))
  · rw [List.eq_of_mem_singleton haz]
    exact hz

/-- **The segment of `w` between two indices spells the difference of the two
vertices.**  This is `listVal_take_split` (SepFourGonPinning) read at vertices. -/
theorem mul_listVal_take_drop (v : G) (w : List (RelLetter G Λ)) (k m : ℕ) :
    vertex v w k * RelLetter.listVal ((w.drop k).take m) = vertex v w (k + m) := by
  have hsp := listVal_take_split w k (k + m) (Nat.le_add_right k m)
  rw [Nat.add_sub_cancel_left] at hsp
  rw [vertex_eq_mul_listVal_take w v k, vertex_eq_mul_listVal_take w v (k + m),
    mul_assoc, hsp]

/-- The vertices of the cut word, before the closing edge, are vertices of `w`. -/
theorem vertex_cutWord (v : G) (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ)
    (z : G) (hm : k + m ≤ w.length) (p : ℕ) (hp : p ≤ m) :
    vertex (vertex v w k) (cutWord w lam k m z) p = vertex v w (k + p) := by
  have hlen : ((w.drop k).take m).length = m := by
    have hdr : m ≤ (w.drop k).length := by
      rw [List.length_drop]
      omega
    exact List.length_take_of_le hdr
  show vertex (vertex v w k) ((w.drop k).take m ++ [RelLetter.comp lam z]) p
      = vertex v w (k + p)
  rw [vertex_append_of_le ((w.drop k).take m) [RelLetter.comp lam z]
      (vertex v w k) p (show p ≤ ((w.drop k).take m).length by omega),
    vertex_take_eq (vertex v w k) (w.drop k) m p hp,
    vertex_eq_mul_vertex_one (w.drop k) (vertex v w k) p, vertex_drop_eq]

/-- The cut word ends where it started, after the closing edge. -/
theorem vertex_cutWord_last (v : G) (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ)
    (z : G) (hm : k + m ≤ w.length) :
    vertex (vertex v w k) (cutWord w lam k m z) (m + 1)
      = vertex v w (k + m) * z := by
  have hlen : ((w.drop k).take m).length = m := by
    have hdr : m ≤ (w.drop k).length := by
      rw [List.length_drop]
      omega
    exact List.length_take_of_le hdr
  show vertex (vertex v w k) ((w.drop k).take m ++ [RelLetter.comp lam z]) (m + 1)
      = vertex v w (k + m) * z
  rw [show m + 1 = ((w.drop k).take m).length + 1 from by omega,
    vertex_append_add ((w.drop k).take m) [RelLetter.comp lam z] (vertex v w k) 1]
  show vertex v w k * RelLetter.listVal ((w.drop k).take m) * z
      = vertex v w (k + m) * z
  rw [mul_listVal_take_drop]

/-- The cut word is closed, the closing letter being the difference of its two
ends. -/
theorem listVal_cutWord (v : G) (w : List (RelLetter G Λ)) (lam : Λ) (k m : ℕ) :
    RelLetter.listVal
        (cutWord w lam k m ((vertex v w (k + m))⁻¹ * vertex v w k)) = 1 := by
  show RelLetter.listVal ((w.drop k).take m ++
    [RelLetter.comp lam ((vertex v w (k + m))⁻¹ * vertex v w k)]) = 1
  rw [listVal_append, listVal_singleton]
  have h1 := mul_listVal_take_drop v w k m
  have h2 : RelLetter.listVal ((w.drop k).take m)
      = (vertex v w k)⁻¹ * vertex v w (k + m) := by
    rw [← h1, inv_mul_cancel_left]
  rw [h2]
  show (vertex v w k)⁻¹ * vertex v w (k + m) *
    ((vertex v w (k + m))⁻¹ * vertex v w k) = 1
  group

/-! ## 5.  The end-to-start form, at an innermost pair -/

/-- **Dahmani--Guirardel--Osin's Lemma 4.21, in the form the cut proves, at one
pair `(μ,b)`.**

The bound binder is asked at the SAME `(μ,b)` as the conclusion, and at `n ≤ 6`
sides: the cut of an `n`-gon is an `(n+1)`-gon, so a conclusion at `n ≤ 5` needs
the hypothesis at `n ≤ 6`.  Everything after that binder is proved outright.

The pair-specific form is what the base-case tower can supply --- its endpoint
is proved at one `(μ,b)` at a time --- and the proof only ever spends the bound
at its own pair.  `connector_mem_relBall` below is this with the binder asked at
every pair instead, for the consumers that hold it in that shape.

Given components `[i,k)` and `[i',k')` of a `(μ,b)`-quasi-geodesic `n`-gon with
the first connected to the second, and with no component start strictly between
them connected to the first, the element joining the END of the first to the
START of the second lies in `D.relBall lam (C * n)`.

The start-to-start element `(vertex v w i)⁻¹ * vertex v w i'` is *not* bounded:
see `not_connectedPairSpan_of_infinite`.  Nor can the innermost hypothesis be
dropped; the module docstring records the configuration that defeats it. -/
theorem connector_mem_relBall_at (D : RelGenSet G Λ) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b)
    (hbound : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 5 → ∀ (v : G) (w : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v w →
        ∀ (lam : Λ) (i k i' k' : ℕ), IsComp lam w i k → IsComp lam w i' k' →
          i < i' → Connected D.fam lam v w i i' →
          (∀ p : ℕ, i < p → p < i' → IsCompStart lam w p →
            ¬ Connected D.fam lam v w i p) →
          (vertex v w i')⁻¹ * vertex v w k ∈ D.relBall lam (C * n) := by
  obtain ⟨C, hC0, hCb⟩ := hbound
  refine ⟨2 * C, by omega, ?_⟩
  intro n hn v w hpoly lam i k i' k' hcomp hcomp' hii' hconn hinner
  obtain ⟨hlet, -, c, hc0, hcn, hcmono, hcqg⟩ := hpoly
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hnext := hcomp.2.2.2.2
  have hik' : i' < k' := hcomp'.1
  have hkw' : k' ≤ w.length := hcomp'.2.1
  have hrange' := hcomp'.2.2.1
  have hprev' := hcomp'.2.2.2.1
  -- a polygon with no letters has no components
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · exfalso
      rw [hn0, hc0] at hcn
      omega
    · exact hpos
  -- the second component starts strictly after the first ends: a component start
  -- inside `[i,k)` would have a `lam`-letter before it, and the letter at `k` is
  -- not a `lam`-letter while the letter at `i'` is
  have hki' : k < i' := by
    rcases Nat.lt_trichotomy i' k with hlt | heq | hgt
    · exact absurd (hrange (i' - 1) (by omega) (by omega) (by omega))
        (hprev' (i' - 1) (by omega) (by omega))
    · exfalso
      subst heq
      exact hnext (by omega) (hrange' _ le_rfl hik' (by omega))
    · exact hgt
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i' = k + m := ⟨i' - k, by omega⟩
  have hmw : k + m ≤ w.length := by omega
  -- the closing letter
  have hconn' : (vertex v w i)⁻¹ * vertex v w (k + m) ∈ D.fam lam := hconn
  have hspan : (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hcomp
  set z : G := (vertex v w (k + m))⁻¹ * vertex v w k with hz
  have hzfam : z ∈ D.fam lam := by
    have hrw : z = ((vertex v w i)⁻¹ * vertex v w (k + m))⁻¹ *
        ((vertex v w i)⁻¹ * vertex v w k) := by
      rw [hz]
      group
    rw [hrw]
    exact mul_mem (inv_mem hconn') hspan
  rcases eq_or_ne z 1 with hz1 | hz1
  · rw [hz1]
    exact one_mem_relBall D lam _
  -- the cut word, its length and its vertices
  have hPlen : (cutWord w lam k m z).length = m + 1 :=
    length_cutWord w lam k m z hmw
  have hvP : ∀ p : ℕ, p ≤ m →
      vertex (vertex v w k) (cutWord w lam k m z) p = vertex v w (k + p) :=
    fun p hp => vertex_cutWord v w lam k m z hmw p hp
  have hvPlast : vertex (vertex v w k) (cutWord w lam k m z) (m + 1)
      = vertex v w (k + m) * z := vertex_cutWord_last v w lam k m z hmw
  -- the cut word is a quasi-geodesic `(n+1)`-gon
  have hpolyP : IsQuasiGeodesicPolygon D mu b (n + 1) (vertex v w k)
      (cutWord w lam k m z) := by
    refine ⟨letters_cutWord D hlet lam k m hzfam, ?_,
      fun s => if s ≤ n then (if c s ≤ k + m then c s - k else m) else m + 1,
      ?_, ?_, ?_, ?_⟩
    · rw [hz]
      exact listVal_cutWord v w lam k m
    · show (if (0 : ℕ) ≤ n then (if c 0 ≤ k + m then c 0 - k else m) else m + 1) = 0
      rw [if_pos (Nat.zero_le n), hc0, if_pos (Nat.zero_le (k + m)), Nat.zero_sub]
    · show (if n + 1 ≤ n then (if c (n + 1) ≤ k + m then c (n + 1) - k else m)
        else m + 1) = (cutWord w lam k m z).length
      rw [hPlen, if_neg (show ¬ n + 1 ≤ n by omega)]
    · intro s
      show (if s ≤ n then (if c s ≤ k + m then c s - k else m) else m + 1)
          ≤ (if s + 1 ≤ n then (if c (s + 1) ≤ k + m then c (s + 1) - k else m)
              else m + 1)
      have hcs := hcmono s
      by_cases hs1 : s + 1 ≤ n
      · rw [if_pos (show s ≤ n by omega), if_pos hs1]
        by_cases h1 : c s ≤ k + m
        · rw [if_pos h1]
          by_cases h2 : c (s + 1) ≤ k + m
          · rw [if_pos h2]
            omega
          · rw [if_neg h2]
            omega
        · by_cases h2 : c (s + 1) ≤ k + m
          · exact absurd (le_trans hcs h2) h1
          · exact le_of_eq (by rw [if_neg h1, if_neg h2])
      · rw [if_neg hs1]
        by_cases hs : s ≤ n
        · rw [if_pos hs]
          by_cases h1 : c s ≤ k + m
          · rw [if_pos h1]
            omega
          · rw [if_neg h1]
            omega
        · exact le_of_eq (by rw [if_neg hs])
    · intro s hs p q hp hpq hq
      have hdeg : ∀ d : ℕ, ((0 : ℕ) : ℝ) / mu - b ≤ (d : ℝ) := by
        intro d
        have h1 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        rw [Nat.cast_zero, zero_div]
        linarith
      have hp' : (if s ≤ n then (if c s ≤ k + m then c s - k else m)
          else m + 1) ≤ p := hp
      have hq' : q ≤ (if s + 1 ≤ n then
          (if c (s + 1) ≤ k + m then c (s + 1) - k else m) else m + 1) := hq
      rcases Nat.lt_or_ge s n with hsn | hsn
      · -- an interior side, inside one side of `w`
        rw [if_pos (le_of_lt hsn)] at hp'
        rw [if_pos (show s + 1 ≤ n by omega)] at hq'
        rcases Nat.eq_or_lt_of_le hpq with heq | hlt
        · rw [heq, Nat.sub_self]
          exact hdeg _
        · -- read the two clipped endpoints without `if`, which omega does not split
          have hpA : c s ≤ k + p ∨ m ≤ p := by
            by_cases h1 : c s ≤ k + m
            · rw [if_pos h1] at hp'
              exact Or.inl (by omega)
            · rw [if_neg h1] at hp'
              exact Or.inr hp'
          have hqA : q ≤ m ∧ (k + q ≤ c (s + 1) ∨ q = 0) := by
            by_cases h2 : c (s + 1) ≤ k + m
            · rw [if_pos h2] at hq'
              refine ⟨by omega, ?_⟩
              by_cases h3 : k ≤ c (s + 1)
              · exact Or.inl (by omega)
              · exact Or.inr (by omega)
            · rw [if_neg h2] at hq'
              exact ⟨hq', Or.inl (by omega)⟩
          have hqm : q ≤ m := hqA.1
          have h1 : c s ≤ k + p := by
            rcases hpA with h | h
            · exact h
            · omega
          have h2 : k + q ≤ c (s + 1) := by
            rcases hqA.2 with h | h
            · exact h
            · omega
          have hkey := hcqg s hsn (k + p) (k + q) h1 (by omega) h2
          rw [show k + q - (k + p) = q - p from by omega] at hkey
          rw [hvP p (by omega), hvP q hqm]
          exact hkey
      · -- the closing edge
        have hsn' : s = n := by omega
        rw [hsn'] at hp' hq'
        rw [if_pos le_rfl] at hp'
        rw [if_neg (show ¬ n + 1 ≤ n by omega)] at hq'
        rcases Nat.eq_or_lt_of_le hpq with heq | hlt
        · rw [heq, Nat.sub_self]
          exact hdeg _
        · have hpm' : m ≤ p := by
            by_cases h1 : c n ≤ k + m
            · rw [if_pos h1] at hp'
              omega
            · rw [if_neg h1] at hp'
              exact hp'
          have hpm : p = m := by omega
          have hqm : q = p + 1 := by omega
          rw [hqm, hpm, show m + 1 - m = 1 from by omega, hvP m le_rfl, hvPlast]
          have hzge : 1 ≤ wordDist D.alphabet.carrier (vertex v w (k + m))
              (vertex v w (k + m) * z) := by
            show 1 ≤ wordNorm D.alphabet.carrier
              ((vertex v w (k + m))⁻¹ * (vertex v w (k + m) * z))
            rw [inv_mul_cancel_left]
            exact one_le_wordNorm D.alphabet.symmetricGenerating hz1
          have hzge' : (1 : ℝ) ≤ ((wordDist D.alphabet.carrier
              (vertex v w (k + m)) (vertex v w (k + m) * z) : ℕ) : ℝ) := by
            exact_mod_cast hzge
          have hmu1 : (1 : ℝ) / mu ≤ 1 := by
            rw [div_le_one (by linarith)]
            exact hmu
          rw [Nat.cast_one]
          linarith
  -- the closing edge is a component of the cut word
  have hcompP : IsComp lam (cutWord w lam k m z) m (m + 1) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj1 hj2 hjw
      rw [getElem_cutWord_last w lam k m z hmw j (by omega) hjw]
      exact rfl
    · intro j hj hjw hc
      rw [getElem_cutWord_lt w lam k m z hmw j hjw (by omega) (by omega)] at hc
      exact hprev' (k + j) (by omega) (by omega) hc
    · intro hk
      exact absurd hk (by omega)
  -- and it is isolated, by the innermost hypothesis
  have hisoP : IsIsolated D.fam lam (vertex v w k) (cutWord w lam k m z) m := by
    refine ⟨⟨m + 1, hcompP⟩, ?_⟩
    intro j hjm hjstart hcconn
    obtain ⟨j2, hj2⟩ := hjstart
    have hj12 : j < j2 := hj2.1
    have hj2P : j2 ≤ (cutWord w lam k m z).length := hj2.2.1
    have hjrange := hj2.2.2.1
    have hjprev := hj2.2.2.2.1
    have hjlt : j < m := by omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hpos
      · exfalso
        subst hj0
        have hp0 : (0 : ℕ) < (cutWord w lam k m z).length := by omega
        have hg := hjrange 0 le_rfl hj12 hp0
        rw [getElem_cutWord_lt w lam k m z hmw 0 hp0 (by omega) (by omega)] at hg
        exact hnext (by omega) hg
      · exact hpos
    -- the corresponding index of `w` starts a component of `w`
    have hpj : j < (cutWord w lam k m z).length := by omega
    have hcj : (w[k + j]'(by omega)).IsCompOf lam := by
      have hg := hjrange j le_rfl hj12 hpj
      rwa [getElem_cutWord_lt w lam k m z hmw j hpj (by omega) hjlt] at hg
    have hpj1 : j - 1 < (cutWord w lam k m z).length := by omega
    have hprevw : ¬ (w[k + (j - 1)]'(by omega)).IsCompOf lam := by
      have hg := hjprev (j - 1) (by omega) hpj1
      rwa [getElem_cutWord_lt w lam k m z hmw (j - 1) hpj1 (by omega) (by omega)] at hg
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (k + j) (by omega) hcj
    have hi₀ : i₀ = k + j := by
      by_contra hne
      exact hprevw (hcomp₀.2.2.1 (k + (j - 1)) (by omega) (by omega) (by omega))
    have hstartw : IsCompStart lam w (k + j) := by
      refine ⟨k₀, ?_⟩
      rw [← hi₀]
      exact hcomp₀
    -- connectedness in the cut word is connectedness in `w`
    have hcw : (vertex v w (k + m))⁻¹ * vertex v w (k + j) ∈ D.fam lam := by
      have hmem : (vertex (vertex v w k) (cutWord w lam k m z) m)⁻¹ *
          vertex (vertex v w k) (cutWord w lam k m z) j ∈ D.fam lam := hcconn
      rwa [hvP m le_rfl, hvP j (by omega)] at hmem
    have hcw' : Connected D.fam lam v w (k + m) (k + j) := hcw
    exact hinner (k + j) (by omega) (by omega) hstartw (connected_trans hconn hcw')
  -- the bound, applied to the cut word
  have happ := hCb (n + 1) (by omega) (vertex v w k) (cutWord w lam k m z)
    hpolyP lam m (m + 1) hcompP hisoP
  rw [hvP m le_rfl, hvPlast, inv_mul_cancel_left] at happ
  have hrad : C * (n + 1) ≤ 2 * C * n := by
    have h1 : n + 1 ≤ 2 * n := by omega
    calc C * (n + 1) ≤ C * (2 * n) := Nat.mul_le_mul le_rfl h1
      _ = 2 * C * n := by ring
  exact relBall_mono_radius D lam hrad happ

/-- **Lemma 4.21 with the bound asked at every `(μ,b)`.**

The shape the earlier consumers hold the isolated-component bound in.  It is
`connector_mem_relBall_at` with that binder applied at the one pair the proof
spends it on; the statement is unchanged, so no caller moves. -/
theorem connector_mem_relBall (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (mu b : ℝ) (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 5 → ∀ (v : G) (w : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v w →
        ∀ (lam : Λ) (i k i' k' : ℕ), IsComp lam w i k → IsComp lam w i' k' →
          i < i' → Connected D.fam lam v w i i' →
          (∀ p : ℕ, i < p → p < i' → IsCompStart lam w p →
            ¬ Connected D.fam lam v w i p) →
          (vertex v w i')⁻¹ * vertex v w k ∈ D.relBall lam (C * n) :=
  connector_mem_relBall_at D mu b hmu hb (hbound mu b hmu hb)

/-- **The connector in the other orientation**, for a base closed under inverses
--- which `OsinTheorem54SepSymmetric.exists_symmetric_base` supplies.  `d̂_lam` is
symmetric (`relBall_inv`), so the element from the start of the second component
back to the end of the first is bounded by the same constant. -/
theorem connector_inv_mem_relBall (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {N : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {p q : ℕ}
    (hmem : (vertex v w p)⁻¹ * vertex v w q ∈ D.relBall lam N) :
    (vertex v w q)⁻¹ * vertex v w p ∈ D.relBall lam N := by
  have hinv := relBall_inv D lam hsymm hmem
  rwa [mul_inv_rev, inv_inv] at hinv

end OsinComponents
end GGT
end GroupApproximation
