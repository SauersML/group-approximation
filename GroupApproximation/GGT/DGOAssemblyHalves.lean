import GroupApproximation.GGT.DGOPolygonCutFamily
import GroupApproximation.GGT.DGOIsolatedComponentRotate
import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.GGT.DGOIsolatedComponentBridge

/-!
# The two halves of a cut between named word vertices

The first step of Dahmani--Guirardel--Osin's proof of Proposition 4.14: the
balanced cut divides the polygon into two closed paths.  This module is the
corner primitive used after `DGOAssemblyCuts.splitPairCut` has inserted the two
selected graph vertices as corners of the refined polygon.  It builds the two
paths as words and proves the three things every later step needs of them ---
their letters are admissible, they spell the identity, and their lengths are
what the side count says.

## Corner to corner, and what that saves

DGO's cut lands at graph vertices `u ∈ p_α` and `v ∈ p_β` in two sides.
`splitPairCut` performs the splittings once at the cut-function layer, paying
one added side at each endpoint.  This module then sees `u` and `v` as ordinary
corners, so the halves are whole refined sides plus the chord and none of the
interior-point bookkeeping is duplicated here.

    firstHalf  = (the arc from corner a to corner b) ++ (the chord, reversed)
    secondHalf = (the arc from corner b round to corner a) ++ (the chord)

The second half wraps past the end of the word, which is why it is `w.drop (c b)
++ w.take (c a)` rather than a single interval: the polygon is a cycle and the
word is not.

## Where closure is spent

`firstHalf` closes on the chord's defining equation alone.  `secondHalf` also
needs `listVal w = 1`, and that is the only place it is used here: it is what
turns `listVal (w.drop (c b))` into `(vertex v w (c b))⁻¹ * v`, i.e. what lets
the suffix return to the basepoint.  The asymmetry is real and not an artefact
of how the two are written.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The three words -/

/-- **The arc of the polygon from corner `a` to corner `b`.** -/
def arcWord (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (a b : ℕ) : List (RelLetter G Λ) :=
  (w.drop (c a)).take (c b - c a)

/-- **The first half**: the arc from corner `a` to corner `b`, closed by the
chord read backwards. -/
def firstHalf (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (a b : ℕ)
    (t : List (RelLetter G Λ)) : List (RelLetter G Λ) :=
  arcWord w c a b ++ revWord t

/-- **The second half**: the arc from corner `b` round the end of the word to
corner `a`, closed by the chord. -/
def secondHalf (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (a b : ℕ)
    (t : List (RelLetter G Λ)) : List (RelLetter G Λ) :=
  w.drop (c b) ++ w.take (c a) ++ t

omit [Group G] in
/-- **The wrapped arc of the second half is a prefix of a rotation.**

This identity lets the mature cyclic component-transport API for `rotWord`
handle both pieces of the wrapped arc at once.  In particular, the seam between
`w.drop (c b)` and `w.take (c a)` is no longer special bookkeeping in the
component-surgery layer. -/
theorem secondHalf_eq_rotWord_append (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b : ℕ} (ha : c a ≤ c b) (_hb : c b ≤ w.length)
    (t : List (RelLetter G Λ)) :
    secondHalf w c a b t =
      (rotWord w (c b)).take ((w.length - c b) + c a) ++ t := by
  have hdrop : (w.drop (c b)).length = w.length - c b := by
    rw [List.length_drop]
  have htake : (w.take (c b)).take (c a) = w.take (c a) := by
    rw [List.take_take]
    congr 1
    omega
  -- the rewrite must be ANCHORED: an unqualified `take_of_length_le` matches
  -- `w.take (c a)` on the left first and asks for `w.length ≤ c a`, which is
  -- false.  Naming the instance pins it to the `drop` on the right.
  have hle : (List.drop (c b) w).length ≤ w.length - c b + c a := by
    rw [hdrop]
    omega
  have hfull : List.take (w.length - c b + c a) (List.drop (c b) w)
      = List.drop (c b) w := List.take_of_length_le hle
  have hidx : w.length - c b + c a - (w.length - c b) = c a := by omega
  show w.drop (c b) ++ w.take (c a) ++ t =
    ((w.drop (c b) ++ w.take (c b)).take ((w.length - c b) + c a)) ++ t
  rw [List.take_append, hdrop, hfull, hidx, htake]

/-! ## What the arc spells -/

/-- **The arc spells the displacement between its two corners.** -/
theorem listVal_arcWord (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b : ℕ}
    (hab : c a ≤ c b) :
    RelLetter.listVal (arcWord w c a b)
      = (vertex v w (c a))⁻¹ * vertex v w (c b) := by
  have hkey := vertex_drop_eq w v (c a) (c b - c a)
  have harg : c a + (c b - c a) = c b := by omega
  rw [harg] at hkey
  have hv1 : vertex (1 : G) (w.drop (c a)) (c b - c a)
      = RelLetter.listVal ((w.drop (c a)).take (c b - c a)) := by
    rw [vertex_eq_mul_listVal_take, one_mul]
  rw [hv1] at hkey
  show RelLetter.listVal ((w.drop (c a)).take (c b - c a))
    = (vertex v w (c a))⁻¹ * vertex v w (c b)
  calc RelLetter.listVal ((w.drop (c a)).take (c b - c a))
      = (vertex v w (c a))⁻¹
        * (vertex v w (c a) * RelLetter.listVal ((w.drop (c a)).take (c b - c a))) := by
        rw [inv_mul_cancel_left]
    _ = (vertex v w (c a))⁻¹ * vertex v w (c b) := by rw [hkey]

/-- **The suffix past a corner returns to the basepoint.**  The one use of
closedness in this module. -/
theorem listVal_drop_of_closed (w : List (RelLetter G Λ)) (v : G) {k : ℕ}
    (hk : k ≤ w.length) (hcl : RelLetter.listVal w = 1) :
    RelLetter.listVal (w.drop k) = (vertex v w k)⁻¹ * v := by
  have hkey := vertex_drop_eq w v k (w.length - k)
  have harg : k + (w.length - k) = w.length := by omega
  rw [harg] at hkey
  have hend : vertex v w w.length = v := by
    rw [vertex_eq_mul_listVal_take, List.take_length, hcl, mul_one]
  rw [hend] at hkey
  have hv1 : vertex (1 : G) (w.drop k) (w.length - k) = RelLetter.listVal (w.drop k) := by
    have hlen : w.length - k = (w.drop k).length := by
      rw [List.length_drop]
    rw [hlen, vertex_eq_mul_listVal_take, List.take_length, one_mul]
  rw [hv1] at hkey
  calc RelLetter.listVal (w.drop k)
      = (vertex v w k)⁻¹ * (vertex v w k * RelLetter.listVal (w.drop k)) := by
        rw [inv_mul_cancel_left]
    _ = (vertex v w k)⁻¹ * v := by rw [hkey]

/-- **The prefix up to a corner spells the way there.** -/
theorem listVal_take_eq (w : List (RelLetter G Λ)) (v : G) (k : ℕ) :
    RelLetter.listVal (w.take k) = v⁻¹ * vertex v w k := by
  rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]

/-! ## The halves are closed -/

/-- **The first half spells the identity.** -/
theorem listVal_firstHalf (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b : ℕ}
    (hab : c a ≤ c b) {t : List (RelLetter G Λ)}
    (ht : RelLetter.listVal t = (vertex v w (c a))⁻¹ * vertex v w (c b)) :
    RelLetter.listVal (firstHalf w c a b t) = 1 := by
  show RelLetter.listVal (arcWord w c a b ++ revWord t) = 1
  rw [listVal_append, listVal_arcWord w v c hab, listVal_revWord, ht]
  group

/-- **The second half spells the identity.** -/
theorem listVal_secondHalf (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b : ℕ}
    (hb : c b ≤ w.length) (hcl : RelLetter.listVal w = 1)
    {t : List (RelLetter G Λ)}
    (ht : RelLetter.listVal t = (vertex v w (c a))⁻¹ * vertex v w (c b)) :
    RelLetter.listVal (secondHalf w c a b t) = 1 := by
  show RelLetter.listVal (w.drop (c b) ++ w.take (c a) ++ t) = 1
  rw [listVal_append, listVal_append, listVal_drop_of_closed w v hb hcl,
    listVal_take_eq w v (c a), ht]
  group

/-! ## The halves are admissible -/

/-- **Every letter of the first half is admissible.** -/
theorem isLetter_firstHalf (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {w : List (RelLetter G Λ)}
    (hlet : ∀ x ∈ w, D.IsLetter x) {t : List (RelLetter G Λ)}
    (htlet : ∀ x ∈ t, D.IsLetter x) (c : ℕ → ℕ) (a b : ℕ) :
    ∀ x ∈ firstHalf w c a b t, D.IsLetter x := by
  intro x hx
  rcases List.mem_append.mp hx with harc | hrev
  · exact hlet x (List.mem_of_mem_drop (List.mem_of_mem_take harc))
  · exact isLetter_of_mem_revWord D hsymm htlet x hrev

/-- **Every letter of the second half is admissible.** -/
theorem isLetter_secondHalf (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ x ∈ w, D.IsLetter x) {t : List (RelLetter G Λ)}
    (htlet : ∀ x ∈ t, D.IsLetter x) (c : ℕ → ℕ) (a b : ℕ) :
    ∀ x ∈ secondHalf w c a b t, D.IsLetter x := by
  intro x hx
  rcases List.mem_append.mp hx with hpre | htail
  · rcases List.mem_append.mp hpre with hdrop | htake
    · exact hlet x (List.mem_of_mem_drop hdrop)
    · exact hlet x (List.mem_of_mem_take htake)
  · exact htlet x htail

/-! ## The lengths, which are the side counts -/

/-- **Reversal preserves length.** -/
theorem length_revWord (t : List (RelLetter G Λ)) : (revWord t).length = t.length := by
  show ((t.map invLetter).reverse).length = t.length
  rw [List.length_reverse, List.length_map]

omit [Group G] in
/-- **The arc has as many letters as the corners are apart.** -/
theorem length_arcWord (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b : ℕ}
    (hb : c b ≤ w.length) : (arcWord w c a b).length = c b - c a := by
  show ((w.drop (c a)).take (c b - c a)).length = c b - c a
  rw [List.length_take, List.length_drop]
  omega

/-- **The first half's length.** -/
theorem length_firstHalf (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b : ℕ}
    (hb : c b ≤ w.length) (t : List (RelLetter G Λ)) :
    (firstHalf w c a b t).length = (c b - c a) + t.length := by
  show (arcWord w c a b ++ revWord t).length = (c b - c a) + t.length
  rw [List.length_append, length_arcWord w c hb, length_revWord]

omit [Group G] in
/-- **The second half's length.**  The two arcs plus the chord; together with the
first half this is `w.length + 2 * t.length`, which is the `Σ n_j ≤ n + C log n`
clause of the subdivision recursion in miniature. -/
theorem length_secondHalf (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b : ℕ}
    (ha : c a ≤ w.length) (t : List (RelLetter G Λ)) :
    (secondHalf w c a b t).length = (w.length - c b) + c a + t.length := by
  show (w.drop (c b) ++ w.take (c a) ++ t).length = (w.length - c b) + c a + t.length
  rw [List.length_append, List.length_append, List.length_drop, List.length_take]
  omega

/-- **The two halves together carry the whole word twice over the chord.** -/
theorem length_firstHalf_add_secondHalf (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b : ℕ} (hab : c a ≤ c b) (hb : c b ≤ w.length) (t : List (RelLetter G Λ)) :
    (firstHalf w c a b t).length + (secondHalf w c a b t).length
      = w.length + 2 * t.length := by
  rw [length_firstHalf w c hb, length_secondHalf w c (by omega)]
  omega

end DGOPolygonCut
end GGT
end GroupApproximation
