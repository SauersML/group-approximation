import GroupApproximation.GGT.DGOAssemblyCuts

/-!
# The vertices of the halves are the vertices of the polygon

Everything the assembly says about the two halves of the cut has eventually to
be said back at the original polygon: a component of a half is a component of
the polygon, and connectedness in a half is connectedness in the polygon.  Both
reduce to one fact, proved here --- along the arc, the vertex map of a half
**is** the vertex map of the polygon, shifted by the corner.

    vertex (vertex v w (c a)) (firstHalf w c a b t) k = vertex v w (c a + k)

That is what makes the transfer free rather than an induction: `Connected` is
defined from vertices alone, so once the vertex maps agree the two
connectedness relations are the same proposition with different names.

## Why the hypotheses are index bounds and nothing else

The arc of the first half is `(w.drop (c a)).take (c b − c a)`, and reading `k`
letters of it touches only the first `k`, so the `take` is invisible for
`k ≤ c b − c a` and the `drop` is a shift.  Neither step needs the word to be
closed, admissible, or geodesic; the only hypotheses are that `k` has not run
past the arc.  The same holds for the second half along its own arc, which
starts at corner `b` and runs to the end of the word.

Past the arc the statement is false and no version of it is wanted: those
indices are on the chord, where the half is not following the polygon at all.
Isolation arguments therefore split into an arc part, handled by transfer, and a
chord part, handled by the break --- and that split is exactly
Dahmani--Guirardel--Osin's, where a distinguished component fails to be isolated
in a half only by being connected to a component of the chord.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Two elementary displacements -/

/-- **A prefix is invisible below its length.** -/
theorem vertex_take (v : G) (u : List (RelLetter G Λ)) {k m : ℕ} (hk : k ≤ m) :
    vertex v (u.take m) k = vertex v u k := by
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take, List.take_take]
  have hmin : min k m = k := by omega
  rw [hmin]

/-- **A concatenation is invisible below the length of its first factor.** -/
theorem vertex_append_left (v : G) (u z : List (RelLetter G Λ)) {k : ℕ}
    (hk : k ≤ u.length) : vertex v (u ++ z) k = vertex v u k := by
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take,
    List.take_append_of_le_length hk]

/-- **A suffix read from the vertex it starts at is the polygon, shifted.** -/
theorem vertex_drop_from (w : List (RelLetter G Λ)) (v : G) (m k : ℕ) :
    vertex (vertex v w m) (w.drop m) k = vertex v w (m + k) := by
  have hsmul := vertex_smul (vertex v w m) (1 : G) (w.drop m) k
  rw [mul_one] at hsmul
  rw [hsmul]
  exact vertex_drop_eq w v m k

/-! ## The arc of the first half -/

/-- **Vertices of the arc are vertices of the polygon, shifted by the corner.** -/
theorem vertex_arcWord (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ)
    {a b k : ℕ} (hk : k ≤ c b - c a) :
    vertex (vertex v w (c a)) (arcWord w c a b) k = vertex v w (c a + k) := by
  show vertex (vertex v w (c a)) ((w.drop (c a)).take (c b - c a)) k
    = vertex v w (c a + k)
  rw [vertex_take _ _ hk]
  exact vertex_drop_from w v (c a) k

/-- **Vertices of the first half, along its arc.** -/
theorem vertex_firstHalf (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ)
    {a b k : ℕ} (hk : k ≤ c b - c a) (hb : c b ≤ w.length)
    (t : List (RelLetter G Λ)) :
    vertex (vertex v w (c a)) (firstHalf w c a b t) k = vertex v w (c a + k) := by
  show vertex (vertex v w (c a)) (arcWord w c a b ++ revWord t) k
    = vertex v w (c a + k)
  have hlen : k ≤ (arcWord w c a b).length := by
    rw [length_arcWord w c hb]
    exact hk
  rw [vertex_append_left _ _ _ hlen]
  exact vertex_arcWord w v c hk

/-- **Vertices of the second half, along its arc**, which starts at corner `b`
and runs to the end of the word. -/
theorem vertex_secondHalf (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ)
    {a b k : ℕ} (hk : k ≤ w.length - c b) (t : List (RelLetter G Λ)) :
    vertex (vertex v w (c b)) (secondHalf w c a b t) k = vertex v w (c b + k) := by
  show vertex (vertex v w (c b)) (w.drop (c b) ++ w.take (c a) ++ t) k
    = vertex v w (c b + k)
  have hlen : k ≤ (w.drop (c b)).length := by
    rw [List.length_drop]
    exact hk
  have hlen' : k ≤ (w.drop (c b) ++ w.take (c a)).length := by
    rw [List.length_append]
    omega
  rw [vertex_append_left _ _ _ hlen', vertex_append_left _ _ _ hlen]
  exact vertex_drop_from w v (c b) k

/-- **Every vertex of the wrapped second-half arc is a vertex of the rotated
polygon.**  Unlike `vertex_secondHalf`, this covers both the suffix after `b`
and the prefix before `a`, including pairs that cross the word seam. -/
theorem vertex_secondHalf_rotWord (w : List (RelLetter G Λ)) (v : G)
    (c : ℕ → ℕ) {a b k : ℕ} (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hk : k ≤ (w.length - c b) + c a) (t : List (RelLetter G Λ)) :
    vertex (vertex v w (c b)) (secondHalf w c a b t) k =
      vertex (vertex v w (c b)) (rotWord w (c b)) k := by
  rw [secondHalf_eq_rotWord_append w c ha hb t]
  have hrot : (rotWord w (c b)).length = w.length := length_rotWord w hb
  have hprefix : ((rotWord w (c b)).take ((w.length - c b) + c a)).length =
      (w.length - c b) + c a := by
    rw [List.length_take, hrot]
    omega
  rw [vertex_append_left _ _ _ (by rw [hprefix]; exact hk)]
  exact vertex_take _ _ hk

/-! ## Connectedness transfers -/

/-- **Connectedness in the first half is connectedness in the polygon.**

`Connected` is defined from vertices alone, so this is the vertex dictionary
read twice and nothing more. -/
theorem connected_firstHalf_iff (H : Λ → Subgroup G) (lam : Λ)
    (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b i j : ℕ}
    (hi : i ≤ c b - c a) (hj : j ≤ c b - c a) (hb : c b ≤ w.length)
    (t : List (RelLetter G Λ)) :
    Connected H lam (vertex v w (c a)) (firstHalf w c a b t) i j
      ↔ Connected H lam v w (c a + i) (c a + j) := by
  show (vertex (vertex v w (c a)) (firstHalf w c a b t) i)⁻¹
      * vertex (vertex v w (c a)) (firstHalf w c a b t) j ∈ H lam
    ↔ (vertex v w (c a + i))⁻¹ * vertex v w (c a + j) ∈ H lam
  rw [vertex_firstHalf w v c hi hb t, vertex_firstHalf w v c hj hb t]

/-- **Connectedness in the second half is connectedness in the polygon.** -/
theorem connected_secondHalf_iff (H : Λ → Subgroup G) (lam : Λ)
    (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b i j : ℕ}
    (hi : i ≤ w.length - c b) (hj : j ≤ w.length - c b)
    (t : List (RelLetter G Λ)) :
    Connected H lam (vertex v w (c b)) (secondHalf w c a b t) i j
      ↔ Connected H lam v w (c b + i) (c b + j) := by
  show (vertex (vertex v w (c b)) (secondHalf w c a b t) i)⁻¹
      * vertex (vertex v w (c b)) (secondHalf w c a b t) j ∈ H lam
    ↔ (vertex v w (c b + i))⁻¹ * vertex v w (c b + j) ∈ H lam
  rw [vertex_secondHalf w v c hi t, vertex_secondHalf w v c hj t]

/-- **Connectedness anywhere on the wrapped second-half arc is connectedness
in the rotated polygon.** -/
theorem connected_secondHalf_rotWord_iff (H : Λ → Subgroup G) (lam : Λ)
    (w : List (RelLetter G Λ)) (v : G) (c : ℕ → ℕ) {a b i j : ℕ}
    (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i ≤ (w.length - c b) + c a)
    (hj : j ≤ (w.length - c b) + c a)
    (t : List (RelLetter G Λ)) :
    Connected H lam (vertex v w (c b)) (secondHalf w c a b t) i j ↔
      Connected H lam (vertex v w (c b)) (rotWord w (c b)) i j := by
  show (vertex (vertex v w (c b)) (secondHalf w c a b t) i)⁻¹ *
      vertex (vertex v w (c b)) (secondHalf w c a b t) j ∈ H lam ↔ _
  rw [vertex_secondHalf_rotWord w v c ha hb hi t,
    vertex_secondHalf_rotWord w v c ha hb hj t]

end DGOPolygonCut
end GGT
end GroupApproximation
