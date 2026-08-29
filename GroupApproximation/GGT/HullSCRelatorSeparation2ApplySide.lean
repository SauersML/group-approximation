import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNamed

/-!
# The two configuration clauses, from the two same-side exclusions

`GGT.OsinComponents.two_block_conj_named` carries two clauses about the
configuration: no component start between the matched pair is connected to the
`q`-component, and none in the other arc is connected to the `s`-component.
Together they say the `H_λ`-coset meets the quadrilateral in exactly the two
matched components, and that is what this module derives --- from the two
SAME-SIDE exclusions, one per long side, and nothing else.

The reduction is index bookkeeping and one group identity, done three times.

* `mem_fam_of_connected_side` --- connectedness between two positions of the
  `q`-block is the span of `q` between them lying in `H_λ`; the short first side
  translates both endpoints and cancels.
* `mem_fam_of_connected_revSide` --- the same on the reversed side, where the
  closing relation is what turns a four-gon vertex back into a vertex of `s`.
* `mem_fam_of_connected_cross` --- the mixed one, which is the match itself.

The group identity is that two elements of `H_λ` with a common left factor have
a quotient in `H_λ`, which is how a component connected to one of the matched
pair becomes a component connected to the other on ITS OWN side, where the
same-side exclusion can see it.

## What is NOT here

The same-side exclusions themselves.  `not_connected_qBlock_of_isComp` proves
one of them for a GEODESIC side, by reading `distance ≤ 1` off as
`|i - i'| ≤ 1`.  The sides here are only quasi-geodesic, so that step gives
`i' - i ≤ 1 + b` (`HullSC.index_close_of_connected`) rather than `≤ 1`, and the
exclusion at that range is the design's, not the geometry's.  Both exclusions
are therefore hypotheses, in the shape the design's window clause meets.

There is no reversed-side analogue of `not_connected_qBlock_of_isComp` in the
tree, and on this reading none is wanted: `index_close_of_connected` is stated
over an arbitrary side, so one geometric statement covers both, and what differs
between the sides is only the index arithmetic, which is what the three
translation lemmas above absorb.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Positions of the reversed side -/

/-- **A position in the reversed block, named by its index in `s`.**  The block
is read backwards, so a position `o` past the third corner is
`|p| + |q| + |r| + (|s| - m)` for exactly one `m`, and `m` is positive because
`o` is past the corner rather than at the far end. -/
theorem exists_rev_index (P Q R S : ℕ) {o : ℕ} (h1 : P + Q + R ≤ o)
    (h2 : o < P + Q + R + S) :
    ∃ m : ℕ, m ≤ S ∧ 0 < m ∧ o = P + Q + R + (S - m) :=
  ⟨S - (o - (P + Q + R)), by omega, by omega, by omega⟩

/-! ## Connectedness, read on the side it happens on -/

/-- **Connectedness inside the `q`-block is a span of `q`.** -/
theorem mem_fam_of_connected_side (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ)) {i i' : ℕ} (hi : i ≤ q.length)
    (hi' : i' ≤ q.length)
    (hconn : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + i')) :
    (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∈ D.fam lam := by
  have h : (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i') ∈ D.fam lam :=
    hconn
  rw [vertex_fourGon_side p q r s 1 hi, vertex_fourGon_side p q r s 1 hi',
    one_mul] at h
  have hid : (RelLetter.listVal p * vertex (1 : G) q i)⁻¹ *
      (RelLetter.listVal p * vertex (1 : G) q i')
      = (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' := by
    group
  rwa [hid] at h

/-- **Connectedness inside the reversed block is a span of `s`.** -/
theorem mem_fam_of_connected_revSide (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (j m : ℕ)
    (hconn : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - j))
      (p.length + q.length + r.length + (s.length - m))) :
    (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s m ∈ D.fam lam := by
  have h : (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j)))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - m)) ∈ D.fam lam := hconn
  rwa [vertex_fourGon_opposite_closed p q r s hclose j,
    vertex_fourGon_opposite_closed p q r s hclose m] at h

/-- **Connectedness across the two long sides**, which is the match. -/
theorem mem_fam_of_connected_cross (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    {i : ℕ} (hi : i ≤ q.length) (m : ℕ)
    (hconn : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - m))) :
    (RelLetter.listVal p * vertex (1 : G) q i)⁻¹ * vertex (1 : G) s m
      ∈ D.fam lam := by
  have h : (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - m)) ∈ D.fam lam := hconn
  rwa [vertex_fourGon_side p q r s 1 hi, one_mul,
    vertex_fourGon_opposite_closed p q r s hclose m] at h

/-- **Two elements of `H_λ` with a common left factor have their quotient in
`H_λ`.**  This is how a component connected to one of the matched pair becomes a
component connected to the other on its own side. -/
theorem mem_fam_of_common_left {H : Λ → Subgroup G} {lam : Λ} {A X Y : G}
    (hA : A⁻¹ * X ∈ H lam) (hB : A⁻¹ * Y ∈ H lam) : X⁻¹ * Y ∈ H lam := by
  have h := mul_mem (inv_mem hA) hB
  have hid : (A⁻¹ * X)⁻¹ * (A⁻¹ * Y) = X⁻¹ * Y := by group
  rwa [hid] at h

/-- **Two components matched to the same target are connected to each other.**
The common right factor cancels and so does the short side, which is what turns
a second match on one side into a same-side connection there. -/
theorem mem_fam_of_match_pair {H : Λ → Subgroup G} {lam : Λ} {A U V Z : G}
    (hA : (A * U)⁻¹ * Z ∈ H lam) (hB : (A * V)⁻¹ * Z ∈ H lam) :
    U⁻¹ * V ∈ H lam := by
  have h := mul_mem hA (inv_mem hB)
  have hid : ((A * U)⁻¹ * Z) * ((A * V)⁻¹ * Z)⁻¹ = U⁻¹ * V := by group
  rwa [hid] at h

/-! ## The two clauses -/

section Clauses

variable (D : RelGenSet G Λ) (lam : Λ) (p q r s : List (RelLetter G Λ))

/-- **The innermost clause, from the two same-side exclusions.**

The range splits into three: positions of `q` after the matched one, where the
`q`-side exclusion applies; positions of `r`, which is base-spelled and carries
no component start; and positions of the reversed block before the matched
component's far end, where the match turns the connection into one between two
components of `s` and the `s`-side exclusion applies. -/
theorem innermost_of_sideExclusions
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {i l : ℕ}
    (hi : i ≤ q.length) (hl : l ≤ s.length)
    (hmatch : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - l)))
    (hqside : ∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam)
    (hsside : ∀ m : ℕ, m ≤ s.length → m ≠ l →
      (vertex (1 : G) s l)⁻¹ * vertex (1 : G) s m ∉ D.fam lam) :
    ∀ t : ℕ, p.length + i < t →
      t < p.length + q.length + r.length + (s.length - l) →
      IsCompStart lam (p ++ q ++ r ++ revWord s) t →
      ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i) t := by
  intro t ht1 ht2 hstart hconnt
  rcases Nat.lt_or_ge t (p.length + q.length) with hA | hAge
  · refine hqside (t - p.length) (by omega) (by omega) ?_
    refine mem_fam_of_connected_side D lam p q r s hi (by omega) ?_
    have hteq : t = p.length + (t - p.length) := by omega
    rw [← hteq]
    exact hconnt
  · rcases Nat.lt_or_ge t (p.length + q.length + r.length) with hB | hBge
    · exact not_isCompStart_fourGon_r p q r s lam hr hAge hB hstart
    · obtain ⟨m, hm, -, hteq⟩ :=
        exists_rev_index p.length q.length r.length s.length hBge (by omega)
      refine hsside m hm (by omega) ?_
      refine mem_fam_of_common_left
        (A := RelLetter.listVal p * vertex (1 : G) q i)
        (mem_fam_of_connected_cross D lam p q r s hclose hi l hmatch) ?_
      refine mem_fam_of_connected_cross D lam p q r s hclose hi m ?_
      rw [← hteq]
      exact hconnt

/-- **The other-arc clause, from the two same-side exclusions.**

The first range is the rest of the reversed block, where the `s`-side exclusion
applies directly; the second is the base-spelled first side, which carries no
component start, together with the positions of `q` before the matched one,
where the match turns the connection into one between two components of `q`. -/
theorem otherArc_of_sideExclusions
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {i l : ℕ}
    (hi : i ≤ q.length) (hl : l ≤ s.length)
    (hmatch : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - l)))
    (hqside : ∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam)
    (hsside : ∀ m : ℕ, m ≤ s.length → m ≠ l →
      (vertex (1 : G) s l)⁻¹ * vertex (1 : G) s m ∉ D.fam lam) :
    ∀ o : ℕ,
      (p.length + q.length + r.length + (s.length - l) < o
          ∧ o < (p ++ q ++ r ++ revWord s).length)
        ∨ o < p.length + i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) o →
      ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - l)) o := by
  intro o ho hstart hconno
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  rcases ho with ⟨hb1, hb2⟩ | hb3
  · rw [hlen] at hb2
    obtain ⟨m, hm, -, hoeq⟩ :=
      exists_rev_index p.length q.length r.length s.length (by omega) hb2
    refine hsside m hm (by omega) ?_
    refine mem_fam_of_connected_revSide D lam p q r s hclose l m ?_
    rw [← hoeq]
    exact hconno
  · rcases Nat.lt_or_ge o p.length with hbase | hqpart
    · exact not_isCompStart_fourGon_p p q r s lam hp hbase hstart
    · have hoeq : o = p.length + (o - p.length) := by omega
      have h2 : (RelLetter.listVal p * vertex (1 : G) q (o - p.length))⁻¹ *
          vertex (1 : G) s l ∈ D.fam lam := by
        refine mem_fam_of_connected_cross D lam p q r s hclose (by omega) l ?_
        rw [← hoeq]
        exact connected_symm hconno
      have h1 : (RelLetter.listVal p * vertex (1 : G) q i)⁻¹ *
          vertex (1 : G) s l ∈ D.fam lam :=
        mem_fam_of_connected_cross D lam p q r s hclose hi l hmatch
      exact hqside (o - p.length) (by omega) (by omega)
        (mem_fam_of_match_pair h1 h2)

end Clauses

end OsinComponents
end GGT
end GroupApproximation
