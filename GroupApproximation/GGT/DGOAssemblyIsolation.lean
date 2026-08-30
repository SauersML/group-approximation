import GroupApproximation.GGT.DGOAssemblyLetters

/-!
# A distinguished component stays isolated in its half

The step that makes the break necessary, and says exactly how much of it is
necessary.  A distinguished component of the polygon lying in the arc of a half
is still an isolated component *of that half* --- **unless** it is connected to a
component start lying on the chord.  So the only obstruction the cut can create
is the chord, which is what Dahmani--Guirardel--Osin's algorithm then breaks at.

## The two regions, and why only one of them is work

A component start of a half lies either along the arc or on the chord.  On the
chord it is excluded by hypothesis --- that hypothesis is the break's job, not
this lemma's.  Along the arc, `connected_firstHalf_iff` turns connectedness in
the half into connectedness in the polygon, and isolation in the polygon
forbids it.

## The one subtlety: an arc component start need not be a polygon component start

A run of the polygon that the corner cuts in half starts a *new* component in
the arc, because its predecessor letter is outside the arc.  At every-edge-a-side
every index is a corner, so this is the common case rather than an edge case, and
it is why the proof does not simply transfer `IsCompStart` across.

It does not need to.  What transfers is the *letter*: position `j` of the arc
carries a `lam`-letter, so position `c a + j` of the polygon does too, hence lies
in some component of the polygon (`exists_isComp_of_isCompOf`) whose start `p` is
connected to it (`span_mem_fam`).  Isolation of the distinguished component then
forbids the connection to `p`, one transitivity step removed --- unless `p` is the
distinguished component itself, and then single-edgeness pins `j = i` against
`j ≠ i`.  That last case is where the `SumBound` single-edge clause is spent
inside the assembly rather than at its boundary.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Along the arc, nothing else is connected to a distinguished component.**

The arc half of isolation, extracted because two consumers need exactly this and
neither needs the chord hypothesis: `isIsolated_firstHalf` adds the chord case,
and `chord_partner_unique` uses this one at `j := i'` to show two distinguished
components cannot share a chord partner. -/
theorem not_connected_firstHalf_arc (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i j : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length) (hi : i < c b - c a)
    (hjarc : j < c b - c a) (hne : j ≠ i)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i)) (t : List (RelLetter G Λ))
    (hjstart : IsCompStart lam (firstHalf w c a b t) j) :
    ¬ Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i j := by
  intro hconn
  -- transfer the connection back to the polygon
  have hconnw : Connected D.fam lam v w (c a + i) (c a + j) :=
    (connected_firstHalf_iff D.fam lam w v c (le_of_lt hi) (le_of_lt hjarc) hb t).mp
      hconn
  -- position `j` of the half carries a `lam`-letter, so position `c a + j` does
  obtain ⟨kj, hkj⟩ := hjstart
  obtain ⟨hjk, hkw, hrun, -, -⟩ := hkj
  have hjlen : j < (firstHalf w c a b t).length := by omega
  have hcoHalf : ((firstHalf w c a b t)[j]'hjlen).IsCompOf lam :=
    hrun j (le_refl j) hjk hjlen
  have hjw : c a + j < w.length := by omega
  have hcoW : (w[c a + j]'hjw).IsCompOf lam :=
    (isCompOf_firstHalf_arc_iff lam w c hb hjarc t hjlen).mp hcoHalf
  -- so it lies in a component of the polygon
  obtain ⟨p, k, hpj, hjk', hpcomp⟩ :=
    exists_isComp_of_isCompOf lam w (c a + j) hjw hcoW
  -- whose start is connected to it
  have hpconn : Connected D.fam lam v w p (c a + j) := by
    obtain ⟨-, hkw', hrun', -, -⟩ := hpcomp
    exact span_mem_fam D lam v hlet (c a + j) (le_of_lt hjw) p hpj
      (fun m hm1 hm2 hm3 => hrun' m hm1 (by omega) hm3)
  have hip : Connected D.fam lam v w (c a + i) p :=
    connected_trans hconnw (connected_symm hpconn)
  rcases eq_or_ne p (c a + i) with hpi | hpi
  · -- the component is the distinguished one, and it is a single edge
    subst hpi
    have hkeq : k = c a + i + 1 := isComp_end_unique hpcomp hcomp
    exact hne (by omega)
  · exact hiso.2 p hpi ⟨k, hpcomp⟩ hip

/-- **A distinguished component of the polygon is isolated in the first half,
once the chord is ruled out.** -/
theorem isIsolated_firstHalf (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length) (hi : i < c b - c a)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i)) (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (firstHalf w c a b t) i)
    (hchord : ∀ j : ℕ, c b - c a ≤ j →
      IsCompStart lam (firstHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i j) :
    IsIsolated D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i := by
  refine ⟨hstart, ?_⟩
  intro j hne hjstart hconn
  rcases Nat.lt_or_ge j (c b - c a) with hjarc | hjchord
  · exact not_connected_firstHalf_arc D lam v w c hlet hb hi hjarc hne hcomp hiso t
      hjstart hconn
  · exact hchord j hjchord hjstart hconn

/-- **Two distinguished components cannot share a chord partner.**

The bound on how many breaks the arc needs: the map sending a distinguished
component to the chord component it is connected to is injective, so there are
at most `ℓ(t)` breaks in each half.  That is where `k ≤ 2ℓ(t) + 2` comes from,
and it is the reason the number of pieces is logarithmic rather than linear.

The proof is one transitivity step: if both were connected to `q` they would be
connected to each other, which `not_connected_firstHalf_arc` forbids. -/
theorem chord_partner_unique (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i i' q : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length) (hi : i < c b - c a)
    (hi' : i' < c b - c a) (hne : i' ≠ i)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i)) (t : List (RelLetter G Λ))
    (histart : IsCompStart lam (firstHalf w c a b t) i')
    (hconn : Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i q)
    (hconn' : Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i' q) :
    False :=
  not_connected_firstHalf_arc D lam v w c hlet hb hi hi' hne hcomp hiso t histart
    (connected_trans hconn (connected_symm hconn'))

end DGOPolygonCut
end GGT
end GroupApproximation
