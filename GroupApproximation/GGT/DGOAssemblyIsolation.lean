import GroupApproximation.GGT.DGOAssemblyLetters
import Mathlib.Data.Nat.Dist
import GroupApproximation.GGT.OsinTheorem54SepDistPrefix
import GroupApproximation.GGT.OsinTheorem54SepRotateComponent

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

/-- **Along the arc, no other same-label letter is connected to a distinguished
component.**

This letter-level form is the one the auxiliary-cycle surgery needs for an
arbitrary type-(2) opponent.  Cutting a subpath can change where its component
starts, but it cannot change its first letter or vertex. -/
theorem not_connected_firstHalf_arc_of_isCompOf (D : RelGenSet G Λ) (lam : Λ)
    (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i j : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length)
    (hi : i < c b - c a) (hjarc : j < c b - c a) (hne : j ≠ i)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i)) (t : List (RelLetter G Λ))
    (hjlen : j < (firstHalf w c a b t).length)
    (hcoHalf : ((firstHalf w c a b t)[j]'hjlen).IsCompOf lam) :
    ¬ Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i j := by
  intro hconn
  have hconnw : Connected D.fam lam v w (c a + i) (c a + j) :=
    (connected_firstHalf_iff D.fam lam w v c (le_of_lt hi) (le_of_lt hjarc) hb t).mp
      hconn
  have hjw : c a + j < w.length := by omega
  have hcoW : (w[c a + j]'hjw).IsCompOf lam :=
    (isCompOf_firstHalf_arc_iff lam w c hb hjarc t hjlen).mp hcoHalf
  obtain ⟨p, k, hpj, hjk', hpcomp⟩ :=
    exists_isComp_of_isCompOf lam w (c a + j) hjw hcoW
  have hpconn : Connected D.fam lam v w p (c a + j) := by
    obtain ⟨-, hkw', hrun', -, -⟩ := hpcomp
    exact span_mem_fam D lam v hlet (c a + j) (le_of_lt hjw) p hpj
      (fun m hm1 hm2 hm3 => hrun' m hm1 (by omega) hm3)
  have hip : Connected D.fam lam v w (c a + i) p :=
    connected_trans hconnw (connected_symm hpconn)
  rcases eq_or_ne p (c a + i) with hpi | hpi
  · subst hpi
    have hkeq : k = c a + i + 1 := isComp_end_unique hpcomp hcomp
    exact hne (by omega)
  · exact hiso.2 p hpi ⟨k, hpcomp⟩ hip

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
  obtain ⟨kj, hkj⟩ := hjstart
  obtain ⟨hjk, hkw, hrun, -, -⟩ := hkj
  have hjlen : j < (firstHalf w c a b t).length := by omega
  have hcoHalf : ((firstHalf w c a b t)[j]'hjlen).IsCompOf lam :=
    hrun j (le_refl j) hjk hjlen
  exact not_connected_firstHalf_arc_of_isCompOf D lam v w c hlet hb hi hjarc
    hne hcomp hiso t hjlen hcoHalf

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

/-- **Every failure of isolation in the first half has a chord partner.**
This is the existence half of DGO's broken-component assignment. -/
theorem exists_chord_partner_firstHalf (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length)
    (hi : i < c b - c a)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i))
    (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (firstHalf w c a b t) i)
    (hnot : ¬ IsIsolated D.fam lam (vertex v w (c a))
      (firstHalf w c a b t) i) :
    ∃ j : ℕ, c b - c a ≤ j ∧
      IsCompStart lam (firstHalf w c a b t) j ∧
      Connected D.fam lam (vertex v w (c a)) (firstHalf w c a b t) i j := by
  classical
  by_contra hnone
  apply hnot
  apply isIsolated_firstHalf D lam v w c hlet hb hi hcomp hiso t hstart
  intro j hj hjstart hconn
  exact hnone ⟨j, hj, hjstart, hconn⟩

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

/-! ## The wrapped second half -/

/-- **Letter-level wrapped-arc separation.**

As in `not_connected_firstHalf_arc_of_isCompOf`, this accepts the first letter
of an arbitrary component created by restricting a type-(2) subpath.  The
wrapped arc is handled in the rotated polygon, so an opponent crossing the old
word seam is covered without another case. -/
theorem not_connected_secondHalf_arc_of_isCompOf (D : RelGenSet G Λ)
    (lam : Λ) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b i j : ℕ} (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b)
    (hb : c b ≤ w.length) (hi : i < (w.length - c b) + c a)
    (hjarc : j < (w.length - c b) + c a) (hne : j ≠ i)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (hjlen : j < (secondHalf w c a b t).length)
    (hcoHalf : ((secondHalf w c a b t)[j]'hjlen).IsCompOf lam) :
    ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t) i j := by
  intro hconn
  have hconnR : Connected D.fam lam (vertex v w (c b))
      (rotWord w (c b)) i j :=
    (connected_secondHalf_rotWord_iff D.fam lam w v c ha hb
      (le_of_lt hi) (le_of_lt hjarc) t).mp hconn
  have hrotlen : (rotWord w (c b)).length = w.length := length_rotWord w hb
  have hcoR : ((rotWord w (c b))[j]'(by rw [hrotlen]; omega)).IsCompOf lam :=
    (isCompOf_secondHalf_rotWord_iff lam w c ha hb hjarc t hjlen).mp hcoHalf
  obtain ⟨p, k, hpj, hjk', hpcomp⟩ :=
    exists_isComp_of_isCompOf lam (rotWord w (c b)) j
      (by rw [hrotlen]; omega) hcoR
  have hletR : ∀ x ∈ rotWord w (c b), D.IsLetter x :=
    letters_rotWord D hlet (c b)
  have hpconn : Connected D.fam lam (vertex v w (c b))
      (rotWord w (c b)) p j := by
    obtain ⟨-, hkw', hrun', -, -⟩ := hpcomp
    exact span_mem_fam D lam (vertex v w (c b)) hletR j
      (by rw [hrotlen]; omega) p hpj
      (fun m hm1 hm2 hm3 => hrun' m hm1 (by omega) hm3)
  have hip : Connected D.fam lam (vertex v w (c b))
      (rotWord w (c b)) i p :=
    connected_trans hconnR (connected_symm hpconn)
  rcases eq_or_ne p i with hpi | hpi
  · subst p
    have hkeq : k = i + 1 := isComp_end_unique hpcomp hcomp
    exact hne (by omega)
  · exact hiso.2 p hpi ⟨k, hpcomp⟩ hip

/-- **Along the entire wrapped arc, nothing else is connected to a surviving
distinguished component.**

The arc is treated as a prefix of `rotWord w (c b)`.  Thus the suffix and prefix
regions of the original word, including a connection crossing their seam, are
handled by one component argument. -/
theorem not_connected_secondHalf_arc (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i j : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a)
    (hjarc : j < (w.length - c b) + c a) (hne : j ≠ i)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (hjstart : IsCompStart lam (secondHalf w c a b t) j) :
    ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t) i j := by
  obtain ⟨kj, hkj⟩ := hjstart
  obtain ⟨hjk, hkw, hrun, -, -⟩ := hkj
  have hjlen : j < (secondHalf w c a b t).length := by omega
  have hcoHalf : ((secondHalf w c a b t)[j]'hjlen).IsCompOf lam :=
    hrun j (le_refl j) hjk hjlen
  exact not_connected_secondHalf_arc_of_isCompOf D lam v w c hlet ha hb hi
    hjarc hne hcomp hiso t hjlen hcoHalf

/-- **A surviving rotated component is isolated in the second half once chord
partners are excluded.** -/
theorem isIsolated_secondHalf (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t) i)
    (hchord : ∀ j : ℕ, (w.length - c b) + c a ≤ j →
      IsCompStart lam (secondHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t) i j) :
    IsIsolated D.fam lam (vertex v w (c b)) (secondHalf w c a b t) i := by
  refine ⟨hstart, ?_⟩
  intro j hne hjstart hconn
  rcases Nat.lt_or_ge j ((w.length - c b) + c a) with hjarc | hjchord
  · exact not_connected_secondHalf_arc D lam v w c hlet ha hb hi hjarc hne
      hcomp hiso t hjstart hconn
  · exact hchord j hjchord hjstart hconn

/-- **Every failure of isolation in the wrapped second half has a chord
partner.** -/
theorem exists_chord_partner_secondHalf (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t) i)
    (hnot : ¬ IsIsolated D.fam lam (vertex v w (c b))
      (secondHalf w c a b t) i) :
    ∃ j : ℕ, (w.length - c b) + c a ≤ j ∧
      IsCompStart lam (secondHalf w c a b t) j ∧
      Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t) i j := by
  classical
  by_contra hnone
  apply hnot
  apply isIsolated_secondHalf D lam v w c hlet ha hb hi hcomp hiso t hstart
  intro j hj hjstart hconn
  exact hnone ⟨j, hj, hjstart, hconn⟩

/-- **Two survivors on the wrapped arc cannot share a chord partner.** -/
theorem chord_partner_unique_secondHalf (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i i' q : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b) (hb : c b ≤ w.length)
    (hi : i < (w.length - c b) + c a)
    (hi' : i' < (w.length - c b) + c a) (hne : i' ≠ i)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (histart : IsCompStart lam (secondHalf w c a b t) i')
    (hconn : Connected D.fam lam (vertex v w (c b))
      (secondHalf w c a b t) i q)
    (hconn' : Connected D.fam lam (vertex v w (c b))
      (secondHalf w c a b t) i' q) : False :=
  not_connected_secondHalf_arc D lam v w c hlet ha hb hi hi' hne hcomp hiso t
    histart (connected_trans hconn (connected_symm hconn'))

/-- **An original survivor before the cut point is isolated in the second
half.**  This is the concrete `w.take` branch: rotate the original component
past the seam with `isIsolated_rotWord_before`, then apply the wrapped-arc
isolation theorem above. -/
theorem isIsolated_secondHalf_of_before (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b p : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hclosed : RelLetter.listVal w = 1)
    (ha : c a ≤ c b) (hb : c b < w.length) (hp0 : 0 < p)
    (hpEnd : p + 1 ≤ c a) (hcomp : IsComp lam w p (p + 1))
    (hiso : IsIsolated D.fam lam v w p) (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t)
      (w.length - c b + p))
    (hchord : ∀ j : ℕ, (w.length - c b) + c a ≤ j →
      IsCompStart lam (secondHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
        (w.length - c b + p) j) :
    IsIsolated D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
      (w.length - c b + p) := by
  have hpCut : p + 1 ≤ c b := le_trans hpEnd ha
  have hrotcomp : IsComp lam (rotWord w (c b))
      (w.length - c b + p) (w.length - c b + (p + 1)) :=
    isComp_rotWord_before lam (le_of_lt hb) hcomp hpCut hp0
  have hrotiso : IsIsolated D.fam lam (vertex v w (c b))
      (rotWord w (c b)) (w.length - c b + p) :=
    isIsolated_rotWord_before D lam v hlet hclosed hb hcomp hpCut hp0 hiso
  apply isIsolated_secondHalf D lam v w c hlet ha (le_of_lt hb)
    (i := w.length - c b + p) (by omega) hrotcomp hrotiso t hstart hchord

/-- **The basepoint survivor before the cut is isolated in the second half.**
This is the cyclic edge case of `isIsolated_secondHalf_of_before`: original
index `0` acquires the terminal letter of `w` as its predecessor after rotation,
and isolation of the closed polygon rules that predecessor out. -/
theorem isIsolated_secondHalf_of_before_zero (D : RelGenSet G Λ) (lam : Λ)
    (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hclosed : RelLetter.listVal w = 1)
    (ha : c a ≤ c b) (hb : c b < w.length) (hzeroEnd : 1 ≤ c a)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t) (w.length - c b))
    (hchord : ∀ j : ℕ, (w.length - c b) + c a ≤ j →
      IsCompStart lam (secondHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
        (w.length - c b) j) :
    IsIsolated D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
      (w.length - c b) := by
  have hrotcomp : IsComp lam (rotWord w (c b))
      (w.length - c b) (w.length - c b + 1) :=
    isComp_rotWord_zero_before lam hb hcomp (by omega)
      (notMem_terminal_of_isIsolated_zero D lam v hlet hclosed hcomp hiso
        (by omega))
  have hrotiso : IsIsolated D.fam lam (vertex v w (c b))
      (rotWord w (c b)) (w.length - c b) :=
    isIsolated_rotWord_zero_before D lam v hlet hclosed hb hcomp (by omega) hiso
  apply isIsolated_secondHalf D lam v w c hlet ha (le_of_lt hb)
    (i := w.length - c b) (by omega) hrotcomp hrotiso t hstart hchord

/-- **The before-cut transport when the rotation point is the word endpoint.**
Here `rotWord w |w| = w`, so no cyclic component argument is needed. -/
theorem isIsolated_secondHalf_of_before_at_end (D : RelGenSet G Λ)
    (lam : Λ) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b p : ℕ} (hlet : ∀ x ∈ w, D.IsLetter x)
    (hclosed : RelLetter.listVal w = 1) (ha : c a ≤ c b)
    (hb : c b = w.length) (hpEnd : p + 1 ≤ c a)
    (hcomp : IsComp lam w p (p + 1))
    (hiso : IsIsolated D.fam lam v w p) (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t)
      (w.length - c b + p))
    (hchord : ∀ j : ℕ, (w.length - c b) + c a ≤ j →
      IsCompStart lam (secondHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
        (w.length - c b + p) j) :
    IsIsolated D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
      (w.length - c b + p) := by
  have hrotcomp : IsComp lam (rotWord w (c b))
      (w.length - c b + p) (w.length - c b + p + 1) := by
    simpa [hb, rotWord] using hcomp
  have hrotiso : IsIsolated D.fam lam (vertex v w (c b))
      (rotWord w (c b)) (w.length - c b + p) := by
    simpa [hb, rotWord, vertex_length_of_closed v w hclosed] using hiso
  apply isIsolated_secondHalf D lam v w c hlet ha (by omega)
    (i := w.length - c b + p) (by omega) hrotcomp hrotiso t hstart hchord

/-- **An original survivor after the cut point is isolated in the second
half.**  This is the complementary `w.drop` branch. -/
theorem isIsolated_secondHalf_of_after (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b p : ℕ}
    (hlet : ∀ x ∈ w, D.IsLetter x) (hclosed : RelLetter.listVal w = 1)
    (ha : c a ≤ c b) (hb : c b ≤ w.length) (hp0 : 0 < p)
    (hpStart : c b ≤ p) (hcomp : IsComp lam w p (p + 1))
    (hiso : IsIsolated D.fam lam v w p) (t : List (RelLetter G Λ))
    (hstart : IsCompStart lam (secondHalf w c a b t) (p - c b))
    (hchord : ∀ j : ℕ, (w.length - c b) + c a ≤ j →
      IsCompStart lam (secondHalf w c a b t) j →
      ¬ Connected D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
        (p - c b) j) :
    IsIsolated D.fam lam (vertex v w (c b)) (secondHalf w c a b t)
      (p - c b) := by
  have hwrap : ∀ h0 : 0 < w.length, p + 1 = w.length →
      ¬ (w[0]'h0).IsCompOf lam :=
    notMem_wrap_of_isIsolated D lam v hlet hclosed hcomp hiso hp0
  have hrotcomp0 : IsComp lam (rotWord w (c b))
      (p - c b) (p + 1 - c b) :=
    isComp_rotWord_of_le lam hcomp hpStart hb hwrap
  have hend : p + 1 - c b = (p - c b) + 1 := by omega
  have hrotcomp : IsComp lam (rotWord w (c b)) (p - c b) (p - c b + 1) := by
    rwa [← hend]
  have hrotiso : IsIsolated D.fam lam (vertex v w (c b))
      (rotWord w (c b)) (p - c b) :=
    isIsolated_rotWord_of_le D lam v hlet hclosed hcomp hiso hpStart hb hwrap
  have hpSubSucc : p - c b + 1 = p + 1 - c b := by omega
  have hpSubBound : p + 1 - c b ≤ w.length - c b :=
    Nat.sub_le_sub_right hcomp.2.1 (c b)
  have hiArc : p - c b < (w.length - c b) + c a := by
    have hbase : p - c b < w.length - c b := by omega
    exact hbase.trans_le (Nat.le_add_right (w.length - c b) (c a))
  apply isIsolated_secondHalf D lam v w c hlet ha hb (i := p - c b)
    hiArc hrotcomp hrotiso t hstart hchord

/-! ## The broken-component assignment -/

/-- **Choosing one chord partner for every broken component is injective.**

This packages the disjointness argument used twice in DGO's construction of
the ordered lists `p_{i_j}` and `y_j`.  Two broken components with the same
partner first have the same peripheral label (read the partner's first letter),
then are connected through that partner.  Arc separation (supplied by
`not_connected_firstHalf_arc` or its wrapped analogue) forces their positions,
and hence their original indices, to agree. -/
theorem chordPartner_injOn (D : RelGenSet G Λ) (v : G)
    (half : List (RelLetter G Λ)) (I : Finset ℕ)
    (lam : ℕ → Λ) (pos partner : ℕ → ℕ)
    (hpos : Set.InjOn pos (↑I : Set ℕ))
    (hsep : ∀ s ∈ I, ∀ t ∈ I, pos s ≠ pos t →
      ¬ Connected D.fam (lam s) v half (pos s) (pos t))
    (hpartner : ∀ s ∈ I, IsCompStart (lam s) half (partner s))
    (hconn : ∀ s ∈ I, Connected D.fam (lam s) v half (pos s) (partner s)) :
    Set.InjOn partner (↑I : Set ℕ) := by
  intro s hs t ht heq
  have hsI : s ∈ I := hs
  have htI : t ∈ I := ht
  obtain ⟨ks, hcs⟩ := hpartner s hsI
  obtain ⟨kt, hct⟩ := hpartner t htI
  have hplen : partner s < half.length := lt_of_lt_of_le hcs.1 hcs.2.1
  have hcoS : (half[partner s]'hplen).IsCompOf (lam s) :=
    hcs.2.2.1 (partner s) le_rfl hcs.1 hplen
  have hcoT : (half[partner s]'hplen).IsCompOf (lam t) := by
    have hplenT : partner t < half.length := lt_of_lt_of_le hct.1 hct.2.1
    have h := hct.2.2.1 (partner t) le_rfl hct.1 hplenT
    simpa [← heq] using h
  have hlam : lam s = lam t := eq_of_isCompOf_of_isCompOf hcoS hcoT
  have hposEq : pos s = pos t := by
    by_contra hne
    have hconnT : Connected D.fam (lam s) v half (pos t) (partner t) := by
      rw [hlam]
      exact hconn t htI
    have hthrough : Connected D.fam (lam s) v half (pos s) (pos t) := by
      change (vertex v half (pos t))⁻¹ * vertex v half (partner t) ∈ D.fam (lam s) at hconnT
      rw [← heq] at hconnT
      change Connected D.fam (lam s) v half (pos t) (partner s) at hconnT
      exact connected_trans (hconn s hsI) (connected_symm hconnT)
    exact hsep s hsI t htI hne hthrough
  exact hpos hs ht hposEq

/-- **The broken components admit a disjoint chord-partner assignment.**

Existence comes from `exists_chord_partner_firstHalf` or its wrapped analogue;
`chordPartner_injOn` supplies injectivity.  This is the finite choice step that
turns DGO's successive "take the first broken component" prose into data usable
by the auxiliary-cycle constructor. -/
theorem exists_injective_chordPartner (D : RelGenSet G Λ) (v : G)
    (half : List (RelLetter G Λ)) (I : Finset ℕ)
    (lam : ℕ → Λ) (pos : ℕ → ℕ) (ChordStart : ℕ → Prop)
    (hpos : Set.InjOn pos (↑I : Set ℕ))
    (hsep : ∀ s ∈ I, ∀ t ∈ I, pos s ≠ pos t →
      ¬ Connected D.fam (lam s) v half (pos s) (pos t))
    (hexists : ∀ s ∈ I, ∃ q : ℕ, ChordStart q ∧
      IsCompStart (lam s) half q ∧ Connected D.fam (lam s) v half (pos s) q) :
    ∃ partner : ℕ → ℕ,
      (∀ s ∈ I, ChordStart (partner s) ∧
        IsCompStart (lam s) half (partner s) ∧
        Connected D.fam (lam s) v half (pos s) (partner s)) ∧
      Set.InjOn partner (↑I : Set ℕ) := by
  classical
  let partner : ℕ → ℕ := fun s =>
    if hs : s ∈ I then Classical.choose (hexists s hs) else 0
  have hspec : ∀ s ∈ I, ChordStart (partner s) ∧
      IsCompStart (lam s) half (partner s) ∧
      Connected D.fam (lam s) v half (pos s) (partner s) := by
    intro s hs
    simpa [partner, hs] using Classical.choose_spec (hexists s hs)
  refine ⟨partner, hspec, ?_⟩
  exact chordPartner_injOn D v half I lam pos partner hpos hsep
    (fun s hs => (hspec s hs).2.1) (fun s hs => (hspec s hs).2.2)

/-- **DGO's greedy broken-component enumeration, with its chord incidences.**

The proof of Proposition 4.14 does *not* sort the partners `y_j` along the
cutting chord.  It repeatedly takes the first still-broken polygon component
after the preceding one and records an arbitrary chord component connected to
it.  Thus the datum that is ordered is `pos s`; `partner s` merely travels with
the same source `s`.

`xs` is the increasing list of broken positions and `ys` is the simultaneously
chosen list of their partners.  The final clause is the exact greedy invariant:
between two consecutive entries of `xs` there is no further broken incidence.
This is what rules out a type-(2) opponent between successive charged sides.
No (generally unjustified) monotonicity assertion about `ys` is made. -/
theorem exists_greedy_incidenceEnumeration (I : Finset ℕ)
    (pos partner : ℕ → ℕ) (hpos : Set.InjOn pos (↑I : Set ℕ)) :
    ∃ xs ys : List ℕ,
      xs.length = I.card ∧ ys.length = xs.length ∧
      xs.Pairwise (· ≤ ·) ∧ xs.Nodup ∧
      (∀ x : ℕ, x ∈ xs ↔ ∃ s ∈ I, pos s = x) ∧
      (∀ j : ℕ, ∀ hj : j < xs.length,
        ∃ s ∈ I, xs[j] = pos s ∧ ys[j]? = some (partner s)) ∧
      (∀ j : ℕ, ∀ hj : j + 1 < xs.length, ∀ s ∈ I,
        ¬ (xs[j]'(by omega) < pos s ∧ pos s < xs[j + 1]'hj)) := by
  classical
  let xs : List ℕ := (I.image pos).sort (· ≤ ·)
  let source : ℕ → ℕ := fun x =>
    if hx : ∃ s ∈ I, pos s = x then Classical.choose hx else 0
  let ys : List ℕ := xs.map fun x => partner (source x)
  have hsource : ∀ x : ℕ, (∃ s ∈ I, pos s = x) →
      source x ∈ I ∧ pos (source x) = x := by
    intro x hx
    have hspec := Classical.choose_spec hx
    simpa [source, hx] using hspec
  have hcard : (I.image pos).card = I.card := by
    exact Finset.card_image_iff.mpr fun s hs t ht heq =>
      hpos (by simpa using hs) (by simpa using ht) heq
  have hmem : ∀ x : ℕ, x ∈ xs ↔ ∃ s ∈ I, pos s = x := by
    intro x
    simp only [xs, Finset.mem_sort, Finset.mem_image]
  refine ⟨xs, ys, ?_, ?_, ?_, ?_, hmem, ?_, ?_⟩
  · simpa [xs] using hcard
  · simp [ys]
  · exact Finset.pairwise_sort _ _
  · exact Finset.sort_nodup _ _
  · intro j hj
    have hxmem : xs[j] ∈ xs := List.getElem_mem hj
    have hx : ∃ s ∈ I, pos s = xs[j] := (hmem xs[j]).mp hxmem
    refine ⟨source xs[j], (hsource xs[j] hx).1, ?_, ?_⟩
    · exact (hsource xs[j] hx).2.symm
    · simp [ys, hj]
  · intro j hj s hs hbetween
    have hsmem : pos s ∈ xs := (hmem (pos s)).mpr ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hks⟩ := List.mem_iff_getElem.mp hsmem
    by_cases hkj : k ≤ j
    · rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
      · omega
      · have hle := List.pairwise_iff_getElem.mp
          (show xs.Pairwise (· ≤ ·) from Finset.pairwise_sort _ _) k j hk
          (show j < xs.length by omega) hlt
        omega
    · have hjk : j + 1 ≤ k := by omega
      rcases Nat.eq_or_lt_of_le hjk with heq | hlt
      · subst k
        omega
      · have hle := List.pairwise_iff_getElem.mp
          (show xs.Pairwise (· ≤ ·) from Finset.pairwise_sort _ _) (j + 1) k
          hj hk hlt
        omega

/-! ## Why greedy incidence is not chord order

The next finite calculation isolates the missing assertion in the printed
side-count estimate.  Sixteen broken positions can be visited greedily in arc
order while their distinct chord partners zigzag.  The chord subpaths between
successive partner positions then have total variation `120`.  Even deleting
one edge at every one of the fifteen transitions (to pass from component
starts to the trimmed endpoint convention) leaves `105 > 6 * 16`, before any
polygon, connector, or partner sides are counted.

This satisfies precisely the finite consequences proved above from original
isolation and chord geodesicity: distinct broken positions, distinct partners,
and no broken position between consecutive greedy choices.  Hyperbolicity does
not add a planar/noncrossing relation to these coset incidences.  Therefore the
estimate `∑ n_j ≤ n + 6 * length t` used after DGO's construction needs a
separate monotone-partner (or bounded-total-variation) premise. -/

/-- Total length of the successive intervals traversed by a list of positions
on one combinatorial path. -/
def chordTraversalCost : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: ys => Nat.dist x y + chordTraversalCost (y :: ys)

/-- **The exact extra premise needed by DGO's side-count line.**

For a chord of `L` edges, the successive partner endpoints used by one greedy
half-family must have total variation at most `L`.  Monotone partner order is a
sufficient way to obtain this, but the bounded-variation formulation is the
minimal numerical fact consumed by `∑ n_j ≤ n + 6L`. -/
def ChordPartnerTraversalBound (L : ℕ) (partners : List ℕ) : Prop :=
  chordTraversalCost partners ≤ L

/-- **The traversal bound actually forced by finite chord incidence.**

Unlike `ChordPartnerTraversalBound`, this does not assert that the partners
occur monotonically.  It records the unconditional quadratic estimate: a list
of distinct starts on an `L`-edge chord has at most `L` entries, and every jump
between two starts costs at most `L`.

This is the faithful replacement for the unproved linear-traversal step in the
published proof of Proposition 4.14. -/
def ChordPartnerQuadraticTraversalBound (L : ℕ) (partners : List ℕ) : Prop :=
  chordTraversalCost partners ≤ L * L

/-- The sixteen chord partners used in the source-audit counterexample above:
they are distinct starts on a chord of length sixteen, listed in the order of
their partners on the polygon arc rather than in chord order. -/
def zigzagChordPartners : List ℕ :=
  [0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]

/-- **The printed linear chord-traversal assertion is not a consequence of
distinct chord incidence.**

The explicit source-order enumeration has sixteen distinct entries, every
one the start of an edge on a sixteen-edge chord, but its total variation is
`120`, not at most `16`.  Thus injectivity and chord range alone imply only
the quadratic traversal estimate used below; a linear estimate needs a
genuine monotonicity or bounded-variation theorem. -/
theorem zigzagChordPartners_refutes_linearTraversal :
    zigzagChordPartners.Nodup ∧
      (∀ y ∈ zigzagChordPartners, y < 16) ∧
      chordTraversalCost zigzagChordPartners = 120 ∧
      ¬ ChordPartnerTraversalBound 16 zigzagChordPartners ∧
      ChordPartnerQuadraticTraversalBound 16 zigzagChordPartners := by
  norm_num [zigzagChordPartners, chordTraversalCost,
    ChordPartnerTraversalBound, ChordPartnerQuadraticTraversalBound,
    Nat.dist]

/-- If every entry is at most `L`, each transition costs at most `L`, so the
total traversal is at most `partners.length * L`.  No order premise occurs. -/
theorem chordTraversalCost_le_length_mul {partners : List ℕ} {L : ℕ}
    (hupper : ∀ y ∈ partners, y ≤ L) :
    chordTraversalCost partners ≤ partners.length * L := by
  induction partners with
  | nil => simp [chordTraversalCost]
  | cons x xs ih =>
      cases xs with
      | nil => simp [chordTraversalCost]
      | cons y ys =>
          have hx : x ≤ L := hupper x (by simp)
          have hy : y ≤ L := hupper y (by simp)
          have hdist : Nat.dist x y ≤ L := by
            rcases le_total x y with hxy | hyx
            · rw [Nat.dist_eq_sub_of_le hxy]
              omega
            · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
              omega
          have htail : chordTraversalCost (y :: ys) ≤ (y :: ys).length * L :=
            ih (fun z hz => hupper z (by simp [hz]))
          calc
            chordTraversalCost (x :: y :: ys) =
                Nat.dist x y + chordTraversalCost (y :: ys) := rfl
            _ ≤ L + (y :: ys).length * L := Nat.add_le_add hdist htail
            _ = (x :: y :: ys).length * L := by
              simp only [List.length_cons]
              ring

/-- **Quadratic traversal from the data supplied by the chord construction.**

`partners.Nodup` is partner injectivity, and `y < L` says that `y` is the
start of a component on the `L`-edge chord.  These imply the quadratic bound
without any planar or monotonicity assumption. -/
theorem chordPartnerQuadraticTraversalBound_of_nodup_lt
    {partners : List ℕ} {L : ℕ} (hnodup : partners.Nodup)
    (hrange : ∀ y ∈ partners, y < L) :
    ChordPartnerQuadraticTraversalBound L partners := by
  have hsubset : partners.toFinset ⊆ Finset.range L := by
    intro y hy
    exact Finset.mem_range.mpr (hrange y (by simpa using hy))
  have hcard : partners.length ≤ L := by
    have h := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hnodup, Finset.card_range] at h
    exact h
  unfold ChordPartnerQuadraticTraversalBound
  exact (chordTraversalCost_le_length_mul
    (fun y hy => le_of_lt (hrange y hy))).trans
      (Nat.mul_le_mul hcard le_rfl)

/-- **Quadratic traversal for the greedily enumerated partner list.**

This is the producer-shaped version used by the Proposition 4.14 assembly.
The enumeration is ordered by the broken polygon components, not by their
partners on the chord.  Nevertheless, injectivity of the partner assignment
and the fact that every selected partner starts on an `L`-edge chord imply
that there are at most `L` entries.  Every jump has length at most `L`, hence
the actual greedily ordered list has traversal cost at most `L²`.

No monotonicity or planar ordering of the partners is asserted here. -/
theorem chordPartnerQuadraticTraversalBound_of_enumeration
    (I : Finset ℕ) (partner : ℕ → ℕ) (partners : List ℕ) (L : ℕ)
    (hlength : partners.length = I.card)
    (hentries : ∀ j : ℕ, ∀ hj : j < partners.length,
      ∃ s ∈ I, partners[j] = partner s)
    (hinj : Set.InjOn partner (↑I : Set ℕ))
    (hrange : ∀ s ∈ I, partner s < L) :
    ChordPartnerQuadraticTraversalBound L partners := by
  have himage : (I.image partner).card = I.card := by
    exact Finset.card_image_iff.mpr fun s hs t ht heq =>
      hinj (by simpa using hs) (by simpa using ht) heq
  have hsubset : I.image partner ⊆ Finset.range L := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (hrange s hs)
  have hcard : partners.length ≤ L := by
    rw [hlength, ← himage]
    simpa using Finset.card_le_card hsubset
  have hupper : ∀ y ∈ partners, y ≤ L := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    obtain ⟨s, hs, heq⟩ := hentries j hj
    rw [heq]
    exact le_of_lt (hrange s hs)
  unfold ChordPartnerQuadraticTraversalBound
  exact (chordTraversalCost_le_length_mul hupper).trans
    (Nat.mul_le_mul hcard le_rfl)

/-- **The greedy incidence constructor already supplies the quadratic
traversal input.**

This packages `exists_greedy_incidenceEnumeration` with partner injectivity
and the chord-start range.  It is the exact bridge from the component-surgery
constructor to `sumBound_linear_of_quadraticChordTraversal`: all ordering and
no-intervening-source conclusions are retained, while the partner list gets
the unconditional quadratic traversal certificate. -/
theorem exists_greedy_incidenceEnumeration_quadratic (I : Finset ℕ)
    (pos partner : ℕ → ℕ) (L : ℕ)
    (hpos : Set.InjOn pos (↑I : Set ℕ))
    (hpartner : Set.InjOn partner (↑I : Set ℕ))
    (hrange : ∀ s ∈ I, partner s < L) :
    ∃ xs ys : List ℕ,
      xs.length = I.card ∧ ys.length = xs.length ∧
      xs.Pairwise (· ≤ ·) ∧ xs.Nodup ∧
      (∀ x : ℕ, x ∈ xs ↔ ∃ s ∈ I, pos s = x) ∧
      (∀ j : ℕ, ∀ hj : j < xs.length,
        ∃ s ∈ I, xs[j] = pos s ∧ ys[j]? = some (partner s)) ∧
      ChordPartnerQuadraticTraversalBound L ys ∧
      (∀ j : ℕ, ∀ hj : j + 1 < xs.length, ∀ s ∈ I,
        ¬ (xs[j]'(by omega) < pos s ∧ pos s < xs[j + 1]'hj)) := by
  obtain ⟨xs, ys, hxs, hys, horder, hnodup, hmem, hentries, hgap⟩ :=
    exists_greedy_incidenceEnumeration I pos partner hpos
  have hquadratic : ChordPartnerQuadraticTraversalBound L ys := by
    apply chordPartnerQuadraticTraversalBound_of_enumeration I partner ys L
      (hys.trans hxs) _ hpartner hrange
    intro j hj
    obtain ⟨s, hs, _hx, hy⟩ := hentries j (by omega)
    refine ⟨s, hs, ?_⟩
    rw [List.getElem?_eq_getElem hj] at hy
    exact Option.some.inj hy
  exact ⟨xs, ys, hxs, hys, horder, hnodup, hmem, hentries,
    hquadratic, hgap⟩

/-! ## The two connector-indexed half families -/

/-- **The finite index data for all auxiliary cycles cut from one half.**

There is one auxiliary cycle before the first broken component, one between
each successive pair, and one after the last.  Thus `pieceCount` below is
`sources.length + 1`.  Keeping the simultaneously selected `partners` in this
certificate is essential: the construction is indexed in source order, while
the unconditional estimate on the connector/chord overhead is the quadratic
traversal estimate on that same, generally nonmonotone, partner list.

This structure contains only data already proved by the greedy enumeration;
it does not assert that the corresponding geometric paths have been assembled
or that their target components are isolated.  Those geometric obligations
remain explicit inputs to the family constructor. -/
structure GreedyHalfFamilyIndex (I : Finset ℕ) (pos partner : ℕ → ℕ)
    (chordLength : ℕ) where
  sources : List ℕ
  partners : List ℕ
  source_length : sources.length = I.card
  partner_length : partners.length = sources.length
  source_order : sources.Pairwise (· ≤ ·)
  source_nodup : sources.Nodup
  source_mem : ∀ x : ℕ, x ∈ sources ↔ ∃ s ∈ I, pos s = x
  entries : ∀ j : ℕ, ∀ hj : j < sources.length,
    ∃ s ∈ I, sources[j] = pos s ∧ partners[j]? = some (partner s)
  partner_lt : ∀ y ∈ partners, y < chordLength
  traversal : ChordPartnerQuadraticTraversalBound chordLength partners
  gap : ∀ j : ℕ, ∀ hj : j + 1 < sources.length, ∀ s ∈ I,
    ¬ (sources[j]'(by omega) < pos s ∧ pos s < sources[j + 1]'hj)
  source_count_le : I.card ≤ chordLength

namespace GreedyHalfFamilyIndex

/-- The connector-indexed number of auxiliary cycles in one half. -/
def pieceCount {I : Finset ℕ} {pos partner : ℕ → ℕ} {chordLength : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner chordLength) : ℕ :=
  A.sources.length + 1

theorem pieceCount_eq {I : Finset ℕ} {pos partner : ℕ → ℕ}
    {chordLength : ℕ} (A : GreedyHalfFamilyIndex I pos partner chordLength) :
    A.pieceCount = I.card + 1 := by
  simp [pieceCount, A.source_length]

theorem pieceCount_le {I : Finset ℕ} {pos partner : ℕ → ℕ}
    {chordLength : ℕ} (A : GreedyHalfFamilyIndex I pos partner chordLength) :
    A.pieceCount ≤ chordLength + 1 := by
  rw [A.pieceCount_eq]
  have hcount := A.source_count_le
  omega

end GreedyHalfFamilyIndex

/-- **One half's connector index is constructed from the actual greedy
incidences.**

The last field is the second use of partner injectivity: the partner image is
a subset of the starts of the `chordLength` chord edges, so there are at most
`chordLength` broken components and hence at most `chordLength + 1` auxiliary
cycles in this half. -/
theorem exists_greedyHalfFamilyIndex (I : Finset ℕ)
    (pos partner : ℕ → ℕ) (chordLength : ℕ)
    (hpos : Set.InjOn pos (↑I : Set ℕ))
    (hpartner : Set.InjOn partner (↑I : Set ℕ))
    (hrange : ∀ s ∈ I, partner s < chordLength) :
    Nonempty (GreedyHalfFamilyIndex I pos partner chordLength) := by
  classical
  obtain ⟨xs, ys, hxs, hys, horder, hnodup, hmem, hentries,
    hquadratic, hgap⟩ :=
    exists_greedy_incidenceEnumeration_quadratic I pos partner chordLength
      hpos hpartner hrange
  have himage : (I.image partner).card = I.card := by
    exact Finset.card_image_iff.mpr fun s hs t ht heq =>
      hpartner (by simpa using hs) (by simpa using ht) heq
  have hsubset : I.image partner ⊆ Finset.range chordLength := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (hrange s hs)
  have hcard : I.card ≤ chordLength := by
    rw [← himage]
    simpa using Finset.card_le_card hsubset
  exact ⟨{
    sources := xs
    partners := ys
    source_length := hxs
    partner_length := hys
    source_order := horder
    source_nodup := hnodup
    source_mem := hmem
    entries := hentries
    partner_lt := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
      obtain ⟨s, hs, _hsource, hpartner⟩ := hentries j (by omega)
      rw [List.getElem?_eq_getElem hj] at hpartner
      have heq := Option.some.inj hpartner
      rw [heq]
      exact hrange s hs
    traversal := hquadratic
    gap := hgap
    source_count_le := hcard
  }⟩

/-- **Both greedy halves, with a common cutting chord, in one certificate.**

The two source orders are deliberately independent.  No ordering relation
between partners on either half, or between the two partner lists, is claimed.
The global construction may now index its children by the disjoint union of
the two `pieceCount` ranges; only the proved count and quadratic traversal
bounds are exported. -/
structure TwoHalfGreedyFamilyIndex (I₁ I₂ : Finset ℕ)
    (pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ) (chordLength : ℕ) where
  first : GreedyHalfFamilyIndex I₁ pos₁ partner₁ chordLength
  second : GreedyHalfFamilyIndex I₂ pos₂ partner₂ chordLength

namespace TwoHalfGreedyFamilyIndex

/-- Total number of connector-indexed auxiliary cycles across both halves. -/
def pieceCount {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    (A : TwoHalfGreedyFamilyIndex I₁ I₂ pos₁ partner₁ pos₂ partner₂
      chordLength) : ℕ :=
  A.first.pieceCount + A.second.pieceCount

/-- The two half families contain at most `2 * chordLength + 2` children. -/
theorem pieceCount_le {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    (A : TwoHalfGreedyFamilyIndex I₁ I₂ pos₁ partner₁ pos₂ partner₂
      chordLength) :
    A.pieceCount ≤ 2 * chordLength + 2 := by
  unfold pieceCount
  have h₁ := A.first.pieceCount_le
  have h₂ := A.second.pieceCount_le
  omega

/-- The actual two greedy traversals have total cost at most twice the square
of the chord length. -/
theorem traversalCost_add_le {I₁ I₂ : Finset ℕ}
    {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ} {chordLength : ℕ}
    (A : TwoHalfGreedyFamilyIndex I₁ I₂ pos₁ partner₁ pos₂ partner₂
      chordLength) :
    chordTraversalCost A.first.partners +
        chordTraversalCost A.second.partners ≤
      2 * (chordLength * chordLength) := by
  have h₁ := A.first.traversal
  have h₂ := A.second.traversal
  unfold ChordPartnerQuadraticTraversalBound at h₁ h₂
  omega

end TwoHalfGreedyFamilyIndex

/-- **Simultaneous construction of the two connector-indexed half families.**

This is the exact two-half output of the incidence lane.  Its hypotheses are
the partner assignments supplied independently by the first-half and wrapped
second-half isolation arguments. -/
theorem exists_twoHalfGreedyFamilyIndex (I₁ I₂ : Finset ℕ)
    (pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ) (chordLength : ℕ)
    (hpos₁ : Set.InjOn pos₁ (↑I₁ : Set ℕ))
    (hpartner₁ : Set.InjOn partner₁ (↑I₁ : Set ℕ))
    (hrange₁ : ∀ s ∈ I₁, partner₁ s < chordLength)
    (hpos₂ : Set.InjOn pos₂ (↑I₂ : Set ℕ))
    (hpartner₂ : Set.InjOn partner₂ (↑I₂ : Set ℕ))
    (hrange₂ : ∀ s ∈ I₂, partner₂ s < chordLength) :
    Nonempty (TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength) := by
  obtain ⟨A₁⟩ := exists_greedyHalfFamilyIndex I₁ pos₁ partner₁ chordLength
    hpos₁ hpartner₁ hrange₁
  obtain ⟨A₂⟩ := exists_greedyHalfFamilyIndex I₂ pos₂ partner₂ chordLength
    hpos₂ hpartner₂ hrange₂
  exact ⟨⟨A₁, A₂⟩⟩

/-- Monotone partner order inside one chord interval supplies the named
bounded-variation premise. -/
theorem chordPartnerTraversalBound_of_pairwise {partners : List ℕ} {a L : ℕ}
    (horder : partners.Pairwise (· ≤ ·))
    (hlower : ∀ y ∈ partners, a ≤ y) (hupper : ∀ y ∈ partners, y ≤ a + L) :
    ChordPartnerTraversalBound L partners := by
  unfold ChordPartnerTraversalBound
  have hgeneral : ∀ (ys : List ℕ) (lo hi : ℕ),
      ys.Pairwise (· ≤ ·) →
      (∀ y ∈ ys, lo ≤ y) → (∀ y ∈ ys, y ≤ hi) →
      chordTraversalCost ys ≤ hi - lo := by
    intro ys
    induction ys with
    | nil =>
        intro lo hi _ _ _
        simp [chordTraversalCost]
    | cons x xs ih =>
        intro lo hi hpair hlo hhi
        cases xs with
        | nil => simp [chordTraversalCost]
        | cons y ys =>
            have hpair' := List.pairwise_cons.mp hpair
            have hxy : x ≤ y := hpair'.1 y (by simp)
            have htail : (y :: ys).Pairwise (· ≤ ·) := hpair'.2
            have htail' := List.pairwise_cons.mp htail
            have hlowerTail : ∀ z ∈ y :: ys, y ≤ z := by
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact le_rfl
              · exact htail'.1 z hz
            have hupperTail : ∀ z ∈ y :: ys, z ≤ hi := by
              intro z hz
              exact hhi z (List.mem_cons_of_mem x hz)
            have hrec := ih y hi htail hlowerTail hupperTail
            rw [chordTraversalCost, Nat.dist_eq_sub_of_le hxy]
            have hxlo : lo ≤ x := hlo x (by simp)
            have hyhi : y ≤ hi := hhi y (by simp)
            omega
  have h := hgeneral partners a (a + L) horder hlower hupper
  omega

/-- A smallest convenient explicit zigzag whose chord traversal exceeds the
coefficient `6` in DGO's claimed total-side estimate. -/
def greedyIncidenceZigzagPartners : List ℕ :=
  [0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]

/-- **Finite countermodel to deriving the chord budget from the local
incidence invariants.** -/
theorem greedyIncidence_local_invariants_do_not_bound_chordTraversal :
      greedyIncidenceZigzagPartners.Nodup ∧
      greedyIncidenceZigzagPartners.length = 16 ∧
      (∀ j : ℕ, ∀ hj : j + 1 < 16, ∀ s : ℕ, s < 16 →
        ¬ ((List.range 16)[j]'(by simpa using Nat.lt_of_succ_lt hj) < s ∧
          s < (List.range 16)[j + 1]'(by simpa using hj))) ∧
      6 * 16 + 15 < chordTraversalCost greedyIncidenceZigzagPartners := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · norm_num [greedyIncidenceZigzagPartners]
  · intro j hj s hs hbetween
    simp only [List.getElem_range] at hbetween
    omega
  · norm_num [greedyIncidenceZigzagPartners, chordTraversalCost, Nat.dist]

end DGOPolygonCut
end GGT
end GroupApproximation
