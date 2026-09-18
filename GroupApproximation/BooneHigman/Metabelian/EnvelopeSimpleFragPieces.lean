import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleGap
import GroupApproximation.BooneHigman.V.Supports
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Membership
import GroupApproximation.Meta.AxiomGuard

/-!
# Fragments of `V_X(H)`

`fragPieces H`: the elements of `V_X(H)` supported in the union of the cones of two words of
length `4`.

* `frag_pair` (for `Nontrivial X`): two pieces are jointly supported in a set missing a cone,
  since four words of length `4` leave a fifth one (`frag_exists_word_ne`, diagonal choice);
* `frag_localize_mem`: `V_X(H)` is stable under `localize t`, hence `localize u e` is a piece for
  `|u| = 4` and `e ∈ V_X(H)` (`frag_localize_mem_pieces`);
* `frag_exists_list`: members of the closure of the pieces are products of pieces.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees
open HydeLodha

noncomputable section

variable {X : Type*}

/-- Four words of length `4` miss a fifth word of length `4`. -/
theorem frag_exists_word_ne [Nontrivial X] (p q r s : List X) :
    ∃ t : List X, t.length = 4 ∧ t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s := by
  obtain ⟨x₀, -, -⟩ := exists_pair_ne X
  choose oth hoth using fun a : X => exists_ne a
  refine ⟨[oth (p.getD 0 x₀), oth (q.getD 1 x₀), oth (r.getD 2 x₀), oth (s.getD 3 x₀)], rfl,
    fun h => hoth (p.getD 0 x₀) ?_, fun h => hoth (q.getD 1 x₀) ?_,
    fun h => hoth (r.getD 2 x₀) ?_, fun h => hoth (s.getD 3 x₀) ?_⟩
  · have e := congrArg (fun l : List X => l.getD 0 x₀) h
    simpa using e
  · have e := congrArg (fun l : List X => l.getD 1 x₀) h
    simpa using e
  · have e := congrArg (fun l : List X => l.getD 2 x₀) h
    simpa using e
  · have e := congrArg (fun l : List X => l.getD 3 x₀) h
    simpa using e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_exists_word_ne

variable [Finite X]

/-- Elements of `V_X(H)` supported in two cones of words of length `4`. -/
def fragPieces (H : Subgroup (TreeAut X)) : Set (Equiv.Perm (Cantor X)) :=
  {a | a ∈ roverNekrashevych X H ∧
    ∃ p q : List X, p.length = 4 ∧ q.length = 4 ∧ SupportedIn a (cone p ∪ cone q)}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.fragPieces

theorem mem_fragPieces {H : Subgroup (TreeAut X)} {a : Equiv.Perm (Cantor X)} :
    a ∈ fragPieces H ↔ a ∈ roverNekrashevych X H ∧
      ∃ p q : List X, p.length = 4 ∧ q.length = 4 ∧ SupportedIn a (cone p ∪ cone q) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.mem_fragPieces

theorem fragPieces_inv {H : Subgroup (TreeAut X)} {a : Equiv.Perm (Cantor X)}
    (ha : a ∈ fragPieces H) : a⁻¹ ∈ fragPieces H := by
  obtain ⟨hG, p, q, hp, hq, hs⟩ := mem_fragPieces.mp ha
  exact mem_fragPieces.mpr ⟨(roverNekrashevych X H).inv_mem hG, p, q, hp, hq, hs.inv⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.fragPieces_inv

theorem fragPieces_of_long {H : Subgroup (TreeAut X)} {a : Equiv.Perm (Cantor X)}
    (hG : a ∈ roverNekrashevych X H) {p q : List X} (hp : 4 ≤ p.length) (hq : 4 ≤ q.length)
    (hs : SupportedIn a (cone p ∪ cone q)) : a ∈ fragPieces H :=
  mem_fragPieces.mpr ⟨hG, p.take 4, q.take 4, by rw [List.length_take]; omega,
    by rw [List.length_take]; omega,
    hs.mono (Set.union_subset_union (cone_subset_of_prefix (List.take_prefix 4 p))
      (cone_subset_of_prefix (List.take_prefix 4 q)))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.fragPieces_of_long

/-- **Pairs of pieces** are jointly supported in a set missing a cone. -/
theorem frag_pair [Nontrivial X] {H : Subgroup (TreeAut X)} {a b : Equiv.Perm (Cantor X)}
    (ha : a ∈ fragPieces H) (hb : b ∈ fragPieces H) :
    ∃ S, MissesCone S ∧ SupportedIn a S ∧ SupportedIn b S := by
  obtain ⟨-, p, q, hp, hq, hpq⟩ := mem_fragPieces.mp ha
  obtain ⟨-, r, s, hr, hs, hrs⟩ := mem_fragPieces.mp hb
  obtain ⟨t, ht, htp, htq, htr, hts⟩ := frag_exists_word_ne p q r s
  have hd : ∀ v : List X, v.length = 4 → t ≠ v → Disjoint (cone v) (cone t) :=
    fun v hv hne => disjoint_cone_of_length_eq (hv.trans ht.symm) (Ne.symm hne)
  refine ⟨(cone p ∪ cone q) ∪ (cone r ∪ cone s), ⟨t, ?_⟩, hpq.mono Set.subset_union_left,
    hrs.mono Set.subset_union_right⟩
  exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hd p hp htp, hd q hq htq⟩,
    Set.disjoint_union_left.mpr ⟨hd r hr htr, hd s hs hts⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_pair

/-- `V_X(H)` is stable under acting inside a cone. -/
theorem frag_localize_mem (H : Subgroup (TreeAut X)) (t : List X) {g : Equiv.Perm (Cantor X)}
    (hg : g ∈ roverNekrashevych X H) : localize t g ∈ roverNekrashevych X H := by
  have hle : roverNekrashevych X H ≤ (roverNekrashevych X H).comap (localize t) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro f hf
    rcases hf with hf | ⟨w, h, hh, rfl⟩
    · exact higmanThompsonV_le_rn H (localize_mem_higmanThompsonV hf t)
    · show localize t (localize w (cantorHom h)) ∈ roverNekrashevych X H
      rw [← localize_append]
      exact localize_mem_roverNekrashevych H (t ++ w) hh
  exact hle hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_localize_mem

theorem frag_localize_mem_pieces (H : Subgroup (TreeAut X)) {u : List X} (hu : u.length = 4)
    {e : Equiv.Perm (Cantor X)} (he : e ∈ roverNekrashevych X H) :
    localize u e ∈ fragPieces H :=
  mem_fragPieces.mpr ⟨frag_localize_mem H u he, u, u, hu, hu,
    (localize_supportedIn u e).mono Set.subset_union_left⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_localize_mem_pieces

theorem frag_closure_le (H : Subgroup (TreeAut X)) :
    Subgroup.closure (fragPieces H) ≤ roverNekrashevych X H :=
  (Subgroup.closure_le _).mpr fun _ ha => (mem_fragPieces.mp ha).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_closure_le

/-- Members of the closure of the pieces are products of pieces. -/
theorem frag_exists_list {H : Subgroup (TreeAut X)} {g : Equiv.Perm (Cantor X)}
    (hg : g ∈ Subgroup.closure (fragPieces H)) :
    ∃ l : List (Equiv.Perm (Cantor X)), (∀ a ∈ l, a ∈ fragPieces H) ∧ l.prod = g := by
  have h : g ∈ (Subgroup.closure (fragPieces H)).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid] at h
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure h
  refine ⟨l, fun a ha => ?_, hprod⟩
  rcases hl a ha with h1 | h1
  · exact h1
  · have h2 : a⁻¹ ∈ fragPieces H := h1
    have h3 := fragPieces_inv h2
    rwa [inv_inv] at h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_exists_list

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
