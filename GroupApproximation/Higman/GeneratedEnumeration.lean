import GroupApproximation.Higman.TheoremFour
import GroupApproximation.Higman.REPredNormalForm

/-!
# Higman's Lemma 2.8: a total computable enumeration

Higman's Section 2 reaches an arbitrary recursively enumerable subset of the
sequence space only at its last step, and the object it needs there is not the
bare hypothesis but an *enumeration*: a total recursive family whose members are
exactly the elements of the set.  That is his Lemma 2.8.

## The statement, and the hypothesis Higman omits

As printed (p.463) Lemma 2.8 carries no hypothesis on `X`.  It is false for
`X = ∅`: clause (ii) makes each column `f(·,r)` finitely supported, hence an
element of the sequence space, and clause (i) instantiated at `g = f(·,0)` then
puts that column in `X`.  The gap is in his proof, which takes a recursive `h`
enumerating the indices of members of `X` — the classical fact that a *nonempty*
recursively enumerable set is the range of a total recursive function.  So the
hypothesis is used but never stated, and `B.Nonempty` is restored here.

Nothing is lost: the empty case is discharged before this lemma is ever reached,
by `Seq.higmanGenerated_empty` (`Higman/GeneratedBasic.lean`), since `Z` and `S`
are disjoint.

## Why the proof here is not Higman's

Higman proves 2.8 by Gödel prime-power coding: `r + 1 = ∏ pₙ^{g(n,r)}`, a
pairing `k` of the naturals with the integers, and the closed-form bounds
`a(r) = -r`, `b(r) = r`.  None of that is needed in Lean.  The repository
already has Kleene normal form for recursively enumerable predicates
(`exists_primrec_of_rePred`), and the sequence space is `ℤ →₀ ℤ`, so the finite
support of clause (ii) is part of the type rather than something to arrange.
What remains is the classical dovetailing argument: decode the index into a
code/step pair, keep the code when the search succeeds at that step, and fall
back on a fixed member otherwise.  That fallback is exactly where nonemptiness
is spent.

Clause (ii)'s explicit bounds are therefore not part of this statement.  When
the octuple construction needs `a(r)` and `b(r)`, they are the least and
greatest indices occurring in the list `c r`, computable from it directly.

## Reference

Higman 1961, Lemma 2.8 — stated there without the hypothesis `X ≠ ∅`, which his
proof uses when it takes `X` to be the range of a total recursive function.
Mikaelian's rewriting of the embedding theorem does not restate Section 2, so
there is no cleaner published form to follow.
-/

namespace GroupApproximation
namespace Higman

/-- **Lemma 2.8.**  A nonempty recursively enumerable subset of the sequence
space is the exact set of values of a total computable enumeration by codes. -/
theorem exists_computable_enumeration {B : Set Seq.E} (hB : REset B)
    (hne : B.Nonempty) :
    ∃ c : ℕ → List (ℤ × ℤ), Computable c ∧
      ∀ g : Seq.E, g ∈ B ↔ ∃ r : ℕ, seqOfList (c r) = g := by
  classical
  obtain ⟨F, hF, hspec⟩ := exists_primrec_of_rePred hB
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨l₀, hl₀⟩ := seqOfList_surjective g₀
  -- the dovetailed enumeration: decode an index into a code/step pair
  set dec : ℕ → List (ℤ × ℤ) × ℕ := fun k =>
    (Encodable.decode (α := List (ℤ × ℤ) × ℕ) k).getD (l₀, 0) with hdec_def
  refine ⟨fun k => cond (F (dec k).1 (dec k).2) (dec k).1 l₀, ?_, ?_⟩
  · have hdec : Primrec dec :=
      Primrec.option_getD.comp Primrec.decode (Primrec.const (l₀, 0))
    have h1 : Primrec fun k : ℕ => (dec k).1 := Primrec.fst.comp hdec
    have h2 : Primrec fun k : ℕ => (dec k).2 := Primrec.snd.comp hdec
    exact (Primrec.cond (hF.comp h1 h2) h1 (Primrec.const l₀)).to_comp
  · intro g
    constructor
    · intro hg
      obtain ⟨l, hl⟩ := seqOfList_surjective g
      have hmem : seqOfList l ∈ B := by rw [hl]; exact hg
      obtain ⟨n, hn⟩ := (hspec l).mp hmem
      refine ⟨Encodable.encode (l, n), ?_⟩
      have hdk : dec (Encodable.encode (l, n)) = (l, n) := by
        simp [hdec_def]
      simp only [hdk, hn, cond_true]
      exact hl
    · rintro ⟨r, hr⟩
      have hr' : seqOfList (cond (F (dec r).1 (dec r).2) (dec r).1 l₀) = g := hr
      rcases hcase : F (dec r).1 (dec r).2 with _ | _
      · rw [hcase] at hr'
        simp only [cond_false] at hr'
        rw [← hr', hl₀]
        exact hg₀
      · rw [hcase] at hr'
        simp only [cond_true] at hr'
        rw [← hr']
        exact (hspec (dec r).1).mpr ⟨(dec r).2, hcase⟩

end Higman
end GroupApproximation
