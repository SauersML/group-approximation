import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# A shortest admissible word for an element of a relative ball

`RelGenSet.relBall` is defined by a bounded existential: `h` lies in the ball of
radius `n` when *some* admissible word of length at most `n` spells it while
avoiding `Γ_{H_λ}`.  Nothing in the definition says the word is shortest, and for
most purposes nothing needs to.

Hull's proof of Lemma `ee` is one of the exceptions, and it is worth saying
exactly where, because the minimality is not a convenience there --- it is the
whole of one step.  The `E`-letter of the word has to be an **isolated**
component of the cycle, and isolation fails only if two `E`-components are
connected, meaning their endpoints differ by an element of `E`.  If that
happened, the segment between them could be replaced by the single `E`-letter
naming that difference, giving a shorter admissible word for the same element.
So isolation is exactly what minimality buys, and a ball membership on its own
does not buy it.

This module extracts the shortest word.  It is separated because it is reusable
and because it is checkable on its own: the statement mentions no geometry, and
nothing about it depends on what the word is later used for.

## The minimality is over ALL admissible words, not the short ones

The final clause quantifies over every `v` spelling `h` admissibly and avoiding
`Γ_{H_λ}`, with **no length bound**, and not merely over those of length at most
`n`.  That is deliberate and it is the form the isolation argument needs: the
replacement word produced by collapsing two connected components is short, but
proving it is at most `n` before knowing it is shorter than `w` would be
circular.  The `≤ n` clause is kept as well, since `Nat.find` cannot exceed the
length of the witness the ball membership already provides.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section MinimalWord

variable {G : Type u} [Group G] {Λ : Type w}

/-- **An element of a relative ball is spelled by a shortest admissible word.**

The first four clauses repeat what the ball membership already gives; the fifth
is the point.  `Nat.find` over the set of achievable lengths supplies both: the
witness at the minimum, and minimality against every competitor. -/
theorem exists_minimal_word_of_mem_relBall {D : RelGenSet G Λ} {lam : Λ} {n : ℕ}
    {h : G} (hh : h ∈ D.relBall lam n) :
    ∃ w : List (RelLetter G Λ),
      (∀ a ∈ w, D.IsLetter a) ∧ RelLetter.listVal w = h ∧
        AvoidsFrom D.fam lam w 1 ∧ w.length ≤ n ∧
          ∀ v : List (RelLetter G Λ), (∀ a ∈ v, D.IsLetter a) →
            RelLetter.listVal v = h → AvoidsFrom D.fam lam v 1 →
              w.length ≤ v.length := by
  classical
  obtain ⟨-, w₀, hlet₀, hval₀, hav₀, hlen₀⟩ := hh
  have hP : ∃ k : ℕ, ∃ w : List (RelLetter G Λ),
      (∀ a ∈ w, D.IsLetter a) ∧ RelLetter.listVal w = h ∧
        AvoidsFrom D.fam lam w 1 ∧ w.length = k :=
    ⟨w₀.length, w₀, hlet₀, hval₀, hav₀, rfl⟩
  obtain ⟨w, hlet, hval, hav, hlenw⟩ := Nat.find_spec hP
  refine ⟨w, hlet, hval, hav, ?_, ?_⟩
  · have hmin : Nat.find hP ≤ w₀.length :=
      Nat.find_min' hP ⟨w₀, hlet₀, hval₀, hav₀, rfl⟩
    omega
  · intro v hletv hvalv havv
    have hmin : Nat.find hP ≤ v.length :=
      Nat.find_min' hP ⟨v, hletv, hvalv, havv, rfl⟩
    omega

/-- **The shortest word still lands in the ball it came from.**  Stated because
the isolation argument reads the word both as a path and as a ball witness, and
rebuilding the membership each time obscures which of the two is in play. -/
theorem mem_relBall_of_minimal_word {D : RelGenSet G Λ} {lam : Λ} {n : ℕ}
    {h : G} (hfam : h ∈ D.fam lam) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom D.fam lam w 1) (hlen : w.length ≤ n) :
    h ∈ D.relBall lam n :=
  ⟨hfam, w, hlet, hval, hav, hlen⟩

end MinimalWord

end GGT
end GroupApproximation
