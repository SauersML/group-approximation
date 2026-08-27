import GroupApproximation.Kazhdan.ExactHodgeCertificate
import GroupApproximation.GroupTheory.PresentedGroupRelatorReplay

/-!
# Fox boundaries of literal signed words

This file gives the elementary Fox identity needed by exact Hodge
certificates.  It is deliberately stated for a literal signed word and an
arbitrary group-valued generator tuple.  Thus the proof is independent of a
presentation and contains no word-problem assumption.
-/

namespace GroupApproximation
namespace FoxBoundary

open ExactHodgeCertificate PresentedGroupRelatorReplay
open scoped BigOperators MonoidAlgebra

universe u v

variable {Generator : Type u} {G : Type v} [Group G]

/-- The group element represented by a literal signed letter. -/
def letterValue (s : Generator → G) (letter : Generator × Bool) : G :=
  if letter.2 then s letter.1 else (s letter.1)⁻¹

/-- Evaluation of a literal signed word in a group-valued generator tuple. -/
def wordValue (s : Generator → G) (letters : SignedWord Generator) : G :=
  (letters.map (letterValue s)).prod

/-- Evaluating a signed word after a free-group homomorphism agrees with
mapping the native free-group word. -/
@[simp] theorem wordValue_freeGroup_map
    (f : FreeGroup Generator →* G) (letters : SignedWord Generator) :
    wordValue (fun i ↦ f (FreeGroup.of i)) letters = f (word letters) := by
  induction letters with
  | nil =>
      change 1 = f 1
      simp
  | cons letter rest ih =>
      rcases letter with ⟨generator, positive⟩
      cases positive
      · change (f (FreeGroup.of generator))⁻¹ *
          wordValue (fun i ↦ f (FreeGroup.of i)) rest =
            f ((FreeGroup.of generator)⁻¹ * word rest)
        rw [ih, map_mul, map_inv]
      · change f (FreeGroup.of generator) *
          wordValue (fun i ↦ f (FreeGroup.of i)) rest =
            f (FreeGroup.of generator * word rest)
        rw [ih, map_mul]

/-- Fox boundary of a signed word, starting after an already traversed
prefix.  Positive letters contribute the old prefix and inverse letters
contribute minus the new prefix. -/
noncomputable def boundaryFrom [DecidableEq Generator]
    (s : Generator → G) :
    G → SignedWord Generator → Generator → RatGroupRing G
  | _, [], _ => 0
  | initial, (generator, positive) :: rest, i =>
      let next := initial * letterValue s (generator, positive)
      (if i = generator then
          if positive then MonoidAlgebra.single initial 1
          else -MonoidAlgebra.single next 1
        else 0) + boundaryFrom s next rest i

/-- Fox boundary at the identity prefix. -/
noncomputable def boundary [DecidableEq Generator]
    (s : Generator → G) (letters : SignedWord Generator) :
    Generator → RatGroupRing G :=
  boundaryFrom s 1 letters

/-- The fundamental Fox telescoping identity with an arbitrary initial
prefix. -/
theorem sum_boundaryFrom_mul_coboundary [Fintype Generator]
    [DecidableEq Generator]
    (s : Generator → G) (initial : G) (letters : SignedWord Generator) :
    ∑ i, boundaryFrom s initial letters i * generatorCoboundary s i =
      MonoidAlgebra.single (initial * wordValue s letters) 1 -
        MonoidAlgebra.single initial 1 := by
  induction letters generalizing initial with
  | nil =>
      simp [boundaryFrom, wordValue]
  | cons letter rest ih =>
      rcases letter with ⟨generator, positive⟩
      classical
      simp only [boundaryFrom]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_eq_single generator]
      · rw [ih]
        have hstep :
            (if positive then MonoidAlgebra.single initial 1
              else -MonoidAlgebra.single
                (initial * letterValue s (generator, positive)) 1) *
                generatorCoboundary s generator =
              MonoidAlgebra.single
                  (initial * letterValue s (generator, positive)) 1 -
                MonoidAlgebra.single initial 1 := by
          cases positive
          · simp [letterValue, generatorCoboundary,
              MonoidAlgebra.one_def, mul_sub]
            abel
          · simp [letterValue, generatorCoboundary,
              MonoidAlgebra.one_def, mul_sub]
        simp only [if_pos]
        rw [hstep]
        simp only [wordValue, List.map_cons, List.prod_cons]
        rw [mul_assoc]
        abel
      · intro i _ hi
        simp [hi]
      · simp

/-- The fundamental Fox identity at the identity prefix. -/
theorem sum_boundary_mul_coboundary [Fintype Generator]
    [DecidableEq Generator]
    (s : Generator → G) (letters : SignedWord Generator) :
    ∑ i, boundary s letters i * generatorCoboundary s i =
      MonoidAlgebra.single (wordValue s letters) 1 - 1 := by
  simpa [boundary, MonoidAlgebra.one_def] using
    sum_boundaryFrom_mul_coboundary s 1 letters

end FoxBoundary
end GroupApproximation
