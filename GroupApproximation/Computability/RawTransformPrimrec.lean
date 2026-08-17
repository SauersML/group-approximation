import GroupApproximation.Computability.RawTransform
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

/-!
# The transformation is computable

`RawTransform.rawTransform` builds its output code by list surgery alone, so
unlike the `codeOfList` form it is within reach of Mathlib's `Primrec` API.
This file carries it there.

Everything is assembled from four operations --- `List.map`, `List.range`,
append, and arithmetic on `ℕ` --- so every step is one of `Primrec.list_map`,
`Primrec.list_range`, `Primrec.list_append`, `Primrec.nat_add`,
`Primrec.nat_mod`, or a projection.  The one case split is `invSWord`, which
distinguishes `s₀ = s` from `sᵢ₊₁ = s xᵢ`, and that is `Primrec.nat_casesOn`.

The second code is a parameter rather than the fixed forbidden one: fixing it
would make the statement mention a constant obtained by choice, and there is no
reason to.  A constant is computable whatever produced it, so specialising
costs nothing.
-/

namespace GroupApproximation
namespace RawTransformPrimrec

open PresentationCodes RawTransform RawWord CoprodCode

variable (d : PresentationCode)

/-! ## Arithmetic -/

theorem primrec_genCount : Primrec (fun c : PresentationCode => genCount c) :=
  Primrec.succ.comp Primrec.fst

theorem primrec_srcCount : Primrec (fun c : PresentationCode => srcCount c d) := by
  show Primrec fun c : PresentationCode => genCount c + genCount d
  exact Primrec₂.comp Primrec.nat_add primrec_genCount (Primrec.const (genCount d))

theorem primrec_idxE (k : ℕ) : Primrec (fun c : PresentationCode => idxE c d k) :=
  Primrec₂.comp Primrec.nat_add
    (Primrec₂.comp Primrec.nat_add (primrec_srcCount d)
      (Primrec₂.comp Primrec.nat_add (primrec_srcCount d) (Primrec.const 1)))
    (Primrec.const k)

/-! ## The word-level operations -/

theorem primrec_normWord :
    Primrec₂ (fun (c : PresentationCode) (u : List (ℕ × Bool)) => normWord c u) :=
  Primrec.list_map Primrec.snd
    (Primrec.pair
      (Primrec₂.comp Primrec.nat_mod (Primrec.fst.comp Primrec.snd)
        (primrec_genCount.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_invWord :
    Primrec (fun u : List (ℕ × Bool) => invWord u) :=
  Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.dom_bool (fun b => !b) |>.comp (Primrec.snd.comp Primrec.snd))))

/-! ## The four families -/

theorem primrec_leftWords :
    Primrec (fun c : PresentationCode => leftWords c) :=
  Primrec.list_map (Primrec.snd.comp Primrec.id)
    (primrec_normWord)

theorem primrec_rightWords :
    Primrec (fun c : PresentationCode => rightWords c d) :=
  Primrec.list_map (Primrec.const d.2)
    (Primrec.list_map Primrec.snd
      (Primrec.pair
        (Primrec₂.comp Primrec.nat_add
          (primrec_genCount.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.comp Primrec.nat_mod (Primrec.fst.comp Primrec.snd)
            (Primrec.const (genCount d))))
        (Primrec.snd.comp Primrec.snd)))

theorem primrec_invSWord :
    Primrec₂ (fun (c : PresentationCode) (j : ℕ) => invSWord c d j) := by
  have h : Primrec fun a : PresentationCode × ℕ =>
      (Nat.casesOn a.2 [((idxE a.1 d 0), false)]
        (fun i => [(i, false), ((idxE a.1 d 0), false)]) : List (ℕ × Bool)) := by
    refine Primrec.nat_casesOn Primrec.snd ?_ ?_
    · exact Primrec₂.comp Primrec.list_cons
        (Primrec.pair ((primrec_idxE d 0).comp Primrec.fst) (Primrec.const false))
        (Primrec.const [])
    · exact Primrec₂.comp Primrec.list_cons
        (Primrec.pair Primrec.snd (Primrec.const false))
        (Primrec₂.comp Primrec.list_cons
          (Primrec.pair ((primrec_idxE d 0).comp (Primrec.fst.comp Primrec.fst))
            (Primrec.const false))
          (Primrec.const []))
  refine h.of_eq fun a => ?_
  obtain ⟨c, j⟩ := a
  cases j <;> rfl

theorem primrec_outIdx : Primrec (fun c : PresentationCode => outIdx c d) := by
  show Primrec fun c : PresentationCode => srcCount c d + (srcCount c d + 5)
  exact Primrec₂.comp Primrec.nat_add (primrec_srcCount d)
    (Primrec₂.comp Primrec.nat_add (primrec_srcCount d) (Primrec.const 5))

theorem primrec_idxT :
    Primrec₂ (fun (c : PresentationCode) (j : ℕ) => idxT c d j) := by
  show Primrec fun a : PresentationCode × ℕ => srcCount a.1 d + a.2
  exact Primrec₂.comp Primrec.nat_add ((primrec_srcCount d).comp Primrec.fst) Primrec.snd

theorem primrec_killWord :
    Primrec₂ (fun (c : PresentationCode) (j : ℕ) => killWord c d j) :=
  Primrec₂.comp Primrec.list_cons
    (Primrec.pair ((primrec_idxE d 1).comp Primrec.fst) (Primrec.const true))
    (Primrec₂.comp Primrec.list_cons
      (Primrec.pair (primrec_idxT d)
        (Primrec.const true))
      (Primrec₂.comp Primrec.list_cons
        (Primrec.pair ((primrec_idxE d 1).comp Primrec.fst) (Primrec.const false))
        (Primrec₂.comp Primrec.list_append
          (primrec_invSWord d)
          (Primrec₂.comp Primrec.list_cons
            (Primrec.pair (primrec_idxT d)
              (Primrec.const false))
            (Primrec.const [])))))

theorem primrec_kills :
    Primrec (fun c : PresentationCode =>
      (List.range (srcCount c d + 1)).map (killWord c d)) :=
  Primrec.list_map
    (Primrec.list_range.comp
      (Primrec₂.comp Primrec.nat_add (primrec_srcCount d) (Primrec.const 1)))
    (primrec_killWord d)

theorem primrec_zWord :
    Primrec₂ (fun (c : PresentationCode) (w : List (ℕ × Bool)) => zWord c d w) :=
  Primrec₂.comp Primrec.list_append
    (primrec_normWord)
    (Primrec₂.comp Primrec.list_cons
      (Primrec.pair ((primrec_idxE d 0).comp Primrec.fst) (Primrec.const true))
      (Primrec₂.comp Primrec.list_append
        (primrec_invWord.comp (primrec_normWord))
        (Primrec₂.comp Primrec.list_cons
          (Primrec.pair ((primrec_idxE d 0).comp Primrec.fst) (Primrec.const false))
          (Primrec.const []))))

/-- A cascade relator whose letters are fixed offsets: read a constant list of
offsets through `idxE`. -/
theorem primrec_offsets (L : List (ℕ × Bool)) :
    Primrec (fun c : PresentationCode => L.map (fun q => (idxE c d q.1, q.2))) :=
  Primrec.list_map (Primrec.const L)
    (Primrec.pair
      (Primrec₂.comp Primrec.nat_add
        (Primrec₂.comp Primrec.nat_add ((primrec_srcCount d).comp Primrec.fst)
          (Primrec₂.comp Primrec.nat_add ((primrec_srcCount d).comp Primrec.fst)
            (Primrec.const 1)))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_cascadeWords :
    Primrec₂ (fun (c : PresentationCode) (w : List (ℕ × Bool)) => cascadeWords c d w) := by
  have h1 : Primrec (fun c : PresentationCode =>
      [(idxE c d 2, true), (idxE c d 1, true), (idxE c d 2, false),
        (idxE c d 1, false), (idxE c d 1, false)]) :=
    (primrec_offsets d [(2, true), (1, true), (2, false), (1, false), (1, false)]).of_eq
      fun _ => rfl
  have h2 : Primrec (fun c : PresentationCode =>
      [(idxE c d 3, true), (idxE c d 2, true), (idxE c d 3, false),
        (idxE c d 2, false), (idxE c d 2, false)]) :=
    (primrec_offsets d [(3, true), (2, true), (3, false), (2, false), (2, false)]).of_eq
      fun _ => rfl
  have h3 : Primrec₂ (fun (c : PresentationCode) (w : List (ℕ × Bool)) =>
      (idxE c d 4, true) :: (zWord c d w ++ [(idxE c d 4, false), (idxE c d 3, false)])) :=
    Primrec₂.comp Primrec.list_cons
      (Primrec.pair ((primrec_idxE d 4).comp Primrec.fst) (Primrec.const true))
      (Primrec₂.comp Primrec.list_append
        (primrec_zWord d)
        (Primrec₂.comp Primrec.list_cons
          (Primrec.pair ((primrec_idxE d 4).comp Primrec.fst) (Primrec.const false))
          (Primrec₂.comp Primrec.list_cons
            (Primrec.pair ((primrec_idxE d 3).comp Primrec.fst) (Primrec.const false))
            (Primrec.const []))))
  exact Primrec₂.comp Primrec.list_cons (h1.comp Primrec.fst)
    (Primrec₂.comp Primrec.list_cons (h2.comp Primrec.fst)
      (Primrec₂.comp Primrec.list_cons h3 (Primrec.const [])))

theorem primrec_rawWords :
    Primrec₂ (fun (c : PresentationCode) (w : List (ℕ × Bool)) => rawWords c d w) :=
  Primrec₂.comp Primrec.list_append
    (Primrec₂.comp Primrec.list_append
      (Primrec₂.comp Primrec.list_append
        (primrec_leftWords.comp Primrec.fst)
        ((primrec_rightWords d).comp Primrec.fst))
      ((primrec_kills d).comp Primrec.fst))
    (primrec_cascadeWords d)

theorem primrec_rawTransform :
    Primrec₂ (fun (c : PresentationCode) (w : List (ℕ × Bool)) => rawTransform c d w) :=
  Primrec.pair ((primrec_outIdx d).comp Primrec.fst)
    (primrec_rawWords d)

/-- **The transformation is computable.** -/
theorem computable_rawTransform :
    Computable (fun x : PresentationCode × List (ℕ × Bool) => rawTransform x.1 d x.2) :=
  (primrec_rawTransform d).to_comp

end RawTransformPrimrec
end GroupApproximation
