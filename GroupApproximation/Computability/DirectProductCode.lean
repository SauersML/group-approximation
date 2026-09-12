import GroupApproximation.Computability.FreeEdgeTowerCode

/-!
# A primitive-recursive code for direct products

The rope presentation in `Higman.RopeTrick` has a direct product between its
two HNN layers.  `CoprodCode` supplies the free-product syntax, but there was
no corresponding raw constructor for a direct product.  This file adds that
constructor by appending the finite rectangular family of commutators between
the two displayed generator alphabets.

Every definition is list surgery on `PresentationCode`; no group-theoretic
injectivity, embedding, or permanence input occurs here.  The semantic
identification with a direct product is deliberately a separate obligation.
-/

namespace GroupApproximation
namespace DirectProductCode

open PresentationCodes RawTransform RawTransformPrimrec

/-- A raw word in the concrete finite-presentation encoding. -/
abbrev Raw : Type := List (ℕ × Bool)

/-- Normalize a left-factor word before putting it in the sum alphabet. -/
def leftWord (c : PresentationCode) (w : Raw) : Raw :=
  w.map fun p => (p.1 % genCount c, p.2)

/-- Shift a normalized right-factor word past the left alphabet. -/
def rightWord (c d : PresentationCode) (w : Raw) : Raw :=
  w.map fun p => (genCount c + p.1 % genCount d, p.2)

/-- The commutator of the `i`-th left and `j`-th right generators. -/
def commutatorWord (c : PresentationCode) (i j : ℕ) : Raw :=
  [(i, true), (genCount c + j, true),
    (i, false), (genCount c + j, false)]

/-- One row of the rectangular commutator family. -/
def commutatorRow (c d : PresentationCode) (i : ℕ) : List Raw :=
  (List.range (genCount d)).map (commutatorWord c i)

/-- All cross-factor commutators, in row-major order. -/
def commutatorWords (c d : PresentationCode) : List Raw :=
  ((List.range (genCount c)).map (commutatorRow c d)).flatten

/-- The raw relator list of the direct-product presentation. -/
def productWords (c d : PresentationCode) : List Raw :=
  c.2.map (leftWord c) ++ d.2.map (rightWord c d) ++ commutatorWords c d

/-- **The direct-product presentation code.**  The two alphabets are placed
consecutively and every cross commutator is appended. -/
def productCode (c d : PresentationCode) : PresentationCode :=
  (genCount c + d.1, productWords c d)

@[simp] theorem productCode_genCount (c d : PresentationCode) :
    genCount (productCode c d) = genCount c + genCount d := by
  simp only [productCode, genCount]
  omega

@[simp] theorem productCode_relators (c d : PresentationCode) :
    (productCode c d).2 = productWords c d := rfl

/-! ## Primitive recursiveness -/

theorem primrec_leftWord :
    Primrec₂ (fun (c : PresentationCode) (w : Raw) => leftWord c w) :=
  primrec_normWord

theorem primrec_rightWord :
    Primrec (fun a : (PresentationCode × PresentationCode) × Raw =>
      rightWord a.1.1 a.1.2 a.2) := by
  have hgenC : Primrec (fun a : (PresentationCode × PresentationCode) × Raw =>
      genCount a.1.1) :=
    primrec_genCount.comp (Primrec.fst.comp Primrec.fst)
  have hgenD : Primrec (fun a : (PresentationCode × PresentationCode) × Raw =>
      genCount a.1.2) :=
    primrec_genCount.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map Primrec.snd
    (Primrec.pair
      (Primrec₂.comp Primrec.nat_add (hgenC.comp Primrec.fst)
        (Primrec₂.comp Primrec.nat_mod (Primrec.fst.comp Primrec.snd)
          (hgenD.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_commutatorWord :
    Primrec (fun a : (PresentationCode × PresentationCode) × (ℕ × ℕ) =>
      commutatorWord a.1.1 a.2.1 a.2.2) := by
  have hi : Primrec
      (fun a : (PresentationCode × PresentationCode) × (ℕ × ℕ) => a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hj : Primrec
      (fun a : (PresentationCode × PresentationCode) × (ℕ × ℕ) => a.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hright : Primrec
      (fun a : (PresentationCode × PresentationCode) × (ℕ × ℕ) =>
        genCount a.1.1 + a.2.2) :=
    Primrec₂.comp Primrec.nat_add
      (primrec_genCount.comp (Primrec.fst.comp Primrec.fst)) hj
  exact Primrec₂.comp Primrec.list_cons
    (Primrec.pair hi (Primrec.const true))
    (Primrec₂.comp Primrec.list_cons
      (Primrec.pair hright (Primrec.const true))
      (Primrec₂.comp Primrec.list_cons
        (Primrec.pair hi (Primrec.const false))
        (Primrec₂.comp Primrec.list_cons
          (Primrec.pair hright (Primrec.const false))
          (Primrec.const []))))

theorem primrec_commutatorWords :
    Primrec (fun a : PresentationCode × PresentationCode =>
      commutatorWords a.1 a.2) := by
  have hrow : Primrec
      (fun a : (PresentationCode × PresentationCode) × ℕ =>
        commutatorRow a.1.1 a.1.2 a.2) := by
    have hrange : Primrec
        (fun a : (PresentationCode × PresentationCode) × ℕ =>
          List.range (genCount a.1.2)) :=
      Primrec.list_range.comp
        (primrec_genCount.comp (Primrec.snd.comp Primrec.fst))
    have hword : Primrec
        (fun a : ((PresentationCode × PresentationCode) × ℕ) × ℕ =>
          commutatorWord a.1.1.1 a.1.2 a.2) :=
      primrec_commutatorWord.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
    exact Primrec.list_map hrange hword
  have hrows : Primrec
      (fun a : PresentationCode × PresentationCode =>
        (List.range (genCount a.1)).map (commutatorRow a.1 a.2)) :=
    Primrec.list_map
      (Primrec.list_range.comp (primrec_genCount.comp Primrec.fst)) hrow
  exact Primrec.list_flatten.comp hrows

theorem primrec_productWords :
    Primrec (fun a : PresentationCode × PresentationCode =>
      productWords a.1 a.2) := by
  have hleft : Primrec (fun a : PresentationCode × PresentationCode =>
      a.1.2.map (leftWord a.1)) :=
    primrec_leftWords.comp Primrec.fst
  have hright : Primrec (fun a : PresentationCode × PresentationCode =>
      a.2.2.map (rightWord a.1 a.2)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) primrec_rightWord
  have hfactorWords : Primrec (fun a : PresentationCode × PresentationCode =>
      a.1.2.map (leftWord a.1) ++ a.2.2.map (rightWord a.1 a.2)) :=
    Primrec₂.comp Primrec.list_append hleft hright
  have hall : Primrec (fun a : PresentationCode × PresentationCode =>
      (a.1.2.map (leftWord a.1) ++ a.2.2.map (rightWord a.1 a.2)) ++
        commutatorWords a.1 a.2) :=
    Primrec₂.comp Primrec.list_append hfactorWords primrec_commutatorWords
  exact hall.of_eq fun _ => rfl

/-- Computing the direct-product presentation is primitive recursive. -/
theorem primrec_productCode :
    Primrec (fun a : PresentationCode × PresentationCode =>
      productCode a.1 a.2) :=
  Primrec.pair
    (Primrec₂.comp Primrec.nat_add
      (primrec_genCount.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    primrec_productWords

theorem computable_productCode :
    Computable (fun a : PresentationCode × PresentationCode =>
      productCode a.1 a.2) :=
  primrec_productCode.to_comp

end DirectProductCode
end GroupApproximation
