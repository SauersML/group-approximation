import GroupApproximation.Computability.DirectProductCode

/-!
# Primitive-recursive finite codes for amalgam presentations

Given finite presentations for two factors and a finite list of word pairs
`(uᵢ,vᵢ)`, this module emits the standard presentation of their free product
with relations `uᵢ=vᵢ`.  This is the raw syntactic operation used by
`BenignWitness.mapEmb`: its edge group is only required to be finitely
generated, so the displayed pairs are precisely the finite data needed by the
amalgamated-product presentation.

Semantic identification with a particular pushout is deliberately separate;
it requires the caller to prove that the displayed pairs generate the glued
subgroup and spell the two embedding maps.
-/

namespace GroupApproximation
namespace AmalgamCode

open PresentationCodes DirectProductCode RawTransformPrimrec RawWord

abbrev Raw : Type := List (ℕ × Bool)

/-- The two factor presentations on their consecutive alphabets. -/
def factorWords (c d : PresentationCode) : List Raw :=
  c.2.map (leftWord c) ++ d.2.map (rightWord c d)

/-- One displayed identification `u=v`, written as `u v⁻¹`. -/
def amalgamRelator (c d : PresentationCode) (p : Raw × Raw) : Raw :=
  leftWord c p.1 ++ invWord (rightWord c d p.2)

/-- The presentation of the free product of `c` and `d`, quotiented by the
finite displayed identifications. -/
def amalgamCode (c d : PresentationCode) (edges : List (Raw × Raw)) :
    PresentationCode :=
  (genCount c + d.1,
    factorWords c d ++ edges.map (amalgamRelator c d))

@[simp] theorem amalgamCode_genCount (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    genCount (amalgamCode c d edges) = genCount c + genCount d := by
  simp only [amalgamCode, genCount]
  omega

@[simp] theorem amalgamCode_relators (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    (amalgamCode c d edges).2 =
      factorWords c d ++ edges.map (amalgamRelator c d) := rfl

/-! ## Primitive recursiveness -/

theorem primrec_factorWords :
    Primrec (fun a : PresentationCode × PresentationCode =>
      factorWords a.1 a.2) := by
  have hleft : Primrec (fun a : PresentationCode × PresentationCode =>
      a.1.2.map (leftWord a.1)) :=
    primrec_leftWords.comp Primrec.fst
  have hright : Primrec (fun a : PresentationCode × PresentationCode =>
      a.2.2.map (rightWord a.1 a.2)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) primrec_rightWord
  exact Primrec.list_append.comp hleft hright

theorem primrec_amalgamRelator :
    Primrec (fun a : (PresentationCode × PresentationCode) × (Raw × Raw) =>
      amalgamRelator a.1.1 a.1.2 a.2) := by
  have hleft : Primrec
      (fun a : (PresentationCode × PresentationCode) × (Raw × Raw) =>
        leftWord a.1.1 a.2.1) :=
    Primrec₂.comp primrec_leftWord
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hright : Primrec
      (fun a : (PresentationCode × PresentationCode) × (Raw × Raw) =>
        rightWord a.1.1 a.1.2 a.2.2) :=
    primrec_rightWord.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_append.comp hleft (primrec_invWord.comp hright)

abbrev Input : Type :=
  (PresentationCode × PresentationCode) × List (Raw × Raw)

theorem primrec_amalgamRelators :
    Primrec (fun a : Input =>
      a.2.map (amalgamRelator a.1.1 a.1.2)) :=
  Primrec.list_map Primrec.snd
    (primrec_amalgamRelator.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))

theorem primrec_amalgamCode :
    Primrec (fun a : Input => amalgamCode a.1.1 a.1.2 a.2) := by
  have hcount : Primrec (fun a : Input => genCount a.1.1 + a.1.2.1) :=
    Primrec₂.comp Primrec.nat_add
      (primrec_genCount.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hfactor : Primrec (fun a : Input => factorWords a.1.1 a.1.2) :=
    primrec_factorWords.comp Primrec.fst
  exact Primrec.pair hcount
    (Primrec.list_append.comp hfactor primrec_amalgamRelators)

theorem computable_amalgamCode :
    Computable (fun a : Input => amalgamCode a.1.1 a.1.2 a.2) :=
  primrec_amalgamCode.to_comp

end AmalgamCode
end GroupApproximation
