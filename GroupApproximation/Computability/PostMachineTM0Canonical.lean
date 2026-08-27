import GroupApproximation.Computability.ListBlankCanonical
import GroupApproximation.Computability.PostMachineTM0

/-!
# Naming a TM0 configuration

`Computability.PostMachineTM0` identifies the machine simulated here with
Mathlib's `Turing.TM0`, and stops one step short of identifying
*configurations*.  A `Cfg` carries the written part of its tape as two raw
lists, while `Turing.Tape` carries two `Turing.ListBlank`s --- lists modulo
trailing blanks --- so `toTM0` is not injective: `[a]` and `[a, default]` are
different configurations with one image.  A TM0 run could therefore be pushed
forward but never pulled back to a *named* configuration, and the statements on
that side had to quantify existentially over "some configuration with the same
image" (`reaches_iff`, `exists_mk_eq_mk_of_reaches`).

The ambiguity is exactly the one `Computability.ListBlankCanonical` removes for
half-tapes, and this file spends that there: a configuration is `Canonical` when
neither written half ends in a blank.  Two facts close the gap.

* `toTM0_injOn_canonical`: distinct canonical configurations have distinct
  images, so a canonical `Cfg` is named by its TM0 image.
* `exists_canonical_cfg`: every TM0 configuration is the image of exactly one
  canonical configuration --- the missing pullback, and it is unique.

`normalize` deletes the trailing blanks from both halves, which moves no machine
(`toTM0_normalize`) because deleting them does not change the `ListBlank`.  With
it, `toTM0_eq_iff` measures precisely what `toTM0` collapses: two configurations
share an image exactly when they normalize to the same one, and nothing else is
identified.  Over an alphabet with decidable equality the pullback is computed
rather than chosen, by `ofTM0Cfg`, and `equivCanonical` is the resulting
bijection.

Existence and uniqueness need no decidable equality --- only `normalize` and
`ofTM0Cfg` do, since they compute a representative instead of asserting one.
-/

open Turing
open GroupApproximation.Turing

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

variable {Γ Λ : Type} [Inhabited Γ]

/-- A configuration is *canonical* when neither written half of its tape ends in
a blank.  The two halves are independent --- a machine reads them in opposite
directions --- so the condition is imposed on each separately, and the head
symbol is unconstrained: it is a genuine symbol of the tape, blank or not. -/
def Canonical (c : Cfg Γ Λ) : Prop :=
  NoTrailingBlank c.left ∧ NoTrailingBlank c.right

/-- **A canonical configuration is named by its TM0 image.**  Equality of the
images gives equality of the state, of the head symbol, and of the two
half-tapes *as `ListBlank`s*; on canonical configurations the last two upgrade
to equality of the underlying lists, which is the whole point of canonical
representatives. -/
theorem toTM0_injOn_canonical {c d : Cfg Γ Λ} (hc : Canonical c) (hd : Canonical d)
    (h : toTM0 c = toTM0 d) : c = d := by
  have hq : c.q = d.q := congrArg (fun X : TM0.Cfg Γ Λ => X.q) h
  have hh : c.head = d.head := congrArg (fun X : TM0.Cfg Γ Λ => X.Tape.head) h
  have hl : ListBlank.mk c.left = ListBlank.mk d.left :=
    congrArg (fun X : TM0.Cfg Γ Λ => X.Tape.left) h
  have hr : ListBlank.mk c.right = ListBlank.mk d.right :=
    congrArg (fun X : TM0.Cfg Γ Λ => X.Tape.right) h
  obtain ⟨cq, cl, ch, cr⟩ := c
  obtain ⟨dq, dl, dh, dr⟩ := d
  simp only [Cfg.mk.injEq]
  exact ⟨hq, mk_injOn hc.1 hd.1 hl, hh, mk_injOn hc.2 hd.2 hr⟩

/-- **Every TM0 configuration is the image of exactly one canonical
configuration.**  This is the pullback `toTM0` did not have: a TM0 run may now
be read back as a run through named configurations.  Existence is
`GroupApproximation.Turing.exists_canonical` applied to each half of the tape
separately, uniqueness is `toTM0_injOn_canonical`, and neither needs decidable
equality on the alphabet. -/
theorem exists_canonical_cfg (X : TM0.Cfg Γ Λ) :
    ∃! c : Cfg Γ Λ, Canonical c ∧ toTM0 c = X := by
  obtain ⟨q, ⟨a, L, R⟩⟩ := X
  obtain ⟨l, ⟨hl, hlL⟩, -⟩ := exists_canonical L
  obtain ⟨r, ⟨hr, hrR⟩, -⟩ := exists_canonical R
  have himg : toTM0 (⟨q, l, a, r⟩ : Cfg Γ Λ) = ⟨q, ⟨a, L, R⟩⟩ := by
    simp [toTM0, hlL, hrR]
  refine ⟨⟨q, l, a, r⟩, ⟨⟨hl, hr⟩, himg⟩, ?_⟩
  rintro c ⟨hc, hcX⟩
  exact toTM0_injOn_canonical hc ⟨hl, hr⟩ (hcX.trans himg.symm)

section Normalize

variable [DecidableEq Γ]

/-- Delete the trailing blanks from both written halves of the tape.  The state
and the head symbol are untouched: only the two lists carry the ambiguity. -/
def normalize (c : Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨c.q, trim c.left, c.head, trim c.right⟩

/-- Normalizing does not move the machine.  Nothing here is about the transition
function; deleting a trailing blank simply does not change the `ListBlank` a
list names. -/
@[simp] theorem toTM0_normalize (c : Cfg Γ Λ) : toTM0 (normalize c) = toTM0 c := by
  simp [toTM0, normalize, mk_trim]

/-- Normalizing lands in canonical configurations. -/
theorem canonical_normalize (c : Cfg Γ Λ) : Canonical (normalize c) :=
  ⟨noTrailingBlank_trim _, noTrailingBlank_trim _⟩

/-- A canonical configuration has nothing to normalize. -/
theorem normalize_eq_self_of_canonical {c : Cfg Γ Λ} (h : Canonical c) :
    normalize c = c := by
  show (⟨c.q, trim c.left, c.head, trim c.right⟩ : Cfg Γ Λ) = c
  rw [trim_eq_self h.1, trim_eq_self h.2]

/-- `normalize` is idempotent. -/
theorem normalize_normalize (c : Cfg Γ Λ) : normalize (normalize c) = normalize c :=
  normalize_eq_self_of_canonical (canonical_normalize c)

/-- **Exactly what `toTM0` collapses.**  Two configurations have the same TM0
image precisely when they normalize to the same configuration --- so the map
identifies trailing blanks and nothing else.  This is the sharp form of the
failure of injectivity, replacing the earlier statements that could only say
*some* configuration with the same image exists. -/
theorem toTM0_eq_iff (c d : Cfg Γ Λ) : toTM0 c = toTM0 d ↔ normalize c = normalize d := by
  constructor
  · intro h
    refine toTM0_injOn_canonical (canonical_normalize c) (canonical_normalize d) ?_
    rw [toTM0_normalize, toTM0_normalize, h]
  · intro h
    rw [← toTM0_normalize c, ← toTM0_normalize d, h]

/-- The canonical configuration named by a TM0 configuration, computed rather
than chosen: `GroupApproximation.Turing.toList` reads the canonical list off
each half of the tape. -/
def ofTM0Cfg (X : TM0.Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨X.q, toList X.Tape.left, X.Tape.head, toList X.Tape.right⟩

/-- `ofTM0Cfg` lands in canonical configurations. -/
theorem canonical_ofTM0Cfg (X : TM0.Cfg Γ Λ) : Canonical (ofTM0Cfg X) :=
  ⟨noTrailingBlank_toList _, noTrailingBlank_toList _⟩

/-- `ofTM0Cfg` is a section of `toTM0`: the configuration it names has the TM0
configuration it was read from as its image. -/
@[simp] theorem toTM0_ofTM0Cfg (X : TM0.Cfg Γ Λ) : toTM0 (ofTM0Cfg X) = X := by
  obtain ⟨q, ⟨a, L, R⟩⟩ := X
  simp [toTM0, ofTM0Cfg]

/-- Going to a TM0 configuration and back is normalization: the round trip
forgets exactly the trailing blanks. -/
@[simp] theorem ofTM0Cfg_toTM0 (c : Cfg Γ Λ) : ofTM0Cfg (toTM0 c) = normalize c :=
  (normalize_eq_self_of_canonical (canonical_ofTM0Cfg (toTM0 c))).symm.trans
    ((toTM0_eq_iff _ _).mp (toTM0_ofTM0Cfg (toTM0 c)))

/-- **Canonical configurations are the TM0 configurations.**  The identification
the file exists for, as an explicit bijection: a machine step, a run, or a
halting condition may be transported in either direction without an existential
quantifier standing in for the lost representative. -/
def equivCanonical : {c : Cfg Γ Λ // Canonical c} ≃ TM0.Cfg Γ Λ where
  toFun c := toTM0 c.1
  invFun X := ⟨ofTM0Cfg X, canonical_ofTM0Cfg X⟩
  left_inv c := Subtype.ext <| show ofTM0Cfg (toTM0 c.1) = c.1 by
    rw [ofTM0Cfg_toTM0, normalize_eq_self_of_canonical c.2]
  right_inv X := toTM0_ofTM0Cfg X

end Normalize

end PostMachine
end StringRewriting
end GroupApproximation
