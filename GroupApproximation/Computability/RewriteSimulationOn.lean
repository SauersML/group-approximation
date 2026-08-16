import GroupApproximation.Computability.RewriteSimulation

/-!
# Simulation without global determinism

`Computability.RewriteSimulation` discharges the hard direction of a machine
encoding, but it asks for one thing a real encoding cannot give: that the
rewriting system be deterministic on **every** word.  A Turing machine encoding
is deterministic only on *configuration* words --- those carrying exactly one
state letter.  A word carrying two state letters admits a step at each of them,
so the system is not globally deterministic, and the earlier interface could
never have accepted a genuine machine.  `UnaryCounterSimulation` satisfied it
only because a one-letter alphabet makes every word a configuration.

This file removes that requirement.  What replaces it is the observation that
determinism on configurations is *free*: a step out of `encode c` is a machine
step by `step_complete`, and `step` is a function, so two steps out of the same
configuration have the same target.  Nothing has to be assumed.

The one genuinely new condition is **backward closure**: a word that steps *into*
a configuration is itself a configuration.  A standard encoding has it for the
same reason it has the forward direction --- both sides of every rule carry
exactly one state letter, so a rule application preserves "is a configuration"
in both directions, and `Derives.countP_eq` is exactly the tool that checks it.

## Why backward closure is what the zigzag needs

Derivability is the equivalence closure, so a derivation between two
configurations may step backwards into words that are not configurations.
Forward closure alone does not stop that.  With closure in both directions
every word along the zigzag is a configuration, the runs out of each are
linearly ordered by `Reach.linear`, and the join goes through --- with no
determinism hypothesis anywhere.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*} {C : Type*}

/-- A machine encoding, asking only what a real encoding provides.

The four fields are: the encoding is injective, a machine step is a rewriting
step, a rewriting step *out of* a configuration is a machine step, and a
rewriting step *into* a configuration comes from a configuration.  There is no
determinism field: on configurations it is a consequence, and off them it is
false for any honest encoding. -/
structure SimulationOn (α : Type*) (C : Type*) where
  /-- The rewriting system. -/
  system : RewriteSystem α
  /-- Configurations, written as words. -/
  encode : C → List α
  /-- The machine's partial step function. -/
  step : C → Option C
  /-- Distinct configurations have distinct words. -/
  encode_injective : Function.Injective encode
  /-- A machine step is a rewriting step. -/
  step_sound : ∀ c d, step c = some d → Step system (encode c) (encode d)
  /-- A rewriting step out of a configuration is a machine step. -/
  step_complete : ∀ c w, Step system (encode c) w →
    ∃ d, step c = some d ∧ w = encode d
  /-- A rewriting step into a configuration starts at a configuration. -/
  step_closed_inv : ∀ c w, Step system w (encode c) → ∃ d, w = encode d

variable (S : SimulationOn α C)

/-! ## Determinism on configurations is free -/

/-- Two rewriting steps out of the same configuration agree.  No hypothesis:
`step` is a function. -/
theorem SimulationOn.deterministic_at (c : C) {b d : List α}
    (hb : Step S.system (S.encode c) b) (hd : Step S.system (S.encode c) d) :
    b = d := by
  obtain ⟨x, hx, rfl⟩ := S.step_complete c b hb
  obtain ⟨y, hy, rfl⟩ := S.step_complete c d hd
  rw [hx] at hy
  exact congrArg S.encode (Option.some.inj hy)

/-- A halting configuration is a normal form. -/
theorem SimulationOn.normalForm_of_halts {c : C} (hc : S.step c = none) :
    NormalForm S.system (S.encode c) := by
  intro w hw
  obtain ⟨d, hd, _⟩ := S.step_complete c w hw
  rw [hc] at hd
  simp at hd

/-! ## Runs and reductions -/

/-- A machine run gives a reduction. -/
theorem SimulationOn.reduces_of_reach {c d : C} (h : Reach S.step c d) :
    Reduces S.system (S.encode c) (S.encode d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (S.step_sound _ _ hstep)

/-- A reduction out of a configuration is a machine run, and never leaves the
configurations. -/
theorem SimulationOn.reach_of_reduces {c : C} {w : List α}
    (h : Reduces S.system (S.encode c) w) :
    ∃ d, Reach S.step c d ∧ w = S.encode d := by
  induction h with
  | refl => exact ⟨c, Reach.refl c, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨d, hcd, rfl⟩ := ih
    obtain ⟨e, hde, rfl⟩ := S.step_complete d _ hstep
    exact ⟨e, hcd.tail hde, rfl⟩

/-- **Confluence at configurations**, with no determinism hypothesis: two
reductions out of a configuration are two runs of the machine, and runs out of
one configuration are linearly ordered. -/
theorem SimulationOn.join_of_reduces {c : C} {x y : List α}
    (hx : Reduces S.system (S.encode c) x)
    (hy : Reduces S.system (S.encode c) y) :
    ∃ z, Reduces S.system x z ∧ Reduces S.system y z := by
  obtain ⟨d, hcd, rfl⟩ := S.reach_of_reduces hx
  obtain ⟨e, hce, rfl⟩ := S.reach_of_reduces hy
  rcases Reach.linear hcd hce with h | h
  · exact ⟨S.encode e, S.reduces_of_reach h, Relation.ReflTransGen.refl⟩
  · exact ⟨S.encode d, Relation.ReflTransGen.refl, S.reduces_of_reach h⟩

/-! ## The zigzag stays among configurations -/

/-- Being a configuration is preserved along a single step, in both
directions.  Forward is `step_complete`; backward is `step_closed_inv`. -/
theorem SimulationOn.isConfig_step_iff {a b : List α} (h : Step S.system a b) :
    ((∃ c, a = S.encode c) ↔ ∃ c, b = S.encode c) := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨d, _, rfl⟩ := S.step_complete c b h
    exact ⟨d, rfl⟩
  · rintro ⟨c, rfl⟩
    exact S.step_closed_inv c a h

/-- Being a configuration is preserved along a whole derivation.  Stated as an
iff because derivability is the equivalence closure. -/
theorem SimulationOn.isConfig_derives_iff {a b : List α}
    (h : Derives S.system a b) :
    ((∃ c, a = S.encode c) ↔ ∃ c, b = S.encode c) := by
  induction h with
  | rel x y hxy => exact S.isConfig_step_iff hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The crux, without global determinism -/

/-- **Derivability between configurations is meeting of machine runs.**  The
zigzag never leaves the configurations, by closure in both directions, and each
leg is joined by `join_of_reduces`.  No determinism is assumed anywhere. -/
theorem SimulationOn.derives_iff (c d : C) :
    Derives S.system (S.encode c) (S.encode d) ↔
      ∃ e, Reach S.step c e ∧ Reach S.step d e := by
  constructor
  · intro h
    have key : ∀ {x y : List α}, Derives S.system x y →
        (∃ c, x = S.encode c) →
        ∃ z, Reduces S.system x z ∧ Reduces S.system y z := by
      intro x y hxy
      induction hxy with
      | rel u v huv =>
        intro _
        exact ⟨v, Relation.ReflTransGen.single huv, Relation.ReflTransGen.refl⟩
      | refl u =>
        intro _
        exact ⟨u, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      | symm u v huv ih =>
        intro hv
        obtain ⟨z, h₁, h₂⟩ := ih ((S.isConfig_derives_iff huv).mpr hv)
        exact ⟨z, h₂, h₁⟩
      | trans u v w huv hvw ih₁ ih₂ =>
        intro hu
        obtain ⟨z₁, hu₁, hv₁⟩ := ih₁ hu
        obtain ⟨cv, hcv⟩ := (S.isConfig_derives_iff huv).mp hu
        obtain ⟨z₂, hv₂, hw₂⟩ := ih₂ ⟨cv, hcv⟩
        subst hcv
        obtain ⟨z, hz₁, hz₂⟩ := S.join_of_reduces hv₁ hv₂
        exact ⟨z, hu₁.trans hz₁, hw₂.trans hz₂⟩
    obtain ⟨x, hcx, hdx⟩ := key h ⟨c, rfl⟩
    obtain ⟨e, hce, rfl⟩ := S.reach_of_reduces hcx
    obtain ⟨e', hde', he'⟩ := S.reach_of_reduces hdx
    have hee : e' = e := S.encode_injective he'.symm
    subst hee
    exact ⟨e', hce, hde'⟩
  · rintro ⟨e, hce, hde⟩
    exact ((S.reduces_of_reach hce).derives).trans
      ((S.reduces_of_reach hde).derives).symm

/-- **Distinct halts stay distinct**, now for an interface a real machine
encoding can actually satisfy. -/
theorem SimulationOn.eq_of_derives_of_halts {c d : C}
    (hc : S.step c = none) (hd : S.step d = none)
    (h : Derives S.system (S.encode c) (S.encode d)) : c = d := by
  obtain ⟨e, hce, hde⟩ := (S.derives_iff c d).mp h
  have hc' : c = e := by
    rcases Reach.cases_head hce with h' | ⟨f, hf, _⟩
    · exact h'
    · rw [hc] at hf
      simp at hf
  have hd' : d = e := by
    rcases Reach.cases_head hde with h' | ⟨f, hf, _⟩
    · exact h'
    · rw [hd] at hf
      simp at hf
  exact hc'.trans hd'.symm

/-- The same statement in the presented monoid. -/
theorem SimulationOn.mk_eq_mk_iff_of_halts {c d : C}
    (hc : S.step c = none) (hd : S.step d = none) :
    StringRewriting.mk S.system (S.encode c) =
      StringRewriting.mk S.system (S.encode d) ↔ c = d := by
  constructor
  · intro h
    exact S.eq_of_derives_of_halts hc hd (StringRewriting.mk_eq_mk_iff.mp h)
  · rintro rfl
    rfl

/-- **The word problem is the reachability problem.**  Against a *halting*
configuration `d`, equality in the presented monoid says exactly that the
machine driven from `c` arrives at `d`.

This is the form the reduction actually needs.  `mk_eq_mk_iff_of_halts` says
distinct halts stay distinct, which keeps the encoding honest but decides
nothing; here one side of the comparison is fixed and the other ranges over
starting configurations, so an algorithm for the word problem would be an
algorithm for "does this machine run reach that halt".  A machine whose halting
is undecidable therefore hands its undecidability to the monoid.

The proof is `derives_iff` plus the observation that a halting configuration
reaches nothing but itself, so the meeting point of the two runs has to be `d`
and the second run has to be empty. -/
theorem SimulationOn.mk_eq_mk_iff_reach_of_halts {c d : C} (hd : S.step d = none) :
    StringRewriting.mk S.system (S.encode c) =
      StringRewriting.mk S.system (S.encode d) ↔ Reach S.step c d := by
  rw [StringRewriting.mk_eq_mk_iff]
  constructor
  · intro h
    obtain ⟨e, hce, hde⟩ := (S.derives_iff c d).mp h
    have hde' : d = e := by
      rcases Reach.cases_head hde with h' | ⟨f, hf, _⟩
      · exact h'
      · rw [hd] at hf
        simp at hf
    rw [hde']
    exact hce
  · intro h
    exact (S.derives_iff c d).mpr ⟨d, h, Reach.refl d⟩

end StringRewriting
end GroupApproximation
