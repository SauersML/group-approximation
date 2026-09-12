import GroupApproximation.Computability.RewriteMonoid

/-!
# Invariants of a string rewriting system

A simulation argument has two directions.  The easy one --- a computation gives
a derivation --- is a matter of applying rules.  The hard one --- a derivation
gives a computation --- has to rule out derivations that wander outside the
words a machine can produce, and that is done with *invariants*: quantities
preserved by every rule, hence by every derivation.

This file provides the ones a Post-style simulation uses:

* a letter count preserved rule-wise is preserved by derivations
  (`Derives.countP_eq`); the instance that matters is "exactly one state
  letter", which is what confines a derivation to configuration words;
* length, for a length-preserving system (`Derives.length_eq`);
* the alphabet is not enlarged (`Derives.mem_of_rules_subset`).

Each hypothesis is a check on the finitely many rules, which is what makes
these usable: an invariant of a concrete machine encoding becomes a finite
verification.

One point of technique, since it recurs.  Derivability is the *equivalence*
closure of rewriting, so an induction over it must prove a statement that is
symmetric in its two endpoints.  "Every letter of `a` lies in `S` implies every
letter of `b` does" is not, and the induction gets stuck at the `symm` case;
the iff version goes through unchanged, and the one-directional form is then a
corollary.  The same will be true of every invariant added later.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*}

/-! ## Counting invariants -/

/-- **A rule-wise count invariant is a derivation invariant.**  If every rule
preserves the number of letters satisfying `p`, so does every derivation. -/
theorem Derives.countP_eq {R : RewriteSystem α} (p : α → Bool)
    (hR : ∀ q ∈ R.rules, q.1.countP p = q.2.countP p)
    {a b : List α} (h : Derives R a b) : a.countP p = b.countP p := by
  induction h with
  | rel x y hxy =>
    cases hxy with
    | intro u v l r hr =>
      have hlr : l.countP p = r.countP p := hR (l, r) hr
      simp only [List.countP_append, hlr]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- A length-preserving system has length-preserving derivations. -/
theorem Derives.length_eq {R : RewriteSystem α}
    (hR : ∀ q ∈ R.rules, q.1.length = q.2.length)
    {a b : List α} (h : Derives R a b) : a.length = b.length := by
  induction h with
  | rel x y hxy =>
    cases hxy with
    | intro u v l r hr =>
      have hlr : l.length = r.length := hR (l, r) hr
      simp only [List.length_append, hlr]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-! ## Alphabet invariants -/

/-- A single step neither enlarges nor shrinks the alphabet, when both sides of
every rule lie inside `S`.  Stated as an iff so that it survives the symmetric
closure. -/
theorem Step.mem_iff_of_rules_subset {R : RewriteSystem α} {S : Set α}
    (hR : ∀ q ∈ R.rules, (∀ x ∈ q.1, x ∈ S) ∧ ∀ x ∈ q.2, x ∈ S)
    {a b : List α} (h : Step R a b) :
    ((∀ x ∈ a, x ∈ S) ↔ ∀ x ∈ b, x ∈ S) := by
  cases h with
  | intro u v l r hr =>
    constructor
    · intro ha z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · rcases List.mem_append.mp hz' with hzu | hzr
        · exact ha z (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hzu))))
        · exact (hR (l, r) hr).2 z hzr
      · exact ha z (List.mem_append.mpr (Or.inr hz'))
    · intro hb z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · rcases List.mem_append.mp hz' with hzu | hzl
        · exact hb z (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hzu))))
        · exact (hR (l, r) hr).1 z hzl
      · exact hb z (List.mem_append.mpr (Or.inr hz'))

/-- **Derivations do not leave the alphabet**, in the symmetric form the
induction needs. -/
theorem Derives.mem_iff_of_rules_subset {R : RewriteSystem α} {S : Set α}
    (hR : ∀ q ∈ R.rules, (∀ x ∈ q.1, x ∈ S) ∧ ∀ x ∈ q.2, x ∈ S)
    {a b : List α} (h : Derives R a b) :
    ((∀ x ∈ a, x ∈ S) ↔ ∀ x ∈ b, x ∈ S) := by
  induction h with
  | rel x y hxy => exact Step.mem_iff_of_rules_subset hR hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- The one-directional form, which is how it is used. -/
theorem Derives.mem_of_rules_subset {R : RewriteSystem α} {S : Set α}
    (hR : ∀ q ∈ R.rules, (∀ x ∈ q.1, x ∈ S) ∧ ∀ x ∈ q.2, x ∈ S)
    {a b : List α} (h : Derives R a b) (ha : ∀ x ∈ a, x ∈ S) :
    ∀ x ∈ b, x ∈ S :=
  (Derives.mem_iff_of_rules_subset hR h).mp ha

/-! ## Consequences for the presented monoid -/

/-- **Invariants separate.**  To show two words are different in the presented
monoid, exhibit a rule-wise count that tells them apart.  This is the only way
to prove a negative about a presented monoid without solving its word problem,
and every lower bound in the chain ahead has this shape. -/
theorem mk_ne_mk_of_countP_ne {R : RewriteSystem α} (p : α → Bool)
    (hR : ∀ q ∈ R.rules, q.1.countP p = q.2.countP p)
    {a b : List α} (hab : a.countP p ≠ b.countP p) : mk R a ≠ mk R b := by
  intro h
  exact hab (Derives.countP_eq p hR (mk_eq_mk_iff.mp h))

/-- The presented monoid of a nontrivial length-preserving system is not
trivial: length separates the empty word from any nonempty one. -/
theorem mk_ne_one_of_length_ne_zero {R : RewriteSystem α}
    (hR : ∀ q ∈ R.rules, q.1.length = q.2.length)
    {a : List α} (ha : a ≠ []) : mk R a ≠ 1 := by
  intro h
  have hlen : a.length = ([] : List α).length :=
    Derives.length_eq hR (mk_eq_mk_iff.mp h)
  exact ha (List.eq_nil_of_length_eq_zero (by simpa using hlen))

end StringRewriting
end GroupApproximation
