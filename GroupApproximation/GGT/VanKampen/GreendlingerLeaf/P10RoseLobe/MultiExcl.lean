import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLake
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-dart exclusions

Lane gl-p10-67.  The five generic exclusions added to the hypotheses of `roseLobeChoice_Statement`
by `roseLobeMulti_Statement`: each says that the hypotheses of one two-dart case lemma
(`MultiLake`, `MultiLobe`) are never met.  Each is literally "hypotheses of the case lemma
`→ False`", with the same argument order, so the reduction applies the lemma verbatim.

* `roseLobeMulti_NoLakePair` / `_NoLakeWrap`: `roseLobeMulti_lake_pair` / `_lake_wrap`;
* `roseLobeMulti_NoLobePair` / `_NoLobeWrap`: `roseLobeMulti_lobe_pair` / `_lobe_wrap` (the
  kept dart `x` and its non-membership are bundled into one `∃`; reachability of `x` from `c`
  is not assumed: in use it is proved by `roseLobeChoice_kept_on`);
* `roseLobeMulti_NoKeptPair`: `roseLobeMulti_kept_pair`.

## LOUD: strength

Definitions only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

/-- **No adjacent lake pair**: no two consecutive darts `a`, `b` of `c = A ++ [a, b] ++ C`
(`A ++ C ≠ []`) carry, under `f`, the whole trace on `c` of an `s`-class missing `PO` and `PS`. -/
def roseLobeMulti_NoLakePair {α : Type*} (s : α → α → Prop) (c : List α) (f : α → α)
    (PO PS : α → Prop) : Prop :=
  ∀ (A C : List α) (a b : α), c = A ++ [a, b] ++ C → A ++ C ≠ [] →
    Relation.EqvGen s (f a) (f b) →
    (∀ e ∈ c, Relation.EqvGen s (f a) (f e) → e = a ∨ e = b) →
    (∀ x, PO x → ¬Relation.EqvGen s (f a) x) →
    (∀ x, PS x → ¬Relation.EqvGen s (f a) x) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_NoLakePair

/-- **No lake pair at the ends**: as `roseLobeMulti_NoLakePair` for the first and last darts of
`c = [a] ++ M ++ [b]`, `M ≠ []`. -/
def roseLobeMulti_NoLakeWrap {α : Type*} (s : α → α → Prop) (c : List α) (f : α → α)
    (PO PS : α → Prop) : Prop :=
  ∀ (M : List α) (a b : α), c = [a] ++ M ++ [b] → M ≠ [] →
    Relation.EqvGen s (f a) (f b) →
    (∀ e ∈ c, Relation.EqvGen s (f a) (f e) → e = a ∨ e = b) →
    (∀ x, PO x → ¬Relation.EqvGen s (f a) x) →
    (∀ x, PS x → ¬Relation.EqvGen s (f a) x) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_NoLakeWrap

/-- **No adjacent inside pair**, suitably placed: no two consecutive darts `a`, `b` of
`c = A ++ [a, b] ++ C` are the whole trace on `c` of an `s`-class missing some `kp`-dart, with
the pair not inside `I` away from both ends of `I`, and ending `c` if it meets `T`. -/
def roseLobeMulti_NoLobePair {α : Type*} (s : α → α → Prop) (c I T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (A C : List α) (a b : α), c = A ++ [a, b] ++ C → Relation.EqvGen s a b →
    (∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b) →
    (∃ x, kp x ∧ ¬Relation.EqvGen s a x) →
    (a ∉ I ∨ b ∉ I ∨ [a, b] <+: I ∨ [a, b] <:+ I) → ((a ∉ T ∧ b ∉ T) ∨ C = []) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_NoLobePair

/-- **No inside pair at the ends**, suitably placed: the first and last darts of
`c = [a] ++ M ++ [b]` are not the whole trace on `c` of an `s`-class missing some `kp`-dart,
when `M` misses `T` or `a` is off `T`. -/
def roseLobeMulti_NoLobeWrap {α : Type*} (s : α → α → Prop) (c T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (M : List α) (a b : α), c = [a] ++ M ++ [b] → Relation.EqvGen s a b →
    (∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b) →
    (∃ x, kp x ∧ ¬Relation.EqvGen s a x) →
    ((∀ d ∈ M, d ∉ T) ∨ a ∉ T) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_NoLobeWrap

/-- **No kept pair**, suitably placed: the class of a `kp`-dart does not meet
`c = A ++ [a, b] ++ C` (`A ++ C ≠ []`) in exactly the consecutive darts `a`, `b`, when the pair
misses `T` or nothing of `A` is on `T`. -/
def roseLobeMulti_NoKeptPair {α : Type*} (s : α → α → Prop) (c T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (A C : List α) (a b x : α), c = A ++ [a, b] ++ C → A ++ C ≠ [] → kp x →
    Relation.EqvGen s a x → Relation.EqvGen s a b →
    (∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b) →
    ((a ∉ T ∧ b ∉ T) ∨ ∀ e ∈ A, e ∉ T) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_NoKeptPair

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
