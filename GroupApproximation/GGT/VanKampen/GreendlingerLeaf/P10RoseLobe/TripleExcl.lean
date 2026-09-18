import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleLake
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The three-, four- and five-dart exclusions

Lane gl-p10-69.  The six generic exclusions added to the hypotheses of `roseLobeMulti_Statement`
by `roseLobeTriple_Statement`: each says that the hypotheses of one case lemma (`TripleLake`,
`TripleLobe`) are never met.  Each is literally "hypotheses of the case lemma `→ False`", with
the same argument order, so the reduction applies the lemma verbatim.

* `roseLobeTriple_NoLakeRun` / `_NoLakeWrapL` / `_NoLakeWrapR`: `roseLobeTriple_lake_run` /
  `_lake_wrapL` / `_lake_wrapR`;
* `roseLobeTriple_NoLobeRun` / `_NoLobeQuad` / `_NoLobeQuint`: `roseLobeTriple_lobe_run` /
  `_lobe_quad` / `_lobe_quint` (the kept dart `x` and its non-membership are bundled into one
  `∃`; reachability of `x` from `c` is not assumed: in use it is `roseLobeChoice_kept_on`).

## LOUD: strength

Definitions only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

/-- **No consecutive lake triple**: no three consecutive darts of `c = A ++ [a1, a2, a3] ++ C`
(`A ++ C ≠ []`) carry, under `f`, the whole trace on `c` of an `s`-class missing `PO`, `PS`. -/
def roseLobeTriple_NoLakeRun {α : Type*} (s : α → α → Prop) (c : List α) (f : α → α)
    (PO PS : α → Prop) : Prop :=
  ∀ (A C : List α) (a1 a2 a3 : α), c = A ++ [a1, a2, a3] ++ C → A ++ C ≠ [] →
    Relation.EqvGen s (f a1) (f a2) → Relation.EqvGen s (f a1) (f a3) →
    (∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3]) →
    (∀ x, PO x → ¬Relation.EqvGen s (f a1) x) →
    (∀ x, PS x → ¬Relation.EqvGen s (f a1) x) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLakeRun

/-- **No lake triple wrapping after the first dart**: as `roseLobeTriple_NoLakeRun` for
`c = [a1] ++ M ++ [a2, a3]`, `M ≠ []`. -/
def roseLobeTriple_NoLakeWrapL {α : Type*} (s : α → α → Prop) (c : List α) (f : α → α)
    (PO PS : α → Prop) : Prop :=
  ∀ (M : List α) (a1 a2 a3 : α), c = [a1] ++ M ++ [a2, a3] → M ≠ [] →
    Relation.EqvGen s (f a1) (f a2) → Relation.EqvGen s (f a1) (f a3) →
    (∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3]) →
    (∀ x, PO x → ¬Relation.EqvGen s (f a1) x) →
    (∀ x, PS x → ¬Relation.EqvGen s (f a1) x) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLakeWrapL

/-- **No lake triple wrapping after the second dart**: as `roseLobeTriple_NoLakeRun` for
`c = [a1, a2] ++ M ++ [a3]`, `M ≠ []`. -/
def roseLobeTriple_NoLakeWrapR {α : Type*} (s : α → α → Prop) (c : List α) (f : α → α)
    (PO PS : α → Prop) : Prop :=
  ∀ (M : List α) (a1 a2 a3 : α), c = [a1, a2] ++ M ++ [a3] → M ≠ [] →
    Relation.EqvGen s (f a1) (f a2) → Relation.EqvGen s (f a1) (f a3) →
    (∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3]) →
    (∀ x, PO x → ¬Relation.EqvGen s (f a1) x) →
    (∀ x, PS x → ¬Relation.EqvGen s (f a1) x) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLakeWrapR

/-- **No consecutive inside triple**, suitably placed: no three consecutive darts of
`c = A ++ [a1, a2, a3] ++ C` are closed under the `s`-classes they meet while all of these miss
some `kp`-dart, with the triple not inside `I` away from both ends of `I`, and ending `c` if it
meets `T`. -/
def roseLobeTriple_NoLobeRun {α : Type*} (s : α → α → Prop) (c I T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (A C : List α) (a1 a2 a3 : α), c = A ++ [a1, a2, a3] ++ C →
    (∀ e ∈ c, ∀ r ∈ [a1, a2, a3], Relation.EqvGen s r e → e ∈ [a1, a2, a3]) →
    (∃ x, kp x ∧ ∀ r ∈ [a1, a2, a3], ¬Relation.EqvGen s r x) →
    ((∃ d ∈ [a1, a2, a3], d ∉ I) ∨ [a1, a2, a3] <+: I ∨ [a1, a2, a3] <:+ I) →
    ((∀ d ∈ [a1, a2, a3], d ∉ T) ∨ C = []) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLobeRun

/-- **No consecutive inside quadruple**, suitably placed: as `roseLobeTriple_NoLobeRun` for
four consecutive darts. -/
def roseLobeTriple_NoLobeQuad {α : Type*} (s : α → α → Prop) (c I T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (A C : List α) (a1 a2 a3 a4 : α), c = A ++ [a1, a2, a3, a4] ++ C →
    (∀ e ∈ c, ∀ r ∈ [a1, a2, a3, a4], Relation.EqvGen s r e → e ∈ [a1, a2, a3, a4]) →
    (∃ x, kp x ∧ ∀ r ∈ [a1, a2, a3, a4], ¬Relation.EqvGen s r x) →
    ((∃ d ∈ [a1, a2, a3, a4], d ∉ I) ∨ [a1, a2, a3, a4] <+: I ∨
      [a1, a2, a3, a4] <:+ I) →
    ((∀ d ∈ [a1, a2, a3, a4], d ∉ T) ∨ C = []) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLobeQuad

/-- **No consecutive inside quintuple**, suitably placed: as `roseLobeTriple_NoLobeRun` for
five consecutive darts. -/
def roseLobeTriple_NoLobeQuint {α : Type*} (s : α → α → Prop) (c I T : List α)
    (kp : α → Prop) : Prop :=
  ∀ (A C : List α) (a1 a2 a3 a4 a5 : α), c = A ++ [a1, a2, a3, a4, a5] ++ C →
    (∀ e ∈ c, ∀ r ∈ [a1, a2, a3, a4, a5], Relation.EqvGen s r e →
      e ∈ [a1, a2, a3, a4, a5]) →
    (∃ x, kp x ∧ ∀ r ∈ [a1, a2, a3, a4, a5], ¬Relation.EqvGen s r x) →
    ((∃ d ∈ [a1, a2, a3, a4, a5], d ∉ I) ∨ [a1, a2, a3, a4, a5] <+: I ∨
      [a1, a2, a3, a4, a5] <:+ I) →
    ((∀ d ∈ [a1, a2, a3, a4, a5], d ∉ T) ∨ C = []) → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_NoLobeQuint

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
