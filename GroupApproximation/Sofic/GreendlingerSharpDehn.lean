import GroupApproximation.Sofic.GreendlingerPieceOverlapProof
import GroupApproximation.Sofic.GreendlingerSharpTwins

/-!
# Dehn's algorithm at the sharp threshold

`GreendlingerDehn` reaches `GreendlingerConclusion` --- the *half*-form --- by
rewriting, and every length condition along that route is the literal
`|r| < 2|u|`.  That is not an artifact of clearing a denominator, the way the
`1/6` in `GreendlingerDeepArc` was: it is the rule.  A Dehn step replaces `u` by
`invRev v` inside `r = u ++ v`, and `2|u| > |r|` is exactly what makes the
replacement shorter, which is what makes the system terminate and what makes
`DehnStep.length_lt` --- hence the whole critical-pair induction --- go through.
So the rewriting route as written is pinned at a half by its own rule, and
`greendlinger_of_dehnStep` returns a half-form arc because a half is what the
rule says.

This file installs the sharp threshold in the rule itself.  `DehnStepSharp`
demands `(1 - 3λ)|r| < |u|`, and for `λ ≤ 1/6` that is a *stronger* demand than
`2|u| > |r|`, since `1 - 3λ ≥ 1/2`.  The replacement is then still strictly
shorter --- `|v| = |r| - |u| < 3λ|r| ≤ |r|/2 < |u|` --- so the system still
terminates, and a step out of a reduced word now exhibits precisely what
`GreendlingerConclusionSharp` asks for.

## What twins, and what does not

Everything unconditional in `GreendlingerDehn` twins verbatim, because none of it
reads the length condition: context-freeness, closure under concatenation, the
stem cancelling itself, the expression's word.  Two places acquire a side
condition:

* `dehnReducibleSharp_conjugate` needs `0 < lam`.  Deleting a whole relator in
  one step asks for `(1 - 3λ)|s| < |s|`, which is `0 < 3λ|s|`; at `λ = 0` the
  sharp rule cannot even delete a relator, which is the same degeneracy
  `GreendlingerSharpTwins.lam_pos_of_metric` exists to rule out.
* `DehnStepSharp.length_lt` needs `lam ≤ 1/6`, for the reason above.

The *critical-pair analysis* does **not** twin, and the obstruction is one lemma.
`GreendlingerDehnCritical.dehnStep_of_swap_of_lt` --- a lengthening swap is a step
read backwards --- turns `|u| < |v|` into the step condition on the reversed
split, and `|u| < |v|` gives exactly `|v| > |r|/2` and no more.  Below a sixth
the sharp rule wants `|v| > (1 - 3λ)|r|`, which is strictly more, so the
"lengthening swaps are free" reduction that every configuration in
`GreendlingerDehnSwap` is filtered through is unavailable.  Nothing here attempts
it, and no sharp twin of `DehnSwap`, `PieceOverlapRight` or the joint induction is
offered.

## What this leaves open, and how it compares

One leaf: `DehnReduceClosedSharp` --- sharp reducibility survives free reduction.
It is the exact twin of `GreendlingerDehn.DehnReduceClosed`, and
`dehnReduceClosedSharp_sixth_iff` shows the twin is faithful: at `λ = 1/6` the
two rules are the same relation and the two leaves are the same statement.  So
the sharp gate now has a second route with **one** open leaf beside the drop
route's two.

That count is not a measure of difficulty and should not be read as one.
`GreendlingerPieceOverlapProof.pieceOverlapRight_iff_dehnSwapClosed` records that
the `λ`-free critical-pair analysis reduced the *configuration* the residual
speaks about and not its logical strength; the leaf here is upstream even of
that analysis, so it is one statement of full strength, whereas the drop route's
two leaves are each strictly weaker than the gate.  What the route does buy is
independence: it shares no machinery with the descent, needs no palindromes, no
minimal expressions and no weight, and its leaf is a statement about one
rewriting system rather than about where two cancellations leave a window.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The threshold, as arithmetic -/

/-- **The sharp threshold implies the half threshold**, for `λ ≤ 1/6`.  This is
the whole of the relation between the two rules: `1 - 3λ ≥ 1/2`, so a block
exceeding `(1 - 3λ)|r|` exceeds `|r|/2`, and the natural-number condition the
`λ`-free rule carries follows. -/
theorem lt_two_mul_of_sharp_long {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {r u : List (α × Bool)}
    (hlong : (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ)) :
    r.length < 2 * u.length := by
  have hrnn : (0 : ℚ) ≤ (r.length : ℚ) := by positivity
  have hhalf : (1 : ℚ) / 2 * (r.length : ℚ) ≤ (1 - 3 * lam) * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) hrnn
  have hcast : (r.length : ℚ) < ((2 * u.length : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- **At a sixth the two thresholds agree.**  `1 - 3·(1/6) = 1/2`, so the
`λ`-free rule's condition is the sharp condition read at `λ = 1/6`. -/
theorem sharp_long_sixth_of_lt_two_mul {r u : List (α × Bool)}
    (hlong : r.length < 2 * u.length) :
    (1 - 3 * (1 / 6 : ℚ)) * (r.length : ℚ) < (u.length : ℚ) := by
  have hcast : (r.length : ℚ) < ((2 * u.length : ℕ) : ℚ) := by exact_mod_cast hlong
  push_cast at hcast
  have hcoef : (1 - 3 * (1 / 6 : ℚ)) * (r.length : ℚ) = (r.length : ℚ) / 2 := by
    ring
  rw [hcoef]
  linarith

/-! ## 2.  The sharp rewriting system -/

/-- **One step of Dehn's algorithm at the sharp threshold.**  The free rule is
unchanged; the Dehn rule replaces a block occupying more than `(1 - 3λ)` of a
symmetrized relator by the inverse of the rest.

The `λ`-free `DehnStep` is this rule at `λ = 1/6`
(`dehnStepSharp_sixth_of_dehnStep`, `DehnStepSharp.toDehnStep`); below a sixth
the sharp rule is strictly more demanding, so it takes strictly fewer steps and
`DehnReducibleSharp` is a smaller class than `DehnReducible`. -/
inductive DehnStepSharp (R : Set (List (α × Bool))) (lam : ℚ) :
    List (α × Bool) → List (α × Bool) → Prop
  | free (A B : List (α × Bool)) (x : α × Bool) :
      DehnStepSharp R lam (A ++ (x :: invLetter x :: B)) (A ++ B)
  | dehn (A B u v r : List (α × Bool)) (hr : r ∈ symmetrization R)
      (hsplit : r = u ++ v)
      (hlong : (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ)) :
      DehnStepSharp R lam (A ++ (u ++ B)) (A ++ (FreeGroup.invRev v ++ B))

/-- A word the sharp algorithm takes to the empty word. -/
def DehnReducibleSharp (R : Set (List (α × Bool))) (lam : ℚ)
    (w : List (α × Bool)) : Prop :=
  Relation.ReflTransGen (DehnStepSharp R lam) w []

/-! ## 3.  The sharp system sits inside the `λ`-free one -/

/-- **A sharp step is a step**, for `λ ≤ 1/6`. -/
theorem DehnStepSharp.toDehnStep {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) {W W' : List (α × Bool)}
    (h : DehnStepSharp R lam W W') : DehnStep R W W' := by
  cases h with
  | free A B x => exact DehnStep.free A B x
  | dehn A B u v r hr hsplit hlong =>
      exact DehnStep.dehn A B u v r hr hsplit (lt_two_mul_of_sharp_long hlam hlong)

/-- **At a sixth, every step is sharp.** -/
theorem dehnStepSharp_sixth_of_dehnStep {R : Set (List (α × Bool))}
    {W W' : List (α × Bool)} (h : DehnStep R W W') :
    DehnStepSharp R (1 / 6) W W' := by
  cases h with
  | free A B x => exact DehnStepSharp.free A B x
  | dehn A B u v r hr hsplit hlong =>
      exact DehnStepSharp.dehn A B u v r hr hsplit
        (sharp_long_sixth_of_lt_two_mul hlong)

/-- **A sharp step shortens its word**, which is what makes the sharp system
terminate: the free rule deletes two letters, and the Dehn rule leaves at most
`3λ|r| ≤ |r|/2` where more than `|r|/2` stood. -/
theorem DehnStepSharp.length_lt {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) {W W' : List (α × Bool)}
    (h : DehnStepSharp R lam W W') : W'.length < W.length :=
  DehnStep.length_lt (DehnStepSharp.toDehnStep hlam h)

/-- A sharp derivation is a derivation. -/
theorem dehnDerivationSharp_toDerivation {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) :
    ∀ {W V : List (α × Bool)}, Relation.ReflTransGen (DehnStepSharp R lam) W V →
      Relation.ReflTransGen (DehnStep R) W V := by
  intro W V h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (DehnStepSharp.toDehnStep hlam hbc)

/-- At a sixth, every derivation is sharp. -/
theorem dehnDerivationSharp_sixth {R : Set (List (α × Bool))} :
    ∀ {W V : List (α × Bool)}, Relation.ReflTransGen (DehnStep R) W V →
      Relation.ReflTransGen (DehnStepSharp R (1 / 6)) W V := by
  intro W V h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (dehnStepSharp_sixth_of_dehnStep hbc)

/-- Sharp reducibility is reducibility. -/
theorem DehnReducibleSharp.toDehnReducible {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) {w : List (α × Bool)}
    (h : DehnReducibleSharp R lam w) : DehnReducible R w := by
  have hb : Relation.ReflTransGen (DehnStepSharp R lam) w [] := h
  exact dehnDerivationSharp_toDerivation hlam hb

/-- At a sixth, every reducible word is sharply reducible. -/
theorem dehnReducibleSharp_sixth_of_dehnReducible {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : DehnReducible R w) :
    DehnReducibleSharp R (1 / 6) w := by
  have hb : Relation.ReflTransGen (DehnStep R) w [] := h
  exact dehnDerivationSharp_sixth hb

/-- **At a sixth the two systems have the same reducible words.** -/
theorem dehnReducibleSharp_sixth_iff {R : Set (List (α × Bool))}
    {w : List (α × Bool)} :
    DehnReducibleSharp R (1 / 6) w ↔ DehnReducible R w :=
  ⟨fun h => DehnReducibleSharp.toDehnReducible le_rfl h,
    fun h => dehnReducibleSharp_sixth_of_dehnReducible h⟩

/-! ## 4.  The sharp system is context free -/

/-- **A sharp step applies in any context.**  Quoted from `DehnStep.context`; the
length condition is carried untouched, which is why the whole structural layer
twins. -/
theorem DehnStepSharp.context {R : Set (List (α × Bool))} {lam : ℚ}
    {w w' : List (α × Bool)} (h : DehnStepSharp R lam w w')
    (A B : List (α × Bool)) :
    DehnStepSharp R lam (A ++ w ++ B) (A ++ w' ++ B) := by
  cases h with
  | free A₁ B₁ x =>
      have h1 : A ++ (A₁ ++ (x :: invLetter x :: B₁)) ++ B
          = (A ++ A₁) ++ (x :: invLetter x :: (B₁ ++ B)) := by
        simp only [List.append_assoc, List.cons_append]
      have h2 : A ++ (A₁ ++ B₁) ++ B = (A ++ A₁) ++ (B₁ ++ B) := by
        simp only [List.append_assoc]
      rw [h1, h2]
      exact DehnStepSharp.free (A ++ A₁) (B₁ ++ B) x
  | dehn A₁ B₁ u v r hr hsplit hlong =>
      have h1 : A ++ (A₁ ++ (u ++ B₁)) ++ B = (A ++ A₁) ++ (u ++ (B₁ ++ B)) := by
        simp only [List.append_assoc]
      have h2 : A ++ (A₁ ++ (FreeGroup.invRev v ++ B₁)) ++ B
          = (A ++ A₁) ++ (FreeGroup.invRev v ++ (B₁ ++ B)) := by
        simp only [List.append_assoc]
      rw [h1, h2]
      exact DehnStepSharp.dehn (A ++ A₁) (B₁ ++ B) u v r hr hsplit hlong

/-- A whole sharp derivation applies in any context. -/
theorem dehnDerivationSharp_context {R : Set (List (α × Bool))} {lam : ℚ}
    {w w₂ : List (α × Bool)}
    (h : Relation.ReflTransGen (DehnStepSharp R lam) w w₂)
    (A B : List (α × Bool)) :
    Relation.ReflTransGen (DehnStepSharp R lam) (A ++ w ++ B) (A ++ w₂ ++ B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (DehnStepSharp.context hbc A B)

/-! ## 5.  Closure properties -/

theorem dehnReducibleSharp_nil (R : Set (List (α × Bool))) (lam : ℚ) :
    DehnReducibleSharp R lam ([] : List (α × Bool)) := Relation.ReflTransGen.refl

/-- A cancelling pair is sharply reducible: the free rule is unchanged. -/
theorem dehnReducibleSharp_pair (R : Set (List (α × Bool))) (lam : ℚ)
    (x : α × Bool) : DehnReducibleSharp R lam [x, invLetter x] :=
  Relation.ReflTransGen.single (DehnStepSharp.free [] [] x)

/-- **Sharply reducible words are closed under concatenation.**  The derivation
for the first word runs inside the concatenation and leaves the second standing;
no free reduction across the junction is needed, so no length condition is
consulted. -/
theorem DehnReducibleSharp.append {R : Set (List (α × Bool))} {lam : ℚ}
    {u v : List (α × Bool)} (hu : DehnReducibleSharp R lam u)
    (hv : DehnReducibleSharp R lam v) : DehnReducibleSharp R lam (u ++ v) := by
  have h1 : Relation.ReflTransGen (DehnStepSharp R lam) ([] ++ u ++ v)
      ([] ++ [] ++ v) := dehnDerivationSharp_context hu [] v
  simp only [List.nil_append] at h1
  exact h1.trans hv

/-- A stem followed by its own inverse is sharply reducible. -/
theorem dehnReducibleSharp_append_invRev (R : Set (List (α × Bool))) (lam : ℚ) :
    ∀ c : List (α × Bool), DehnReducibleSharp R lam (c ++ FreeGroup.invRev c) := by
  intro c
  induction c with
  | nil => exact dehnReducibleSharp_nil R lam
  | cons a c' ih =>
      have h1 : (a :: c') ++ FreeGroup.invRev (a :: c')
          = [a] ++ (c' ++ FreeGroup.invRev c') ++ [invLetter a] := by
        rw [invRev_cons]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      have h2 := dehnDerivationSharp_context ih [a] [invLetter a]
      rw [h1]
      refine h2.trans ?_
      simp only [List.append_nil]
      exact dehnReducibleSharp_pair R lam a

/-- **A conjugate of a symmetrized relator is sharply reducible.**  One sharp
step deletes the whole relator, and the stem then cancels itself.

This is the first place the sharp threshold costs anything: deleting all of `s`
asks for `(1 - 3λ)|s| < |s|`, which is `0 < 3λ|s|`, so the sharp system needs
`0 < lam` where the `λ`-free one needed only `s ≠ []`.  The gate assembly
recovers `0 < lam` from the metric condition, exactly as the drop route does. -/
theorem dehnReducibleSharp_conjugate {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) {s : List (α × Bool)} (hs : s ∈ symmetrization R)
    (hsne : s ≠ []) (c : List (α × Bool)) :
    DehnReducibleSharp R lam (c ++ (s ++ FreeGroup.invRev c)) := by
  have hpos : (0 : ℚ) < (s.length : ℚ) := by
    have hb : 0 < s.length := List.length_pos_iff.mpr hsne
    exact_mod_cast hb
  have hexp : (1 - 3 * lam) * (s.length : ℚ)
      = (s.length : ℚ) - 3 * (lam * (s.length : ℚ)) := by ring
  have hmul : 0 < lam * (s.length : ℚ) := mul_pos hlam0 hpos
  have hlong : (1 - 3 * lam) * (s.length : ℚ) < (s.length : ℚ) := by
    rw [hexp]
    linarith
  have hstep : DehnStepSharp R lam (c ++ (s ++ FreeGroup.invRev c))
      (c ++ (FreeGroup.invRev [] ++ FreeGroup.invRev c)) :=
    DehnStepSharp.dehn c (FreeGroup.invRev c) s [] s hs (List.append_nil s).symm
      hlong
  refine Relation.ReflTransGen.head hstep ?_
  rw [invRev_nil, List.nil_append]
  exact dehnReducibleSharp_append_invRev R lam c

/-- **The concatenation of the factors of an expression is sharply reducible.**
The `λ`-free statement with `0 < lam` added; `exprWord` itself is reused, not
re-defined, so the two routes read the same word. -/
theorem dehnReducibleSharp_exprWord [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam) (hRne : ∀ r ∈ R, r ≠ []) :
    ∀ e : List (FreeGroup α × List (α × Bool)), ConjValid R e →
      DehnReducibleSharp R lam (exprWord e) := by
  intro e
  induction e with
  | nil =>
      intro _
      exact dehnReducibleSharp_nil R lam
  | cons xs e ih =>
      intro hv
      obtain ⟨x, s⟩ := xs
      obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
      rw [exprWord_cons]
      exact DehnReducibleSharp.append
        (dehnReducibleSharp_conjugate hlam0 h1
          (ne_nil_of_mem_symmetrization hRne h1) x.toWord) (ih h2)

/-! ## 6.  A sharp step out of a reduced word is the sharp conclusion -/

/-- **The payoff of moving the threshold into the rule.**  A step out of a
reduced word cannot be free, so it is a sharp Dehn step, and a sharp Dehn step
names a subword which is a prefix of a symmetrized relator and occupies more than
`(1 - 3λ)` of it --- which is exactly the datum `GreendlingerConclusionSharp`
asks for, with no rounding and no second argument.

`GreendlingerDehn.greendlinger_of_dehnStep` is this statement at the half
threshold, and returns the half-form for the same reason: the rule it reads is
the rule that was written. -/
theorem greendlingerSharp_of_dehnStepSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} {w w' : List (α × Bool)}
    (hw : FreeGroup.IsReduced w) (h : DehnStepSharp R lam w w') :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ (1 - 3 * lam) * (r.length : ℚ) < (u.length : ℚ) := by
  cases h with
  | free A B x => exact (not_isReduced_cancel hw).elim
  | dehn A B u v r hr hsplit hlong =>
      exact ⟨r, hr, u, ⟨A, B, by simp only [List.append_assoc]⟩,
        ⟨v, hsplit.symm⟩, hlong⟩

/-! ## 7.  The leaf, and the sharp conclusion it buys -/

/-- **The one statement the sharp rewriting route asks for**: sharp reducibility
survives free reduction.  The exact twin of `GreendlingerDehn.DehnReduceClosed`,
and `dehnReduceClosedSharp_sixth_iff` below checks that the twin is faithful.

Like the `λ`-free statement it is false without small cancellation --- the
commutator witness recorded in `GreendlingerDehn` refutes it at `λ = 1/6`, hence
at every smaller `λ`, the sharp system taking a subset of the steps. -/
def DehnReduceClosedSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ W : List (α × Bool), DehnReducibleSharp R lam W →
    DehnReducibleSharp R lam (FreeGroup.reduce W)

/-- **The leaf is the `λ`-free leaf at a sixth.**  Both rules are then the same
relation, so both classes of reducible words coincide and the two closure
statements are one.  This is what makes the file a generalization of
`GreendlingerDehn` rather than a parallel construction. -/
theorem dehnReduceClosedSharp_sixth_iff [DecidableEq α]
    {R : Set (List (α × Bool))} :
    DehnReduceClosedSharp R (1 / 6) ↔ DehnReduceClosed R := by
  constructor
  · intro h W hW
    exact dehnReducibleSharp_sixth_iff.mp
      (h W (dehnReducibleSharp_sixth_iff.mpr hW))
  · intro h W hW
    exact dehnReducibleSharp_sixth_iff.mpr
      (h W (dehnReducibleSharp_sixth_iff.mp hW))

/-- **The sharp conclusion, from the rewriting route.**  A nonempty reduced word
in the normal closure is spelled by the free reduction of a sharply reducible
word, hence is sharply reducible, hence admits a sharp Dehn step, which is the
sharp Greendlinger conclusion.

The `λ`-free proof is quoted line for line; the only new hypothesis is `0 < lam`,
which `dehnReducibleSharp_conjugate` consumes. -/
theorem greendlingerConclusionSharp_of_dehnReduceClosedSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam0 : 0 < lam)
    (hRne : ∀ r ∈ R, r ≠ []) (hclosed : DehnReduceClosedSharp R lam) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e, hv, -, he⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  have hW : DehnReducibleSharp R lam (exprWord e) :=
    dehnReducibleSharp_exprWord hlam0 hRne e hv
  have hmkW : FreeGroup.mk (exprWord e) = FreeGroup.mk w := by
    rw [mk_exprWord, he]
  have hredW : FreeGroup.reduce (exprWord e) = w := by
    have hb := FreeGroup.reduce.sound hmkW
    rwa [hw.reduce_eq] at hb
  have hwD : DehnReducibleSharp R lam w := by
    have hb := hclosed (exprWord e) hW
    rwa [hredW] at hb
  rcases Relation.ReflTransGen.cases_head hwD with hnil | ⟨w', hstep, -⟩
  · exact absurd hnil hwne
  · exact greendlingerSharp_of_dehnStepSharp hw hstep

/-! ## 8.  The gate, along the rewriting route -/

/-- **The sharp gate from one leaf.**  Supply a `DehnReduceClosedSharp` family
and `GreendlingerFreeGate.SharpGreendlingerGate` follows, hence torsion-freeness
of the presented quotient, hence the router.

The two side conditions the gate does not supply --- `0 < lam` and
`∀ r ∈ R, r ≠ []` --- are recovered exactly as
`GreendlingerSharpDropGate.sharpGreendlingerGate_of_cascadeLandingDropSharp`
recovers them, from a piece of the empty word; and where every relator is empty
the normal closure is trivial and no reduced nonempty word lies in it.

The argument is a hypothesis.  Nothing here discharges it. -/
theorem sharpGreendlingerGate_of_dehnReduceClosedSharp [DecidableEq α]
    (hclosed : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DehnReduceClosedSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α := by
  intro R lam hcyc hlam hmetric
  by_cases hex : ∃ r ∈ R, r ≠ []
  · obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := exists_two_distinct_symmetrization hcyc hex
    obtain ⟨r, hr, hrne⟩ := hex
    have hlam0 : 0 < lam :=
      lam_pos_of_metric hmetric hs₁ hs₂ hne (subset_symmetrization R hr) hrne
    have hRne : ∀ q ∈ R, q ≠ [] := fun q hq =>
      ne_nil_of_metric_lam hmetric hs₁ hs₂ hne (subset_symmetrization R hq)
    exact greendlingerConclusionSharp_of_dehnReduceClosedSharp hlam0 hRne
      (hclosed R lam hcyc hRne hlam0 hlam hmetric)
  · intro w hw hwne hmem
    exfalso
    push Not at hex
    have hsub : FreeGroup.mk '' R ⊆
        ((⊥ : Subgroup (FreeGroup α)) : Set (FreeGroup α)) := by
      rintro _ ⟨r, hr, rfl⟩
      have hone : FreeGroup.mk r = (1 : FreeGroup α) := by
        rw [hex r hr, ← FreeGroup.one_eq_mk]
      simp [hone]
    have hb := Subgroup.normalClosure_le_normal hsub hmem
    rw [Subgroup.mem_bot] at hb
    have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [hb]
      exact FreeGroup.one_eq_mk
    have h2 := FreeGroup.reduce.sound h1
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
    exact hwne h2

/-- The rewriting-route gate on the router's own alphabet, which is the instance
every construction in this repository consumes. -/
theorem sharpGreendlingerGate_fin_two_of_dehnReduceClosedSharp
    (hclosed : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DehnReduceClosedSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_dehnReduceClosedSharp hclosed

end SmallCancellationRouter
end GroupApproximation
