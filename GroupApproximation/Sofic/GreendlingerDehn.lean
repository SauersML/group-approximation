import GroupApproximation.Sofic.GreendlingerWeight

/-!
# Dehn's algorithm as a rewriting system

`GreendlingerThreeFactor` reaches the gate by a descent on conjugate-product
expressions and leaves one prefix statement open.  This file reaches the same
gate by an entirely different route --- the rewriting system of Dehn's algorithm
--- and leaves open a single, much simpler statement about that system.  The two
routes share no machinery, so a proof of either closes the gate.

## The system

`DehnStep` has two rules on words:

* **free** --- delete a letter and its formal inverse;
* **dehn** --- a symmetrized relator `r = u ++ v` with `2|u| > |r|` lets an
  occurrence of `u` be replaced by `invRev v`, which is strictly shorter.

`DehnReducible R w` says `w` rewrites to the empty word.  Both rules apply to a
subword in any context, and that is the whole point: the system is *context
free*, so a derivation for `u` runs unchanged inside `u ++ v`.

## What is unconditional

Everything except one step, and all of it easy:

* `DehnReducible.append` --- the reducible words are closed under concatenation.
  This is where context-freeness is spent, and it needs no hypothesis at all,
  because a derivation inside `u` never has to free-reduce across the junction.
* `dehnReducible_conjugate` --- `c ++ (s ++ invRev c)` is reducible for every
  symmetrized `s`: one dehn step deletes `s`, then the stem cancels itself.
* `dehnReducible_exprWord` --- hence the *concatenation* of the factors of any
  conjugate-product expression is reducible.
* `greendlinger_of_dehnStep` --- a reduced word admits no free step, so a
  derivation out of a nonempty reduced word must begin with a dehn step, and
  that step exhibits exactly what the Greendlinger conclusion asks for: a
  subword which is a prefix of a symmetrized relator and more than half of it.

## The one step that is missing, and why it is the right one

The concatenation of the factors is reducible; the word we care about is its
*free reduction*.  So the gate follows from

  `DehnReduceClosed R` --- reducibility survives free reduction,

and from nothing else (`greendlingerConclusion_of_dehnReduceClosed`).

This is exactly where small cancellation has to enter, and it can be seen
failing without it.  Take `R = {[a,b]}`, which is not `C'(1/6)`, and
`w = [a², b²] = a a b b a⁻¹ a⁻¹ b⁻¹ b⁻¹`.  Then `w` is reduced, nonempty, and
lies in the normal closure, so some concatenation of conjugates spelling it is
reducible; but every rotation of the symmetrized commutator alternates the two
generators, while `w` contains `aa` and `bb`, so no subword of `w` is more than
half of a relator and `w` is *not* reducible.  Reducibility therefore does not
survive free reduction there.

Note that the system is not confluent even under `C'(1/6)` --- a relator of even
length split in half gives two reducible-to-nothing halves and hence two
distinct normal forms --- so Newman's lemma is not available and the property
needed is the weaker one above: closure of the identity's class.

## What proving it comes down to

`DehnReduceClosed` unfolds to one step: if `A ++ x :: invLetter x :: B` is
reducible then so is `A ++ B`.  Taking the first step of the derivation and
comparing it with the deletion leaves exactly these cases.

* A free step at the same pair --- the two coincide.
* A free step at a disjoint pair --- the steps commute, and the word is shorter.
* A free step overlapping the pair in one letter --- the two results are the
  *same word*, since deleting either of two overlapping cancelling pairs leaves
  the same letters.
* A dehn step disjoint from the pair --- commutes.
* A dehn step whose occurrence `u` covers both letters --- impossible, because
  `u` sits inside a cyclically reduced relator and so is reduced.
* A dehn step whose occurrence ends at one of the two letters, say
  `u = u₀ ++ [x]` inside `r = u ++ v`.  If `2|u₀| > |r|` the very same relator,
  split one letter earlier, rewrites `A ++ B` to the word the step produced, and
  the case closes.

So one case is left: `2|u| > |r|` but `2|u₀| ≤ |r|`, that is `2|u|` equal to
`|r| + 1` or `|r| + 2` --- an occurrence *barely* over half.  There the two
words differ by a half-relator swap that is not itself a rule, and the lengths
give no induction (`|A ++ B|` is at most the step's output, never smaller).
That single case is where `C'(1/6)` has to be spent, and it is the same
mathematics as the hug in `Sofic/GreendlingerThreeFactor`, in a form that needs
no palindromes, no minimal expressions and no weight.

**The continuation, and where it got to.**  The boundary case above is an
artefact of insisting that the replacement be a *rule*: it is the two letters by
which "more than half" fails after one letter moves across the split.
`Sofic/GreendlingerDehnCritical` drops the length condition and works with the
`DehnSwap` relation instead, which is symmetric and lets the letter move for
free, and `Sofic/GreendlingerDehnFree` then discharges the whole free half
(`dehnFreeClosed_of_dehnSwapClosed`): `DehnReduceClosed` follows from swap
closure alone, and the boundary case is gone.  `Sofic/GreendlingerDehnSwap` then
discharges the swap half by the same method, the two together by one induction
on word length.  What survives of the critical pairs is a single overlap of two
*distinct* relators, `PieceOverlapRight` --- one statement, its mirror image
being derived from it by the system's own mirror symmetry.

Unconditional throughout except where `DehnReduceClosed` is named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The rewriting system -/

/-- One step of Dehn's algorithm: delete a cancelling pair, or replace more than
half of a symmetrized relator by the inverse of the rest. -/
inductive DehnStep (R : Set (List (α × Bool))) :
    List (α × Bool) → List (α × Bool) → Prop
  | free (A B : List (α × Bool)) (x : α × Bool) :
      DehnStep R (A ++ (x :: invLetter x :: B)) (A ++ B)
  | dehn (A B u v r : List (α × Bool)) (hr : r ∈ symmetrization R)
      (hsplit : r = u ++ v) (hlong : r.length < 2 * u.length) :
      DehnStep R (A ++ (u ++ B)) (A ++ (FreeGroup.invRev v ++ B))

/-- A word Dehn's algorithm takes to the empty word. -/
def DehnReducible (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  Relation.ReflTransGen (DehnStep R) w []

/-! ## The system is context free -/

/-- **A step applies in any context.**  This is the property the whole route
turns on. -/
theorem DehnStep.context {R : Set (List (α × Bool))} {w w' : List (α × Bool)}
    (h : DehnStep R w w') (A B : List (α × Bool)) :
    DehnStep R (A ++ w ++ B) (A ++ w' ++ B) := by
  cases h with
  | free A₁ B₁ x =>
      have h1 : A ++ (A₁ ++ (x :: invLetter x :: B₁)) ++ B
          = (A ++ A₁) ++ (x :: invLetter x :: (B₁ ++ B)) := by
        simp only [List.append_assoc, List.cons_append]
      have h2 : A ++ (A₁ ++ B₁) ++ B = (A ++ A₁) ++ (B₁ ++ B) := by
        simp only [List.append_assoc]
      rw [h1, h2]
      exact DehnStep.free (A ++ A₁) (B₁ ++ B) x
  | dehn A₁ B₁ u v r hr hsplit hlong =>
      have h1 : A ++ (A₁ ++ (u ++ B₁)) ++ B = (A ++ A₁) ++ (u ++ (B₁ ++ B)) := by
        simp only [List.append_assoc]
      have h2 : A ++ (A₁ ++ (FreeGroup.invRev v ++ B₁)) ++ B
          = (A ++ A₁) ++ (FreeGroup.invRev v ++ (B₁ ++ B)) := by
        simp only [List.append_assoc]
      rw [h1, h2]
      exact DehnStep.dehn (A ++ A₁) (B₁ ++ B) u v r hr hsplit hlong

/-- A whole derivation applies in any context. -/
theorem dehnDerivation_context {R : Set (List (α × Bool))}
    {w w₂ : List (α × Bool)}
    (h : Relation.ReflTransGen (DehnStep R) w w₂) (A B : List (α × Bool)) :
    Relation.ReflTransGen (DehnStep R) (A ++ w ++ B) (A ++ w₂ ++ B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.context A B)

/-! ## Closure properties, all unconditional -/

theorem dehnReducible_nil (R : Set (List (α × Bool))) :
    DehnReducible R ([] : List (α × Bool)) := Relation.ReflTransGen.refl

/-- A cancelling pair is reducible. -/
theorem dehnReducible_pair (R : Set (List (α × Bool))) (x : α × Bool) :
    DehnReducible R [x, invLetter x] :=
  Relation.ReflTransGen.single (DehnStep.free [] [] x)

/-- **Reducible words are closed under concatenation.**  The derivation for the
first word runs inside the concatenation --- no free reduction across the
junction is needed --- and leaves the second word standing. -/
theorem DehnReducible.append {R : Set (List (α × Bool))} {u v : List (α × Bool)}
    (hu : DehnReducible R u) (hv : DehnReducible R v) :
    DehnReducible R (u ++ v) := by
  have h1 : Relation.ReflTransGen (DehnStep R) ([] ++ u ++ v) ([] ++ [] ++ v) :=
    dehnDerivation_context hu [] v
  simp only [List.nil_append] at h1
  exact h1.trans hv

/-- A stem followed by its own inverse is reducible. -/
theorem dehnReducible_append_invRev (R : Set (List (α × Bool))) :
    ∀ c : List (α × Bool), DehnReducible R (c ++ FreeGroup.invRev c) := by
  intro c
  induction c with
  | nil => exact dehnReducible_nil R
  | cons a c' ih =>
      have h1 : (a :: c') ++ FreeGroup.invRev (a :: c')
          = [a] ++ (c' ++ FreeGroup.invRev c') ++ [invLetter a] := by
        rw [invRev_cons]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      have h2 := dehnDerivation_context ih [a] [invLetter a]
      rw [h1]
      refine h2.trans ?_
      simp only [List.append_nil]
      exact dehnReducible_pair R a

/-- **A conjugate of a symmetrized relator is reducible**: one dehn step deletes
the relator, and the stem then cancels itself. -/
theorem dehnReducible_conjugate {R : Set (List (α × Bool))}
    {s : List (α × Bool)} (hs : s ∈ symmetrization R) (hsne : s ≠ [])
    (c : List (α × Bool)) :
    DehnReducible R (c ++ (s ++ FreeGroup.invRev c)) := by
  have hpos : 0 < s.length := List.length_pos_iff.mpr hsne
  have hstep : DehnStep R (c ++ (s ++ FreeGroup.invRev c))
      (c ++ (FreeGroup.invRev [] ++ FreeGroup.invRev c)) :=
    DehnStep.dehn c (FreeGroup.invRev c) s [] s hs (List.append_nil s).symm
      (by omega)
  refine Relation.ReflTransGen.head hstep ?_
  rw [invRev_nil, List.nil_append]
  exact dehnReducible_append_invRev R c

/-! ## Expressions, read as words -/

/-- The word a conjugate-product expression spells, before any reduction. -/
def exprWord [DecidableEq α] :
    List (FreeGroup α × List (α × Bool)) → List (α × Bool)
  | [] => []
  | (x, s) :: e => (x.toWord ++ (s ++ FreeGroup.invRev x.toWord)) ++ exprWord e

@[simp] theorem exprWord_nil [DecidableEq α] :
    exprWord ([] : List (FreeGroup α × List (α × Bool))) = [] := rfl

@[simp] theorem exprWord_cons [DecidableEq α] (x : FreeGroup α) (s : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    exprWord ((x, s) :: e)
      = (x.toWord ++ (s ++ FreeGroup.invRev x.toWord)) ++ exprWord e := rfl

/-- The expression's word spells the element the expression evaluates to. -/
theorem mk_exprWord [DecidableEq α] :
    ∀ e : List (FreeGroup α × List (α × Bool)),
      FreeGroup.mk (exprWord e) = conjEval e := by
  intro e
  induction e with
  | nil =>
      rw [exprWord_nil, conjEval_nil, ← FreeGroup.one_eq_mk]
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [exprWord_cons, conjEval_cons, ← ih]
      simp only [mk_append_mul, mk_invRev_eq_inv, FreeGroup.mk_toWord]
      group

/-- **The concatenation of the factors of an expression is reducible**, with no
hypothesis beyond nonemptiness of the relators. -/
theorem dehnReducible_exprWord [DecidableEq α] {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) :
    ∀ e : List (FreeGroup α × List (α × Bool)), ConjValid R e →
      DehnReducible R (exprWord e) := by
  intro e
  induction e with
  | nil =>
      intro _
      exact dehnReducible_nil R
  | cons xs e ih =>
      intro hv
      obtain ⟨x, s⟩ := xs
      obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
      rw [exprWord_cons]
      exact DehnReducible.append
        (dehnReducible_conjugate h1 (ne_nil_of_mem_symmetrization hRne h1)
          x.toWord) (ih h2)

/-! ## A reduced word admits no free step -/

/-- A word containing a letter beside its inverse is not reduced: it spells an
element shorter than itself. -/
theorem not_isReduced_cancel [DecidableEq α] {A B : List (α × Bool)}
    {x : α × Bool}
    (h : FreeGroup.IsReduced (A ++ (x :: invLetter x :: B))) : False := by
  have hpair : FreeGroup.mk (x :: invLetter x :: B) = FreeGroup.mk B := by
    rw [mk_cons x (invLetter x :: B), mk_cons (invLetter x) B,
      ← mk_singleton_inv]
    group
  have hmk : FreeGroup.mk (A ++ (x :: invLetter x :: B))
      = FreeGroup.mk (A ++ B) := by
    rw [mk_append_mul, mk_append_mul, hpair]
  have h1 : FreeGroup.norm (FreeGroup.mk (A ++ (x :: invLetter x :: B)))
      = (A ++ (x :: invLetter x :: B)).length := norm_mk_of_isReduced h
  have h2 : FreeGroup.norm (FreeGroup.mk (A ++ B)) ≤ (A ++ B).length :=
    norm_mk_le_length _
  rw [hmk] at h1
  rw [List.length_append, List.length_cons, List.length_cons] at h1
  rw [List.length_append] at h2
  omega

/-- **A step out of a reduced word is the Greendlinger conclusion.**  It cannot
be a free step, so it is a dehn step, and a dehn step names a subword which is a
prefix of a symmetrized relator and more than half of it. -/
theorem greendlinger_of_dehnStep [DecidableEq α] {R : Set (List (α × Bool))}
    {w w' : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    (h : DehnStep R w w') :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length := by
  cases h with
  | free A B x => exact (not_isReduced_cancel hw).elim
  | dehn A B u v r hr hsplit hlong =>
      exact ⟨r, hr, u, ⟨A, B, by simp only [List.append_assoc]⟩,
        ⟨v, hsplit.symm⟩, hlong⟩

/-! ## The nonemptiness side condition -/

/-- **`C'(1/6)` forbids an empty relator** as soon as the symmetrization has two
distinct members: the empty word is then a common prefix of two distinct
symmetrized relators, hence a piece, and a piece must be shorter than a sixth of
every relator it prefixes --- which the empty relator is not.

Both routes to the gate carry `∀ r ∈ R, r ≠ []` as a side condition; this
discharges it in every case that is not degenerate, and the degenerate case ---
a symmetrization with at most one member, so `R ⊆ {[]}` or `R` a single rotation
class --- has nothing to prove or no empty relator to begin with. -/
theorem ne_nil_of_metricSmallCancellation {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {s₁ s₂ : List (α × Bool)} (hs₁ : s₁ ∈ symmetrization R)
    (hs₂ : s₂ ∈ symmetrization R) (hne : s₁ ≠ s₂)
    {r : List (α × Bool)} (hr : r ∈ symmetrization R) : r ≠ [] := by
  intro hnil
  have hpiece : IsPiece (symmetrization R) [] :=
    ⟨s₁, hs₁, s₂, hs₂, hne, List.nil_prefix, List.nil_prefix⟩
  have h := hmetric [] hpiece r hr List.nil_prefix
  rw [hnil] at h
  simp at h

/-! ## The gate, along this route -/

/-- **The one statement this route still asks for**: Dehn-reducibility survives
free reduction.

Everything else above is unconditional.  For a family that is not `C'(1/6)` this
fails --- the module header carries the commutator witness --- so it is exactly
where small cancellation has to be spent. -/
def DehnReduceClosed [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ W : List (α × Bool), DehnReducible R W → DehnReducible R (FreeGroup.reduce W)

/-- **The gate, from the rewriting route.**  A nonempty reduced word in the
normal closure is spelled by the free reduction of a reducible word, hence is
reducible, hence admits a dehn step, which is the Greendlinger conclusion. -/
theorem greendlingerConclusion_of_dehnReduceClosed [DecidableEq α]
    {R : Set (List (α × Bool))} (hRne : ∀ r ∈ R, r ≠ [])
    (hclosed : DehnReduceClosed R) : GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e, hv, -, he⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  have hW : DehnReducible R (exprWord e) := dehnReducible_exprWord hRne e hv
  have hmkW : FreeGroup.mk (exprWord e) = FreeGroup.mk w := by
    rw [mk_exprWord, he]
  have hredW : FreeGroup.reduce (exprWord e) = w := by
    have hb := FreeGroup.reduce.sound hmkW
    rwa [hw.reduce_eq] at hb
  have hwD : DehnReducible R w := by
    have hb := hclosed (exprWord e) hW
    rwa [hredW] at hb
  rcases Relation.ReflTransGen.cases_head hwD with hnil | ⟨w', hstep, -⟩
  · exact absurd hnil hwne
  · exact greendlinger_of_dehnStep hw hstep

end SmallCancellationRouter
end GroupApproximation
