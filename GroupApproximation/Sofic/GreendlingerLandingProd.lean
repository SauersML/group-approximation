import GroupApproximation.Sofic.GreendlingerSharpTwins
import GroupApproximation.Sofic.GreendlingerReducedness

/-!
# The sharp (β) landing production: following the block down the cascade

`GreendlingerSharpTwins` carries the cascade to a general constant and leaves
two `λ`-side residuals, `DeepArcSourceSharp` and `LandingProductionBetaSharp`.
This file attacks the second: the landing obligation outside the
conjugator-absorbed regime, at the family's own constant.

It does so three times, and the last is the one to read first.

## The current residual: `LargeSegmentLands` (§8)

`GreendlingerSharpTwins.LandingProductionBetaSharp'` widens the conclusion to a
disjunction with the hypothesis list untouched.  Against it the cascade drops
out entirely — a head that keeps enough of its own rotation answers on the spot
— and the residual is one statement about one head:
`greendlingerAtSharp_of_two_pieces` fires whenever `|E| < λ·|t|`, so the only
instances still owing anything are those where the head has already lost at
least `λ` of its rotation, and there the block must land.  That restriction is
`LargeSegmentLands`, and §11 shows it is open only in the non-confined case.

    DeepSegmentDichotomy  →  LargeSegmentLands  →  LandingProductionBetaSharp'

## The headline: `LandingProductionBetaSharp` can be walked past

§7 proves `CascadeLandingSharp` — which is what the gate consumes — from
`DeepArcSourceSharp` and a single statement about one head,
`DeepSegmentDichotomy`: the deep eaten segment is a piece, or the block lands.
`LandingProductionBetaSharp` is bypassed, not proved, and
`deepSegmentDichotomy_of_landingProductionBetaSharp` shows the new leaf is
implied by the old obligation, so the trade is one-way in our favour.
`sharpGreendlingerGate_of_deepArcSharp_of_deepSegmentDichotomy` and its `Fin 2`
instance carry it all the way to `SharpGreendlingerGate`.

The reason this is available at all is that `LandingProductionBetaSharp`'s
conclusion is `LandsInSharp` alone, while `CascadeLandingSharp`'s is a
disjunction, and in the shallow regime the *left* disjunct is directly
reachable: the orientation package gives `M = E ++ invRev c`, so
`greendlingerAtSharp_of_two_pieces` fires at `x = |E|` as soon as
`|E| < λ·|t|`, and the head factor delivers the located subword itself.  No
landing site is built and the head conjugator's overhang never enters — which
matters, because §9 shows that overhang is exactly what no local move bounds.

§§3–6 attempted the literal target by a walk down the cascade, and that route is
**dead**: its leaf `StoppingAlternativeBetaSharp` is refuted in §3 by
`not_stoppingAlternativeBetaSharp`.  The reduction theorems there are true but
vacuous and must not be read as progress.  They are kept because the defect is
instructive — a per-factor leaf cannot be stated without the cascade's
provenance for the block length, which is why
`GreendlingerThreeFactor.LeadingConfinement` failed too — and because §2's
cascade moves and §4's step are sound and reusable.

## What the residual regime is, and what it is not

`LandingProductionBetaSharp`'s conclusion is `LandsInSharp` and nothing else.
That is worth saying out loud, because the *disjunction* `CascadeLandingSharp`
states is weaker: `cascadeLandingSharp_of_deepArcSharp_of_landingSharp` commits
to the right disjunct before it calls the hypothesis, so the located conclusion
from the head factor is not available here.  Everything must come from a landing
site inside the tail word.

## The frame: the block is followed, not guessed

The block the head factor loses has length `|M|`, and it eats a prefix of that
length off the tail word.  Where it stops is not a property of any one factor,
so the file does not try to name the landing factor.  It *follows* the block:

* normalize the head of the current tail expression
  (`GreendlingerThreeFactor.exists_palindromic_head`),
* split that head's palindrome at what it loses to everything after it
  (`exists_tail_step_word`),
* ask one question — does the block stop inside this factor, or overrun its
  survivor — and either finish with
  `GreendlingerSharpTwins.landsInSharp_of_confined` or hand the residual block
  on with `landsInSharp_of_overrun`.

`landsInSharp_of_stoppingAlternativeBetaSharp` is that walk, and it is complete:
the bookkeeping of the residual block, the arithmetic that keeps the block
inside the word it is travelling through, the head normalization at every stage,
and the termination are all proved.  The recursion consumes one factor per step
and `LandsInSharp`'s length parameter records the descent, which is what keeps
`greendlingerAtSharp_of_cascadeLandingSharp`'s own induction well-founded once
the site is handed back to it.

`LandsInSharp.compose` and `landsInSharp_of_overrun` are the two cascade moves
`GreendlingerLanding` proves for the half form and the sharp layer does not
carry; they are `λ`-free — the offset field is copied across untouched — so they
are twinned here, verbatim, in §2.

The walk never reads the regime inequality `|M| + j ≤ |c| + |t|`, nor the
orientation package.  That is not an oversight: `CascadeLandingSharp` needs the
inequality for the *inheritance* arithmetic of `greendlingerAtSharp_inherit`,
not for the existence of a landing site.  What the walk does read is
`¬ConjugatorAbsorbedSite c E M e`, which it carries down every step and hands to
the open leaf — so the leaf is asked only about (β)-regime instances, which is
the point of the (α) plumbing.

## The one open leaf

What the walk cannot decide is the question it asks.
`StoppingAlternativeBetaSharp` is that question, quantified over one factor at a
time:

> in an instance carrying no conjugator-absorbed site, a block that stops past a
> factor's conjugator either stops within `λ` of that factor's rotation, or
> overruns the factor's whole survivor — and then there is a further factor for
> it to stop in.

The `λ` enters in exactly one place, the left disjunct, which is the offset
field of `LandsInSharp`; everything else in the predicate is `λ`-free.

## Why the local moves do not close it, and where the danger is

At the adjacent factor the intrusion is `|q| + |E|`: the head conjugator's
overhang past the landing conjugator, plus the relator segment it eats.  The
(α) site is unavailable exactly when `q ≠ []`, as `GreendlingerAlphaPlumb`'s
header records, so the residual regime *is* the nonempty-overhang regime.  There
`GreendlingerBetaBranch.two_mul_hug_le_of_minimal_reroute` gives `2|q| ≤ |t'|`
and the metric condition gives `|E| < λ·|t'|`, so together only

    |q| + |E| < (1/2 + λ)·|t'|,

recorded as `intrusion_lt_half_add_lam_of_hug_of_piece`, where the offset field
of `LandsInSharp` needs `|q| + |E| < λ·|t'|`.  At `λ = 1/6` that is `2/3`
against `1/6`, a factor of four, and the whole shortfall is the overhang: `q`
is a conjugator segment, and no re-expression move bounds a conjugator segment
by a piece.  Sharpening the constant does not help — the two sides scale
differently, and the ratio `(1/2 + λ)/λ` only grows as `λ` shrinks.

The last section says how much of that gap a spectator factor can absorb, and
the answer at a one-factor tail is **none**.  `lt_length_of_landsInSharp_one`
proves that a landing expression of length one cannot place its site anywhere
but in its own palindrome, so `LandsInSharp R lam b V 1` forces `b < |V|`
outright.  Read contrapositively — `ne_nil_of_landingProductionBetaSharp` — a
minimal expression whose tail is a single factor, in the (β) regime, whose head
block eats that factor's whole word refutes `LandingProductionBetaSharp`.  That
is the sharpest falsification handle this file can offer, and the sweep should
be pointed at it before more effort goes into the leaf.

## The spectator slot

The adapters of the last section are the interface for the positive direction:
whatever argument bounds the intrusion, it will end by exhibiting the intruding
segment as a piece, and `intrusion_lt_of_isPiece`,
`intrusion_lt_of_isPiece_rotate`, `intrusion_lt_of_overlap` and
`intrusion_lt_of_overlap_of_reduced` turn that into
`StoppingAlternativeBetaSharp`'s left disjunct verbatim.  The last of them
already spends `GreendlingerReducedness.reducednessVoidsCoincidence`, so on the
(β) branch the distinctness the piece bound needs costs nothing.

Unconditional apart from `StoppingAlternativeBetaSharp`, which is named at every
use.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Two arithmetic twins the walk needs -/

/-- An offset under `λ` of a rotation, at `λ ≤ 1/6`, is under the rotation. -/
theorem lt_length_of_lt_lam_mul {lam : ℚ} (hlam : lam ≤ 1 / 6) {i T : ℕ}
    (hi : (i : ℚ) < lam * (T : ℚ)) : i < T := by
  have hT : (0 : ℚ) ≤ (T : ℚ) := Nat.cast_nonneg T
  have h1 : lam * (T : ℚ) ≤ 1 / 6 * (T : ℚ) :=
    mul_le_mul_of_nonneg_right hlam hT
  have h : (i : ℚ) < (T : ℚ) := by linarith
  exact_mod_cast h

/-- **The offset field, characterized.**  A landing site at the factor in front
of the block exists at *some* admissible offset exactly when the intrusion
itself is admissible.  Both directions, so the left disjunct of
`StoppingAlternativeBetaSharp` is not an over-approximation of what
`landsInSharp_of_confined` consumes — it is that condition, written without the
existential. -/
theorem exists_offset_iff {lam : ℚ} {b n T : ℕ} :
    (∃ i : ℕ, (i : ℚ) < lam * (T : ℚ) ∧ b ≤ n + i)
      ↔ ((b - n : ℕ) : ℚ) < lam * (T : ℚ) := by
  constructor
  · rintro ⟨i, hi, hb⟩
    have hsub : b - n ≤ i := by omega
    have hle : ((b - n : ℕ) : ℚ) ≤ (i : ℚ) := by exact_mod_cast hsub
    linarith
  · intro h
    exact ⟨b - n, h, by omega⟩

/-- The zero offset is admissible as soon as the constant and the rotation are
positive.  This is the sharp form's replacement for `6 * 0 < |t'|`. -/
theorem cast_zero_lt_lam_mul {lam : ℚ} (hlam0 : 0 < lam) {T : ℕ} (hT : 0 < T) :
    ((0 : ℕ) : ℚ) < lam * (T : ℚ) := by
  have h : (0 : ℚ) < (T : ℚ) := by exact_mod_cast hT
  simpa using mul_pos hlam0 h

/-! ## 2.  The two cascade moves, twinned

`GreendlingerLanding.LandsIn.compose` and `landsIn_of_overrun` are the
arithmetic of following a block past a factor.  Both are `λ`-free: the offset
field of the landing site is copied across untouched, and only the survivor and
the drop move.  They are reproved here at `LandsInSharp` because the sharp layer
does not carry them. -/

/-- **Landing sites compose**, at the sharp constant.  A landing site inside
`V₂` for the residual block serves as a landing site inside `A₀ ++ V₂.drop N₀`
for the original one. -/
theorem LandsInSharp.compose [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {b b' N₀ m : ℕ} {V V₂ A₀ : List (α × Bool)}
    (h : LandsInSharp R lam b' V₂ m)
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstep : b + N₀ ≤ b' + A₀.length)
    (harrive : N₀ ≤ b') :
    LandsInSharp R lam b V m := by
  obtain ⟨c', t', f, A, N, i, hf, hV₂, ht', hredp', hmin, hi, hN, hb⟩ := h
  rcases le_or_gt N₀ A.length with hle | hgt
  · refine ⟨c', t', f, A₀ ++ A.drop N₀, N, i, hf, ?_, ht', hredp', hmin, hi,
      hN, ?_⟩
    · rw [hV, hV₂, drop_append_of_le N₀ A _ hle, List.append_assoc]
    · rw [List.length_append, List.length_drop]
      omega
  · refine ⟨c', t', f, A₀, N + (N₀ - A.length), i, hf, ?_, ht', hredp', hmin,
      hi, ?_, ?_⟩
    · rw [hV, hV₂, drop_append_of_ge A N₀ _ (by omega), drop_add]
    · omega
    · omega

/-- **Following an overrunning block one factor on**, at the sharp constant.
When the block is at least as long as what the factor in front of it keeps, the
residual block is `b + N₀ - |A₀|`. -/
theorem landsInSharp_of_overrun [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {b N₀ m : ℕ} {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hover : A₀.length ≤ b)
    (h : LandsInSharp R lam (b + N₀ - A₀.length) V₂ m) :
    LandsInSharp R lam b V m :=
  h.compose hV (by omega) (by omega)

/-! ## 3.  The one open leaf: where a block stops in the factor it meets -/

/-- **REFUTED — the per-factor stopping alternative, over the (β) regime, at a
general constant.**  `not_stoppingAlternativeBetaSharp` below refutes it for
every family with a nonempty reduced symmetrized relator; read that first.  The
statement is kept because §§4–6 are stated against it and because the *shape* of
the defect is the reusable part.

The intended reading, which is what the walk of §5 asks at each factor: a block
of length `b` arriving at the head of a tail word
meets a factor in palindromic normal form `(c', t')`, which keeps `P''` of its
own palindrome and loses `M''` to everything after it.  If the block reaches
past that factor's conjugator, then either it stops within `λ` of the factor's
rotation, or it overruns the factor's survivor entirely — and in the second case
the expression continues, so the block has somewhere left to stop.

The first four arguments are the *original* head data of the instance the walk
started from, carried unchanged down every step so that
`¬ConjugatorAbsorbedSite c E M e` can be handed over: the leaf is asked only
about instances `GreendlingerAlphaPlumb` has not already discharged.

`b ≤ |P''| + |B''|` is the standing invariant of the walk: the block never
outruns the word it is travelling through.  Both `P''` and `B''` are named
rather than derived so that the predicate speaks only about data the walk
already has in hand at the moment it asks the question.

The second disjunct's `f ≠ []` was meant to keep the walk from being handed a
block that has eaten the whole word — `lt_length_of_landsInSharp_one` in §9 is
why the walk cannot recurse there — and it is exactly what makes the predicate
false rather than merely restrictive: in that corner *neither* disjunct holds. -/
def StoppingAlternativeBetaSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c E M : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (c' t' P'' M'' B'' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (b : ℕ),
    ¬ConjugatorAbsorbedSite c E M e →
    t' ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c' t') →
    IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)) →
    palindrome c' t' = P'' ++ M'' →
    (conjEval f).toWord = FreeGroup.invRev M'' ++ B'' →
    c'.length < b → b ≤ P''.length + B''.length →
    ((b - c'.length : ℕ) : ℚ) < lam * (t'.length : ℚ)
      ∨ (P''.length ≤ b ∧ f ≠ [])

/-- **The refutation.**  `StoppingAlternativeBetaSharp` fails for every family
carrying a nonempty reduced symmetrized relator, and the witness costs nothing.

The four arguments `c E M e` occur in exactly one hypothesis,
`¬ConjugatorAbsorbedSite c E M e`, and nowhere else in the statement.  Taking
`e := []` makes that hypothesis *free*: a site names a decomposition
`e = e₁ ++ ((mk c', t') :: f)`, and a list equal to an append ending in a cons
is nonempty, so no site exists over the empty expression.

With the site hypothesis spent for nothing, take a one-factor landing expression
with empty conjugator and let the block be the whole rotation.  Then
`P'' = t'`, `M'' = B'' = []`, every hypothesis holds, and both disjuncts fail:
the left asks `|t'| < λ·|t'|` and the right asks `f ≠ []` of `f = []`.

The defect is over-quantification.  `b` ranges freely over
`|c'| < b ≤ |P''| + |B''|` with nothing tying it to the head block the walk
carries, so the predicate asserts things about blocks the walk never produces —
and it is not a knife-edge, since the same failure occurs with `f ≠ []` whenever
`b = |P''| − 1 > |c'|` and the surviving stretch is at least `λ·|t'|`.  A
per-factor leaf cannot be stated without the cascade's provenance for `b`, which
is the same reason `GreendlingerThreeFactor.LeadingConfinement` failed.

Found by `strike-sweep` while transcribing the predicate for the bounded
adversary search, and recorded rather than repaired because §§7–8 do not go
through it.  `hmin` is a hypothesis rather than a construction only to keep the
witness short; it holds for the expression named, whose conjugator has norm
zero. -/
theorem not_stoppingAlternativeBetaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1)
    {t' : List (α × Bool)} (ht' : t' ∈ symmetrization R)
    (hred : FreeGroup.IsReduced t') (hne : t' ≠ [])
    (hmin : IsMinimalConjExpr R [(FreeGroup.mk ([] : List (α × Bool)), t')]
      (conjEval [(FreeGroup.mk ([] : List (α × Bool)), t')])) :
    ¬StoppingAlternativeBetaSharp R lam := by
  intro halt
  have htpos : 0 < t'.length := List.length_pos_iff.mpr hne
  have htq : (0 : ℚ) < (t'.length : ℚ) := by exact_mod_cast htpos
  have hinvnil : FreeGroup.invRev ([] : List (α × Bool)) = [] :=
    List.length_eq_zero_iff.mp (by rw [FreeGroup.invRev_length]; rfl)
  have hsitefree :
      ¬ConjugatorAbsorbedSite ([] : List (α × Bool)) [] []
        ([] : List (FreeGroup α × List (α × Bool))) := by
    rintro ⟨e₁, f₀, c₀, t₀, d, q, A, N, he, -⟩
    have hlen := congrArg List.length he
    simp only [List.length_nil, List.length_append, List.length_cons] at hlen
    omega
  have hpal : palindrome ([] : List (α × Bool)) t' = t' ++ [] := by
    rw [palindrome_nil, List.append_nil]
  have hredp : FreeGroup.IsReduced (palindrome ([] : List (α × Bool)) t') := by
    rw [palindrome_nil]
    exact hred
  have htailnil : (conjEval ([] : List (FreeGroup α × List (α × Bool)))).toWord
      = FreeGroup.invRev ([] : List (α × Bool)) ++ [] := by
    rw [hinvnil, List.append_nil, conjEval_nil]
    exact FreeGroup.toWord_eq_nil_iff.mpr rfl
  rcases halt [] [] [] [] [] t' t' [] [] [] t'.length hsitefree ht' hredp hmin
      hpal htailnil (by simpa using htpos) (by simp) with hleft | ⟨-, hfne⟩
  · simp only [List.length_nil, Nat.sub_zero] at hleft
    have hb : lam * (t'.length : ℚ) ≤ 1 * (t'.length : ℚ) :=
      mul_le_mul_of_nonneg_right hlam (le_of_lt htq)
    rw [one_mul] at hb
    linarith
  · exact hfne rfl

/-! ## 4.  One step of the walk, with both halves of the word named -/

/-- **The cascade step, with the residual word kept.**
`GreendlingerLanding.exists_tail_step` produces the same split but forgets what
survives beyond the block; the walk needs it, because the block's invariant is
stated against the *whole* word and `B''` is half of it.  `λ`-free. -/
theorem exists_tail_step_word [DecidableEq α]
    {c' t' : List (α × Bool)} {f : List (FreeGroup α × List (α × Bool))}
    (hredp' : FreeGroup.IsReduced (palindrome c' t')) :
    ∃ P'' M'' B'' : List (α × Bool),
      palindrome c' t' = P'' ++ M'' ∧
        (conjEval f).toWord = FreeGroup.invRev M'' ++ B'' ∧
        (conjEval ((FreeGroup.mk c', t') :: f)).toWord = P'' ++ B'' :=
  exists_leading_cancellation
    (w := (conjEval ((FreeGroup.mk c', t') :: f)).toWord)
    FreeGroup.isReduced_toWord hredp' (FreeGroup.mk_toWord).symm

/-- Dropping the destroyed prefix of a word leaves exactly what survives it. -/
theorem drop_invRev_block {M B W : List (α × Bool)}
    (h : W = FreeGroup.invRev M ++ B) : W.drop M.length = B := by
  rw [h, drop_append_of_ge (FreeGroup.invRev M) M.length B
    (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length, Nat.sub_self,
    List.drop_zero]

/-- **The overrun step, in the shape the walk produces it.**  When the block
covers everything the current factor keeps, a landing site for the residual
block inside the rest of the expression is a landing site for the block itself,
with the cascade decomposition read off the two halves of
`exists_tail_step_word` rather than assumed. -/
theorem landsInSharp_of_overrun_step [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {c' t' P'' M'' B'' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {b m : ℕ}
    (hstep : (conjEval ((FreeGroup.mk c', t') :: f)).toWord = P'' ++ B'')
    (htail : (conjEval f).toWord = FreeGroup.invRev M'' ++ B'')
    (hover : P''.length ≤ b)
    (h : LandsInSharp R lam (b + M''.length - P''.length)
      (conjEval f).toWord m) :
    LandsInSharp R lam b (conjEval ((FreeGroup.mk c', t') :: f)).toWord m := by
  refine landsInSharp_of_overrun ?_ hover h
  rw [hstep, drop_invRev_block htail]

/-! ## 5.  The walk -/

/-- **Following the block to wherever it stops.**  For a nonempty minimal
expression and a block no longer than the word that expression spells, the block
has a landing site among the expression's own factors.

The induction is on a bound for the number of factors, and one step is one
factor: normalize the head, split its palindrome at what it loses, and either
stop there — `landsInSharp_of_confined`, with the intrusion `b - |c'|` as the
offset — or hand the residual block `b + |M''| - |P''|` on.  Nothing about the
head factor of the original expression survives past the first step, which is
why the question the walk asks has to be a statement about one factor at a time;
only the (α)-site negation is carried, and it is carried verbatim.

The invariant `b ≤ |W|` is preserved by the overrun step because the word loses
`|P''|` letters of survivor and gains `|M''|` letters of block in exchange, and
the block's own bookkeeping moves by the same two numbers.

`0 < λ` is where the constant is spent, and only there: it is what makes the
zero offset admissible when the block stops inside the landing conjugator. -/
theorem landsInSharp_of_stoppingAlternativeBetaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (halt : StoppingAlternativeBetaSharp R lam)
    {c E M : List (α × Bool)} {e₀ : List (FreeGroup α × List (α × Bool))}
    (hsite : ¬ConjugatorAbsorbedSite c E M e₀) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool))) (b : ℕ),
      e.length ≤ n → e ≠ [] →
      IsMinimalConjExpr R e (conjEval e) →
      b ≤ (conjEval e).toWord.length →
      LandsInSharp R lam b (conjEval e).toWord e.length := by
  intro n
  induction n with
  | zero =>
      intro e b hlen hne _ _
      cases e with
      | nil => exact absurd rfl hne
      | cons x f =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
  | succ n ih =>
      intro e b hlen hne hmin hb
      cases e with
      | nil => exact absurd rfl hne
      | cons x f =>
          obtain ⟨x₁, s₁⟩ := x
          obtain ⟨c', t', ht', hredp', hmin₂⟩ :=
            exists_palindromic_head hR hRne hmin
          have heval : conjEval ((FreeGroup.mk c', t') :: f)
              = conjEval ((x₁, s₁) :: f) := hmin₂.2.1
          have hword : (conjEval ((x₁, s₁) :: f)).toWord
              = (conjEval ((FreeGroup.mk c', t') :: f)).toWord := by rw [heval]
          have hmin₂' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
              (conjEval ((FreeGroup.mk c', t') :: f)) := hmin₂.self_eval
          have ht'pos : 0 < t'.length :=
            List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht')
          obtain ⟨P'', M'', B'', hpal2, htail2, hstep⟩ :=
            exists_tail_step_word (f := f) hredp'
          have hb' : b ≤ P''.length + B''.length := by
            rw [hword, hstep, List.length_append] at hb
            exact hb
          rw [hword]
          rcases le_or_gt b c'.length with hshort | hlong
          · exact landsInSharp_of_confined (i := 0) ht' hredp' hmin₂'
              (cast_zero_lt_lam_mul hlam0 ht'pos) (by omega)
              (by simp only [List.length_cons]; omega)
          · rcases halt c E M e₀ c' t' P'' M'' B'' f b hsite ht' hredp' hmin₂'
                hpal2 htail2 hlong hb' with hoffset | ⟨hover, hfne⟩
            · exact landsInSharp_of_confined (i := b - c'.length) ht' hredp'
                hmin₂' hoffset (by omega)
                (by simp only [List.length_cons]; omega)
            · have hlenf : f.length ≤ n := by
                simp only [List.length_cons] at hlen
                omega
              have hbf : b + M''.length - P''.length
                  ≤ (conjEval f).toWord.length := by
                rw [htail2, List.length_append, FreeGroup.invRev_length]
                omega
              have hrec := ih f (b + M''.length - P''.length) hlenf hfne
                hmin₂.tail hbf
              exact (landsInSharp_of_overrun_step hstep htail2 hover hrec).mono
                (by simp only [List.length_cons]; omega)

/-! ## 6.  The obligation -/

/-- **`LandingProductionBetaSharp`, from the per-factor alternative.**  The
residual obligation is discharged by the walk: the head block is no longer than
the tail word it eats into, the tail of a minimal expression is minimal, and the
tail is nonempty because the block is not.

The orientation package and the regime inequality go unused; what the walk
consumes from the instance is the minimality, the tail decomposition, the fact
that the block is nonempty, and the (α)-site negation.

**Vacuous.**  The implication is a true theorem, but its hypothesis is refuted
by `not_stoppingAlternativeBetaSharp`, so it establishes nothing and must not be
read as progress on `LandingProductionBetaSharp`.  It is kept because the
bookkeeping it assembles — §2's cascade moves, §4's step, the invariant — is
sound and reusable, and because a reader who reaches for the walk should meet
the refutation on the way.  The live route is §§7–8. -/
theorem landingProductionBetaSharp_of_stoppingAlternativeBetaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (halt : StoppingAlternativeBetaSharp R lam) :
    LandingProductionBetaSharp R lam := by
  intro c t e g _P' M B' E _j hmin _ht _hredp _heq htail hlow _hj _hhigh _hM
    _hMinv _hEt _hEpos hsite
  have hlenW : (conjEval e).toWord.length = M.length + B'.length := by
    rw [htail, List.length_append, FreeGroup.invRev_length]
  have hne : e ≠ [] := by
    intro hnil
    have h0 : (conjEval e).toWord = [] := by
      rw [hnil, conjEval_nil]
      exact FreeGroup.toWord_eq_nil_iff.mpr rfl
    rw [h0, List.length_nil] at hlenW
    omega
  exact landsInSharp_of_stoppingAlternativeBetaSharp hR hRne hlam0 halt hsite
    e.length e M.length le_rfl hne hmin.tail (by omega)

/-- **`CascadeLandingSharp` from the deep arc and the per-factor alternative.**
The landing half of the decomposition is now the walk, so the gate's remaining
content is `DeepArcSourceSharp` together with one question about a single
factor. -/
theorem cascadeLandingSharp_of_deepArcSharp_of_stoppingAlternativeBetaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (halt : StoppingAlternativeBetaSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepArcSharp_of_betaSharp hmetric hdeep
    (landingProductionBetaSharp_of_stoppingAlternativeBetaSharp hR hRne hlam0
      halt)

/-- The sharp conclusion, reduced to the deep arc and the per-factor
alternative. -/
theorem greendlingerConclusionSharp_of_deepArcSharp_of_stoppingAlternativeBetaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (halt : StoppingAlternativeBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_deepArcSharp_of_betaSharp hR hRne hlam0 hlam
    hmetric hdeep
    (landingProductionBetaSharp_of_stoppingAlternativeBetaSharp hR hRne hlam0
      halt)

/-! ## 7.  The shorter route: the deep segment, and the left disjunct

Everything above targets `LandingProductionBetaSharp` literally, whose
conclusion is `LandsInSharp` and nothing else.  That is what forces the
overhang into the argument, and §9 records how far short the junction moves
fall.  But the *gate* does not need `LandingProductionBetaSharp`; it needs
`CascadeLandingSharp`, whose conclusion is a disjunction — and in the shallow
regime the left disjunct is directly reachable.

The orientation package already supplies `M = E ++ invRev c`, so
`|M| = |E| + |invRev c|` and `greendlingerAtSharp_of_two_pieces` fires at
`x = |E|` the moment `|E| < λ·|t|`.  The head factor then keeps more than
`(1 − 3λ)` of its own rotation and delivers the located conclusion itself.  No
landing site is built, no cascade decomposition is read, no minimality is
transferred to a later factor, and — the point — the head conjugator's overhang
past the landing conjugator never appears, because the argument never looks at
the landing factor at all.

The first draft of this section asked only "is the deep segment a piece?", and
that is **false**: the buried configuration — the block image sitting inside a
longer next conjugator — matches the segment against conjugator letters, where
minimality bounds it by a half and by nothing sharper.  `DeepSegmentIsPiece`
below records that statement and its refutation; the leaf the route actually
takes is `DeepSegmentDichotomy`, *piece or landing*, with each disjunct asked
exactly where it holds: the overhang configuration gives the piece, the buried
configuration gives the landing at offset zero.

`isPiece_invRev_iff` says what the first disjunct asks, in both directions:
since `invRev E` prefixes `invRev t` for free, being a piece is precisely
reappearing in some symmetrized relator *other* than `invRev t`.  No position,
no length, no fit.  And
`deepSegmentDichotomy_of_landingProductionBetaSharp` is the second direction of
the reduction: the dichotomy is implied by the obligation it replaces, so
nothing is lost by asking for it instead. -/

/-- **REFUTED — the deep segment is always a piece.**  Recorded because it is
the statement the shorter route wants and cannot have, and because the
configuration that kills it is the one that decides the shape of the leaf below.

The counterexample is the *buried* configuration, the branch
`GreendlingerLanding.cascadeLanding_of_leadingConfinement` handles separately:
when the next conjugator is the longer one and the whole block image
`invRev M = c ++ invRev E` sits inside `c'`, the segment `invRev E` is matched
against **conjugator** letters, not relator letters, and nothing makes it a
piece.  Minimality bounds it there by `2|E| ≤ |t|`
(`GreendlingerThreeFactor.eaten_le_of_minimal_reroute`) and by nothing sharper,
which is a half where the sharp budget needs `λ`.

The `¬ConjugatorAbsorbedSite` hypothesis does not exclude that configuration:
the site needs `c = d ++ q`, and in the buried case `c` is strictly shorter than
the landing conjugator, so no such `q` exists and the site is unavailable for a
reason that has nothing to do with the segment. -/
def DeepSegmentIsPiece [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t E M B' : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    M = E ++ FreeGroup.invRev c →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    IsPiece (symmetrization R) (FreeGroup.invRev E)

/-- **OPEN — the (β) dichotomy at one head.**  The repair, and the leaf the
shorter route actually takes: in the (β) regime the deep segment is a piece
**or** the block lands.

The two disjuncts are each asked exactly where they are true.  In the
overhang configuration the segment runs along the landing factor's *rotation*
and is a piece; in the buried configuration it runs along that factor's
*conjugator*, where it is no piece but the block has stopped inside `c'` and
`GreendlingerSharpTwins.landsInSharp_of_confined` supplies the landing at offset
zero.  Neither disjunct alone covers both, which is what
`DeepSegmentIsPiece` above gets wrong.

This is strictly weaker than `LandingProductionBetaSharp`
(`deepSegmentDichotomy_of_landingProductionBetaSharp` proves the implication) and
strictly weaker than `DeepSegmentIsPiece`
(`deepSegmentDichotomy_of_deepSegmentIsPiece`), and it still delivers the gate. -/
def DeepSegmentDichotomy [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t E M P' B' : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → M.length ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    FreeGroup.invRev M = c ++ FreeGroup.invRev E →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    IsPiece (symmetrization R) (FreeGroup.invRev E)
      ∨ LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- The strong form implies the dichotomy, trivially: it is the left disjunct
with no case split. -/
theorem deepSegmentDichotomy_of_deepSegmentIsPiece [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hseg : DeepSegmentIsPiece R) :
    DeepSegmentDichotomy R lam := by
  intro c t E M _P' B' e g hmin ht hredp _heq htail _hlow _hhigh hM _hMinv hEt
    hEpos hsite
  exact Or.inl (hseg c t E M B' e g hmin ht hredp htail hM hEt hEpos hsite)

/-- **The dichotomy is no harder than the obligation it replaces.**  Every
instance of `DeepSegmentDichotomy` is answered by the right disjunct as soon as
`LandingProductionBetaSharp` holds, read at offset `j = 0`.

With `cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy` this is the
second direction: the dichotomy sits strictly between the old obligation and the
gate, so nothing is lost by asking for it instead, and the buried configuration
— which the old obligation also had to answer — is the only place the two
differ in difficulty. -/
theorem deepSegmentDichotomy_of_landingProductionBetaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hbeta : LandingProductionBetaSharp R lam) :
    DeepSegmentDichotomy R lam := by
  intro c t E M P' B' e g hmin ht hredp heq htail hlow hhigh hM hMinv hEt hEpos
    hsite
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
  exact Or.inr (hbeta c t e g P' M B' E 0 hmin ht hredp heq htail hlow
    (cast_zero_lt_lam_mul hlam0 htpos) (by omega) hM hMinv hEt hEpos hsite)

/-- **What the open leaf actually asks, in both directions.**  Half of `IsPiece`
is free for a segment eaten off the end of a rotation: `invRev E` prefixes
`invRev t`, and the symmetrization is closed under `invRev`.  So the segment is
a piece exactly when it also prefixes some symmetrized relator *different from*
`invRev t` — which is the classical reading of "the segment reappears
elsewhere", and is all `DeepSegmentIsPiece` is asking for. -/
theorem isPiece_invRev_iff {R : Set (List (α × Bool))} {t E : List (α × Bool)}
    (ht : t ∈ symmetrization R) (hEt : E <:+ t) :
    IsPiece (symmetrization R) (FreeGroup.invRev E)
      ↔ ∃ s ∈ symmetrization R,
          s ≠ FreeGroup.invRev t ∧ FreeGroup.invRev E <+: s := by
  constructor
  · rintro ⟨w₁, hw₁, w₂, hw₂, hne, hp₁, hp₂⟩
    by_cases h : w₁ = FreeGroup.invRev t
    · exact ⟨w₂, hw₂, fun hc => hne (h.trans hc.symm), hp₂⟩
    · exact ⟨w₁, hw₁, h, hp₁⟩
  · rintro ⟨s, hs, hne, hp⟩
    exact isPiece_of_prefix_two (invRev_mem_symmetrization ht) hs
      (fun hc => hne hc.symm) (invRev_prefix_of_suffix hEt) hp

/-- **`CascadeLandingSharp` from the deep arc and the (β) dichotomy.**  The
shallow regime is split on the existence of a conjugator-absorbed site: the
positive branch is `GreendlingerSharpTwins.cascadeLandingSharp_of_conjugatorAbsorbedSite`
and lands on the right disjunct.  On the negative branch the dichotomy decides —
a piece gives the left disjunct through the two-piece budget, a landing gives the
right one directly.  The deep regime is the deep arc, untouched.

This is the shorter route, and it replaces `LandingProductionBetaSharp` in the
assembly rather than proving it: the landing obligation asks for a site
everywhere, where the disjunction asks only for a located subword, and in the
shallow regime the head factor supplies the second from its own rotation as soon
as the segment it lost is a piece — with the head conjugator's overhang never
entering, since the argument does not look at the landing factor at all. -/
theorem cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam) (hdich : DeepSegmentDichotomy R lam) :
    CascadeLandingSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj
  rcases le_or_gt (M.length + j) (c.length + t.length) with hle | hgt
  · obtain ⟨E, hM, hMinv, hEt, -, hEpos⟩ :=
      eaten_prefix_orientation heq hlow (by omega)
    by_cases hsite : ConjugatorAbsorbedSite c E M e
    · exact cascadeLandingSharp_of_conjugatorAbsorbedSite hmetric hmin ht hEt
        hle hsite
    · rcases hdich c t E M P' B' e g hmin ht hredp heq htail hlow (by omega) hM
          hMinv hEt hEpos hsite with hpiece | hlands
      · have hx : (E.length : ℚ) < lam * (t.length : ℚ) :=
          length_lt_of_eaten hmetric ht hEt hpiece
        have hMlen : M.length ≤ (FreeGroup.invRev c).length + E.length := by
          rw [hM, List.length_append]
          omega
        exact Or.inl (greendlingerAtSharp_of_two_pieces hlam ht heq hMlen hx hj)
      · exact Or.inr ⟨hle, hlands⟩
  · exact Or.inl (hdeep c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt)

/-- The sharp conclusion along the shorter route. -/
theorem greendlingerConclusionSharp_of_deepArcSharp_of_deepSegmentDichotomy
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam) (hdich : DeepSegmentDichotomy R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy hlam hmetric
      hdeep hdich)

/-- **The sharp gate along the shorter route.**  `SharpGreendlingerGate α` from
the deep arc and the (β) dichotomy, with `LandingProductionBetaSharp` bypassed
entirely.

`cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy` needs neither
cyclic reducedness nor nonemptiness of the family, so the bundle
`sharpGreendlingerGate_of_cascadeLandingSharp` hands its `hland` is strictly
more than this route consumes; both are passed through to the deep arc and to
the dichotomy, which may use them. -/
theorem sharpGreendlingerGate_of_deepArcSharp_of_deepSegmentDichotomy
    [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hdich : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepSegmentDichotomy R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    (fun R lam hcyc hRne hlam0 hlam hmetric =>
      cascadeLandingSharp_of_deepArcSharp_of_deepSegmentDichotomy hlam hmetric
        (hdeep R lam hcyc hRne hlam0 hlam hmetric)
        (hdich R lam hcyc hRne hlam0 hlam hmetric))

/-- The same on the router's own alphabet, which is the instance the
construction consumes. -/
theorem sharpGreendlingerGate_fin_two_of_deepArcSharp_of_deepSegmentDichotomy
    (hdeep : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hdich : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepSegmentDichotomy R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_deepArcSharp_of_deepSegmentDichotomy hdeep hdich

/-! ## 8.  The disjunctive target, and the residual re-isolated against it

`GreendlingerSharpTwins.LandingProductionBetaSharp'` widens the conclusion to
`GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨ LandsInSharp …` with the
hypothesis list untouched.  That changes what is left to prove, and by more than
it looks.

Against the primed conclusion the whole cascade drops out.  The walk of §§3–6
existed only because the unprimed conclusion demanded a landing site at *every*
head, so the block had to be followed until it stopped; now a head that keeps
enough of its own rotation answers for itself, on the spot, and the residual is
a statement about **one head** with no cascade in it at all.

And the residual shrinks again.  `greendlingerAtSharp_of_two_pieces` fires
whenever `|E| < λ·|t|`, using nothing but the orientation package, so the only
instances still owing anything are those where the head has lost at least `λ` of
its rotation.  `LargeSegmentLands` is that restriction, and
`landingProductionBetaSharp'_of_largeSegmentLands` is the whole reduction.

The chain of strengths, all proved below or above:

    DeepSegmentDichotomy  →  LargeSegmentLands  →  LandingProductionBetaSharp'

with the first implication by contradiction on the piece bound and the second by
the case split on `|E|`.  `LargeSegmentLands` is the weakest of the three and
the one to attack. -/

/-- **OPEN — a badly damaged head must land.**  `DeepSegmentDichotomy` with the
piece disjunct replaced by its negation as a hypothesis: the block lands
whenever the head has already lost at least `λ` of its rotation, so the head
cannot answer for itself.

This is the residual of `LandingProductionBetaSharp'`, and it is strictly weaker
than everything this file has named before it.  The instances it still owes are
exactly the configurations where the segment `E` is long: the *buried* case
(offset zero suffices), the *meeting* case (offset `|v|` suffices) and the
non-confined case, which is the one that is genuinely open — see §11. -/
def LargeSegmentLands [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t E M P' B' : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → M.length ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    FreeGroup.invRev M = c ++ FreeGroup.invRev E →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    lam * (t.length : ℚ) ≤ (E.length : ℚ) →
    LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- **The disjunctive obligation, from the restricted residual.**  Case on the
size of the segment: a small segment is a piece bound already, and the head
factor answers through the two-piece budget; a large one is handed to
`LargeSegmentLands`.

Nothing else is consumed — no cascade, no landing site built here, and the head
conjugator's overhang never appears. -/
theorem landingProductionBetaSharp'_of_largeSegmentLands [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hls : LargeSegmentLands R lam) :
    LandingProductionBetaSharp' R lam := by
  intro c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv hEt
    hEpos hsite
  rcases le_or_gt (lam * (t.length : ℚ)) (E.length : ℚ) with hlarge | hsmall
  · exact Or.inr (hls c t E M P' B' e g hmin ht hredp heq htail hlow (by omega)
      hM hMinv hEt hEpos hsite hlarge)
  · have hMlen : M.length ≤ (FreeGroup.invRev c).length + E.length := by
      rw [hM, List.length_append]
      omega
    exact Or.inl (greendlingerAtSharp_of_two_pieces hlam ht heq hMlen hsmall hj)

/-- **The dichotomy implies the restricted residual.**  If the segment is a
piece it is shorter than `λ` of the head rotation, which the hypothesis of
`LargeSegmentLands` denies; so the dichotomy's other disjunct is the one that
holds. -/
theorem largeSegmentLands_of_deepSegmentDichotomy [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    (hdich : DeepSegmentDichotomy R lam) : LargeSegmentLands R lam := by
  intro c t E M P' B' e g hmin ht hredp heq htail hlow hhigh hM hMinv hEt hEpos
    hsite hlarge
  rcases hdich c t E M P' B' e g hmin ht hredp heq htail hlow hhigh hM hMinv
      hEt hEpos hsite with hpiece | hlands
  · exfalso
    have hsmall := length_lt_of_eaten hmetric ht hEt hpiece
    linarith
  · exact hlands

/-- The disjunctive obligation from the dichotomy, through the restriction. -/
theorem landingProductionBetaSharp'_of_deepSegmentDichotomy [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdich : DeepSegmentDichotomy R lam) :
    LandingProductionBetaSharp' R lam :=
  landingProductionBetaSharp'_of_largeSegmentLands hlam
    (largeSegmentLands_of_deepSegmentDichotomy hmetric hdich)

/-- **The sharp gate over the restricted residual.**  `SharpGreendlingerGate α`
from the deep arc and `LargeSegmentLands`, through
`GreendlingerSharpTwins.sharpGreendlingerGate_of_deepArcSharp_of_betaSharp'`.

This is the shortest statement of what the lane still owes on the (β) side. -/
theorem sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands
    [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hls : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LargeSegmentLands R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_deepArcSharp_of_betaSharp' hdeep
    (fun R lam hcyc hRne hlam0 hlam hmetric =>
      landingProductionBetaSharp'_of_largeSegmentLands hlam
        (hls R lam hcyc hRne hlam0 hlam hmetric))

/-- The same on the router's own alphabet. -/
theorem sharpGreendlingerGate_fin_two_of_deepArcSharp_of_largeSegmentLands
    (hdeep : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hls : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LargeSegmentLands R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands hdeep hls

/-! ## 9.  No spectator escape at a one-factor tail -/

/-- **A one-factor landing expression cannot absorb a block that eats its
word.**

`LandsInSharp` lets the landing expression be *any* short minimal expression,
not a suffix of the one at hand, and lets a survivor `A` and a drop `N` position
it — which is the freedom a spectator argument would exploit.  At length one
that freedom buys nothing: the landing word is exactly `palindrome c' t'`, whose
length is `2|c'| + |t'|`, and the two fields `N ≤ |c'| + i` and
`b + N ≤ |A| + |c'| + i` together with the offset bound leave the block strictly
inside the word.

The proof is arithmetic once the landing word is computed.  The only relator
facts it spends are that a symmetrized relator is nonempty and that an offset
under `λ` of a rotation is under the rotation, which is where `λ ≤ 1/6` is
read. -/
theorem lt_length_of_landsInSharp_one [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) {b : ℕ} {V : List (α × Bool)}
    (h : LandsInSharp R lam b V 1) : b < V.length := by
  obtain ⟨c'', t'', f, A, N, i, hf, hV, ht'', hredp'', -, hi, hN, hfit⟩ := h
  have hfnil : f = [] := List.length_eq_zero_iff.mp (by omega)
  subst hfnil
  have ht''pos : 0 < t''.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht'')
  have hilt : i < t''.length := lt_length_of_lt_lam_mul hlam hi
  have hW : (conjEval [(FreeGroup.mk c'', t'')]).toWord = palindrome c'' t'' := by
    have h1 : conjEval [(FreeGroup.mk c'', t'')]
        = FreeGroup.mk (palindrome c'' t'') := by
      rw [mk_palindrome, conjEval_cons, conjEval_nil, mul_one]
    rw [h1, FreeGroup.toWord_mk, hredp''.reduce_eq]
  rw [hW] at hV
  have hlenpal : (palindrome c'' t'').length
      = c''.length + t''.length + c''.length := by
    simp [palindrome, FreeGroup.invRev_length, Nat.add_assoc]
  have hlenV : V.length = A.length + ((palindrome c'' t'').length - N) := by
    rw [hV, List.length_append, List.length_drop]
  omega

/-- The same, contrapositively: a block that reaches the end of the word it
travels has no one-factor landing site. -/
theorem not_landsInSharp_one_of_length_le [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) {b : ℕ} {V : List (α × Bool)} (hb : V.length ≤ b) :
    ¬LandsInSharp R lam b V 1 :=
  fun h => absurd (lt_length_of_landsInSharp_one hRne hlam h) (by omega)

/-- **The falsification handle.**  If `LandingProductionBetaSharp` holds, then in
every (β)-regime instance whose tail is a single factor the head block leaves
something of that factor's word standing.

Read the other way, this is a refutation criterion the adversarial sweep can
check directly: exhibit a family satisfying the metric condition at some
`0 < λ ≤ 1/6` and a minimal two-factor expression, in palindromic normal form,
carrying no conjugator-absorbed site, whose leading cancellation destroys the
whole of the second factor's word, and `LandingProductionBetaSharp` is false for
that family.  Nothing in the criterion mentions the constant except through
`λ ≤ 1/6`, so a refutation at one constant is a refutation at every smaller
one. -/
theorem ne_nil_of_landingProductionBetaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hbeta : LandingProductionBetaSharp R lam)
    {c t : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} {P' M B' E : List (α × Bool)} {j : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hhigh : M.length + j ≤ c.length + t.length)
    (hM : M = E ++ FreeGroup.invRev c)
    (hMinv : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hEt : E <:+ t) (hEpos : 0 < E.length)
    (hsite : ¬ConjugatorAbsorbedSite c E M e)
    (hlen : e.length = 1) : B' ≠ [] := by
  intro hnil
  have hland := hbeta c t e g P' M B' E j hmin ht hredp heq htail hlow hj hhigh
    hM hMinv hEt hEpos hsite
  rw [hlen] at hland
  have hlenW : (conjEval e).toWord.length = M.length + B'.length := by
    rw [htail, List.length_append, FreeGroup.invRev_length]
  have hB0 : B'.length = 0 := by simp [hnil]
  exact not_landsInSharp_one_of_length_le hRne hlam (by omega) hland

/-- **The refutation criterion, restated against the disjunctive target.**  A
one-factor tail whose word the block eats whole has no landing site, so
`LargeSegmentLands` fails on it.

This is the sweep to run: a family with `MetricSmallCancellation R lam` for some
`0 < lam ≤ 1/6`, a minimal two-factor expression in palindromic normal form
carrying no conjugator-absorbed site, whose leading cancellation destroys the
whole of the second factor's word (`B' = []`) and whose deep segment is long
(`λ·|t| ≤ |E|`).  Any such instance refutes `LargeSegmentLands`, hence
`LandingProductionBetaSharp'`, hence the disjunctive route.

Both conditions are needed now.  `B' = []` alone refutes only the *unprimed*
obligation, which the widened conclusion has retired: without `λ·|t| ≤ |E|` the
head factor answers for itself through the two-piece budget and no landing site
is owed. -/
theorem ne_nil_of_largeSegmentLands [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hls : LargeSegmentLands R lam)
    {c t E M P' B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hhigh : M.length ≤ c.length + t.length)
    (hM : M = E ++ FreeGroup.invRev c)
    (hMinv : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hEt : E <:+ t) (hEpos : 0 < E.length)
    (hsite : ¬ConjugatorAbsorbedSite c E M e)
    (hlarge : lam * (t.length : ℚ) ≤ (E.length : ℚ))
    (hlen : e.length = 1) : B' ≠ [] := by
  intro hnil
  have hland := hls c t E M P' B' e g hmin ht hredp heq htail hlow hhigh hM
    hMinv hEt hEpos hsite hlarge
  rw [hlen] at hland
  have hlenW : (conjEval e).toWord.length = M.length + B'.length := by
    rw [htail, List.length_append, FreeGroup.invRev_length]
  have hB0 : B'.length = 0 := by simp [hnil]
  exact not_landsInSharp_one_of_length_le hRne hlam (by omega) hland

/-! ## 10.  The spectator slot: turning a piece into the left disjunct -/

/-- **The left disjunct from a piece bound.**  If the block's intrusion into the
landing rotation is covered by a piece prefixing that rotation, the metric
condition gives `StoppingAlternativeBetaSharp`'s left disjunct exactly. -/
theorem intrusion_lt_of_isPiece {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t' D : List (α × Bool)} {b n : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hpiece : IsPiece (symmetrization R) D)
    (hpre : D <+: t') (hfit : b - n ≤ D.length) :
    ((b - n : ℕ) : ℚ) < lam * (t'.length : ℚ) := by
  have h := hmetric D hpiece t' ht' hpre
  have hcast : ((b - n : ℕ) : ℚ) ≤ (D.length : ℚ) := by exact_mod_cast hfit
  linarith

/-- The same, read against a rotation of the landing rotation — which is the
form the chunk bookkeeping produces, since the factor's relator territory begins
at whatever offset the previous junction left. -/
theorem intrusion_lt_of_isPiece_rotate {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t' D : List (α × Bool)} {b n k : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hpiece : IsPiece (symmetrization R) D)
    (hpre : D <+: t'.rotate k) (hfit : b - n ≤ D.length) :
    ((b - n : ℕ) : ℚ) < lam * (t'.length : ℚ) := by
  have h := hmetric D hpiece (t'.rotate k) (rotate_mem_symmetrization ht' k) hpre
  rw [List.length_rotate] at h
  have hcast : ((b - n : ℕ) : ℚ) ≤ (D.length : ℚ) := by exact_mod_cast hfit
  linarith

/-- **The left disjunct from the two-relator overlap.**  The intrusion is a
suffix `E` of the head rotation whose inverse prefixes the landing rotation;
distinctness makes it a piece and the metric condition bounds it, which is
`GreendlingerSharpTwins.intrusion_lt_of_metric` read at the landing rotation. -/
theorem intrusion_lt_of_overlap {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t t' E : List (α × Bool)} {b n k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k)
    (hfit : b - n ≤ E.length) :
    ((b - n : ℕ) : ℚ) < lam * (t'.length : ℚ) := by
  have h := (intrusion_lt_of_metric hmetric ht ht' hEt hintr hne).2
  have hcast : ((b - n : ℕ) : ℚ) ≤ (E.length : ℚ) := by exact_mod_cast hfit
  linarith

/-- **The (β) instance, with distinctness paid by reducedness.**  In the
conjugator-overrun regime the coincidence is void
(`GreendlingerReducedness.invRev_ne_rotate_of_isReduced`), so the overlap bound
applies with no minimality spent and the left disjunct follows from the piece
bound alone. -/
theorem intrusion_lt_of_overlap_of_reduced [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c t t' E : List (α × Bool)} {b n i k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hpal : FreeGroup.IsReduced (palindrome c t))
    (hi : 0 < i) (hic : i ≤ c.length)
    (halign : c.drop (c.length - i) <+: t'.rotate k)
    (hintr : FreeGroup.invRev E <+: t'.rotate (k + i))
    (hfit : b - n ≤ E.length) :
    ((b - n : ℕ) : ℚ) < lam * (t'.length : ℚ) :=
  intrusion_lt_of_overlap hmetric ht ht' hEt hintr
    (invRev_ne_rotate_of_isReduced hpal hi hic halign) hfit

/-- **How far the junction moves fall short.**  In the residual regime the
overhang `q` is nonempty — that is exactly when `GreendlingerAlphaPlumb`'s site
is unavailable — and the intrusion is `|q| + |E|`.  The half-pin bounds the
overhang by half the landing rotation and the metric condition bounds the
segment by `λ` of it, and together they give `(1/2 + λ)` where the offset field
of `LandsInSharp` needs `λ`.

Recorded because it is the precise size of the remaining gap, and because the
gap does not close as the constant sharpens: the ratio `(1/2 + λ)/λ` grows as
`λ` shrinks, so the whole of the shortfall is the overhang, and no
re-expression move bounds a conjugator segment by a piece. -/
theorem intrusion_lt_half_add_lam_of_hug_of_piece {lam q E T : ℚ}
    (hhug : 2 * q ≤ T) (hpiece : E < lam * T) : q + E < T / 2 + lam * T := by
  linarith

/-! ## 11.  What is left of `LargeSegmentLands`, and how to take it

The dichotomy is open, but not uniformly: it is already decided wherever the
block image stays inside the next factor's palindrome, and the argument there is
`GreendlingerLanding.cascadeLanding_of_leadingConfinement` read at the sharp
constant.  Writing it out is mechanical against a compiler and was not attempted
here without one; what follows is the case analysis, with the lemma at each leaf
named, so that it can be.

Normalize the second factor with `GreendlingerThreeFactor.exists_palindromic_snd`
(this is where `hR` and `hRne` are spent) and suppose
`invRev M <+: palindrome c' t'`.  Three cases, on the two conjugators — and the
`λ·|t| ≤ |E|` hypothesis of `LargeSegmentLands` kills the first outright, which
is the second way the disjunctive target pays:

* `|c'| ≤ |c|` — the head conjugator overhangs.  `exists_split_of_overlap_prefix`
  gives `c = c' ++ q` and `q ++ invRev E <+: t'`, hence
  `invRev E <+: t'.rotate |q|`; the coincidence is excluded by
  `GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal` through
  `GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence`, and
  `isPiece_of_overlap` then makes the segment a piece — so `|E| < λ·|t|` and the
  hypothesis is contradicted.  **This case cannot arise.**  The `hfit` side
  condition of `exists_split_of_overlap_prefix` is
  `GreendlingerRegime.swallow_bound_of_minimal'`, which is why writing it out
  still costs a monotonicity step from `λ` to `1/6`.
* `|c| < |c'|` and `|M| ≤ |c'|` — the buried case.  The block has stopped inside
  the landing conjugator, so `landsInSharp_of_confined` at offset `0` gives the
  **right** disjunct; this is where `0 < λ` is spent, through
  `cast_zero_lt_lam_mul`.
* `|c| < |c'|` and `|c'| < |M|` — the block meets the second rotation.  With
  `c' = c ++ y` and `invRev E = y ++ v`, the meeting segment `v` prefixes both
  `t'` and `(invRev t).rotate |y|`, so it is a piece unless the two coincide,
  which `mk_palindrome_mul_eq_one_of_coincidence'` and minimality exclude.  Then
  `landsInSharp_of_confined` at offset `|v|` gives the landing, the fit being
  `meet_length_split` below and the offset bound being the metric condition read
  at `v` directly.

So the residual is the **non-confined** case alone: the block image runs past
what the next factor keeps.  That is the case `LeadingConfinement` asserted away
and the configuration in `GreendlingerThreeFactor`'s header refutes, so it is
genuine content and not bookkeeping.

Read together with §8 the position is: of the four configurations a (β) head can
be in, the overhang one is now answered by the head factor itself, the buried
and meeting ones by a confined landing at offset `0` and `|v|`, and only the
non-confined one is open. -/

/-- **The meet case fits exactly.**  When the second conjugator overhangs the
first by `y` and the deep segment splits as `y ++ v` at the meeting point, the
block ends precisely `|v|` letters into the second rotation — so
`landsInSharp_of_confined` fires at offset `|v|` with no slack to spare, and the
offset bound it needs is the piece bound on `v` and nothing else.

Stated over `ℕ` because that is how the three lengths arrive; the `λ`-side of
the case is one application of the metric condition. -/
theorem meet_length_split {c c' y v E M : ℕ} (hM : M = E + c)
    (hc' : c' = c + y) (hE : E = y + v) : M = c' + v := by
  omega

/-! ## 12.  Audit: `MaximalJunctionSharp` is vacuous

`GreendlingerMaxConjugator`'s route was the other place in the lane where a
conjugator overhang gets beaten, and its header describes the mechanism the
(β) regime needs: at a factor whose conjugator is at least as long as its
neighbour's, the hug is zero and both losses are pieces outright.  Chasing
`not_overrun_into_conjugator` for that mechanism turns up something else, which
is recorded here because it changes what that route is worth.

**`MaximalJunctionSharp` assumes its own content.**  Its intent — the docstring
says it plainly — is that the destroyed part of the rotation *is* a piece.  Its
statement takes `IsPiece (symmetrization R) (t.take x)` as a **hypothesis** and
asserts only the numeric consequence `x < λ·|t|`, which the metric condition
gives for any piece whatever.  `maximalJunctionSharp_of_metric` below proves the
predicate outright from `hmetric`, `0 < λ`, `λ ≤ 1/6` and nonemptiness, with the
four arguments the intent turns on — the two conjugators `c`, `c'`, the
neighbouring rotation `t'` and the domination `|c'| ≤ |c|` — never used.

So `greendlingerAtSharp_of_maximalJunctionSharp` is not conditional on anything:
it is `greendlingerAtSharp_of_two_pieces`, which is what it is defined to be.
Discharging `MaximalJunctionSharp` closes nothing, and a route whose remaining
hypothesis is that predicate is already unconditional and already short of the
gate.  The load-bearing statement on that route is the word-level one the
predicate skips: *that the destroyed part is `t.take x` for a piece*. -/

/-- **The junction predicate follows from the metric condition alone.**  Both
branches are immediate: a piece is under `λ` of every relator it prefixes, and
the `x = 0` branch is `0 < λ·|t|`.

The `x > |t|` corner is not an exception — there `t.take x` is `t` itself, so
the piece hypothesis would make a relator shorter than `λ` of itself, which
`λ ≤ 1/6` forbids; the branch is discharged by contradiction rather than by a
bound.

Stated as an audit result, not as a step: nothing in this file consumes it. -/
theorem maximalJunctionSharp_of_metric {R : Set (List (α × Bool))} {lam : ℚ}
    (hRne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    MaximalJunctionSharp R lam := by
  intro _c t _c' _t' x ht _ht' _hle hp
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
  have htq : (0 : ℚ) < (t.length : ℚ) := by exact_mod_cast htpos
  rcases hp with hpiece | hx0
  · have h := hmetric (t.take x) hpiece t ht (List.take_prefix x t)
    rw [List.length_take] at h
    rcases le_or_gt x t.length with hle | hgt
    · have hmin : min x t.length = x := by omega
      rwa [hmin] at h
    · exfalso
      have hmin : min x t.length = t.length := by omega
      rw [hmin] at h
      have hb : lam * (t.length : ℚ) ≤ 1 / 6 * (t.length : ℚ) :=
        mul_le_mul_of_nonneg_right hlam (le_of_lt htq)
      linarith
  · rw [hx0, Nat.cast_zero]
    exact mul_pos hlam0 htq

end SmallCancellationRouter
end GroupApproximation
