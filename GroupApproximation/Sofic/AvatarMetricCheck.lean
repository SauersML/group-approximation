import GroupApproximation.Sofic.BespokeRouterGateAssembly
import GroupApproximation.Sofic.GreendlingerCombinatorics

/-!
# The avatar exponent code, verified: `C'(1/8)`, no block powers, protected ball

`notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md` designs the router's relator family
as an *exponent code* over the two-letter avatar alphabet: with `L` blocks,
stride `K` and `V` avatar-carrying generators,

    W_ν  :=  ∏_{j=1}^{L}  y₁ · y₂^(K·ν + j),

positive words whose `y₂`-exponents are globally distinct.  The note lists four
properties the family must have, and names the Lean discharge of each.  This
module is that discharge, stated over the word layer of
`Sofic.SmallCancellationRouter` (`symmetrization`, `IsPiece`,
`MetricSmallCancellation`) and threaded into the router's two consumption
points.

## What is proved, and against what

The explicit family lives in a sibling module.  Nothing here depends on it:
every theorem is stated against `AvatarMetricData`, a bundle of the *checkable*
facts an exponent-code family has — a length floor, a `y₂`-run ceiling, the
pinning property, one unique cyclic mark per relator, and two numeric margins.
The sibling supplies that bundle; everything downstream of it is proved.

* **(a) Junction control.**  `code_injective`: the code `(ν, j) ↦ K·ν + j` is
  injective as soon as `L ≤ K`, so no two positions of the system carry the same
  exponent.  `junction_residue`: at a junction `W_x^{±} W_{x'}^{∓}` the two
  `y₂`-runs that meet cancel down to a run of exponent `K·|x − x'|`, which is
  *nonzero* whenever the avatars differ — the junction never eats past the run,
  so one normalization pass leaves a cyclically reduced word — and at most `K·V`,
  so junction runs are code-sized and the run ceiling survives rewriting.

* **(b) Piece pinning → `C'(1/8)`.**  `length_le_of_runs_bounded` is the
  counting half: in a word whose `y₂`-runs are bounded by `A`, a window carrying
  at most `k` `y₁`-letters is at most `k·(A + 1) + A` long.  So a window of
  length `3·A + 3` spans two consecutive complete `y₂`-runs, at least one of
  which is a code run rather than a junction residue
  (`code_ne_mul_stride`), and its exponent pins the position — that is the
  `pinned` field — while a piece cannot do that, because it prefixes two
  *different* symmetrized relators.  `metric_eighth` turns the resulting piece
  ceiling and the relator floor into `MetricSmallCancellation R (1/8)` by one
  inequality.

  The threshold is *three* separators, not the design note's two: a window
  spanning one complete run pins nothing when that run is a junction residue,
  since a residue records only a difference of avatar indices.  Two consecutive
  runs always meet a code run, because a junction leaves at most one residue.

* **(c) No block powers.**  `not_isProperPower_of_unique_mark` is the general
  fact: if some property of the cyclic word holds at exactly one cyclic position,
  the word is not a block power.  A rotation fixing the word would translate that
  position onto another one, and the exponent sequence being strictly increasing
  along the blocks is exactly what makes a position's exponent unique.  The
  design note's shortcut — "the arc exceeds half" — is *refuted* by
  `PeriodicOverlap.not_isProperPower_of_two_mul_length_le`, so the translation
  argument is used and the Fine–Wilf strand is not.

* **(d) Protected ball.**  `protectedBall_of_word`: §1's padding floor gives
  `2·|W_d| ≤ min |r|` directly, because symmetrization preserves length
  (`length_eq_of_mem_symmetrization`).

## The threading, which only runs one way

`metric_sixth` fills `RouterRelatorDesign.metric` by
`BespokeRouter.metricSmallCancellation_mono`, and the *same* `C'(1/8)` proof is
what `routerConclusions_of_check` hands to
`RouterRelatorDesign.routerConclusions_of_sharpGate`.  Monotonicity runs
`C'(1/8) → C'(1/6)` and never back, so the landed `1/6` field can never supply
the gate call: both consumers are fed from `metric_eighth`.

## Decidability, and why it is not spent here

Every field of `AvatarMetricData` reduces to a finite check on an explicit
family — `uniqueMark` and `runs_short` range over the finitely many rotations and
windows of finitely many relators, `pinned` over their finitely many common
prefixes, and `leadCode` is by design a computable reading.  They are
nevertheless *stated*, not computed: the relators of this family are thousands of
letters long, and a kernel-level `decide` over normal forms of words that size is
the repository's standard timeout.  The arithmetic above is deliberately
inequality-only for the same reason, and `runs_short_of_doubled` exists so that
the run check is two explicit words per relator rather than a quantifier over
rotations.
-/

namespace GroupApproximation
namespace AvatarMetricCheck

open SmallCancellationRouter

/-! ## 0.  The avatar alphabet

Two generators, `Fin 2`.  Index `0` is `y₁`, the block separator; index `1` is
`y₂`, whose runs carry the exponent code. -/

/-- The positive `y₁`-letter: the separator that begins each code block. -/
def genOne : Fin 2 × Bool := (0, true)

/-- The positive `y₂`-letter: the letter whose runs carry the exponents. -/
def genTwo : Fin 2 × Bool := (1, true)

/-- Whether a letter is a `y₁`-letter, of either sign.  Its complement — the
`y₂`-letters — is what a *run* is made of. -/
def isGenOne (c : Fin 2 × Bool) : Bool := decide (c.1 = 0)

/-! ## 1.  Counting: how far a window runs without meeting a separator

The one combinatorial input the piece bound needs.  In a word all of whose
separator-free stretches are at most `A` long, the length is controlled by the
number of separators; a window carrying at most `k` separators is at most
`k·(A + 1) + A` long, so any longer window spans more than `k − 1` complete
runs. -/

/-- The counting induction, carrying the length `k` of the separator-free
stretch already consumed to the left of the window.  The accumulator is what
makes the induction go through: without it the step that keeps a separator-free
head has no budget to charge the head to. -/
private theorem length_add_le_aux {β : Type*} (q : β → Bool) (A : ℕ) :
    ∀ w : List β,
      (∀ u : List β, u <:+: w → (∀ x ∈ u, q x = false) → u.length ≤ A) →
      ∀ k : ℕ,
        (∀ u : List β, u <+: w → (∀ x ∈ u, q x = false) → u.length + k ≤ A) →
        w.length + k ≤ w.countP q * (A + 1) + A := by
  intro w
  induction w with
  | nil =>
      intro _ k hpre
      have h0 := hpre [] List.nil_prefix (by simp)
      simpa using h0
  | cons x t ih =>
      intro hinf k hpre
      have htail : t <:+: x :: t := (List.suffix_cons x t).isInfix
      have hinf' : ∀ u : List β, u <:+: t → (∀ y ∈ u, q y = false) → u.length ≤ A :=
        fun u hu hfree => hinf u (hu.trans htail) hfree
      obtain ⟨c, hc⟩ : ∃ c, t.countP q = c := ⟨_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P, c * (A + 1) = P := ⟨_, rfl⟩
      by_cases hqx : q x = true
      · have hcount : (x :: t).countP q = c + 1 := by
          simp [hqx, hc]
        have hk : k ≤ A := by
          have h0 := hpre [] List.nil_prefix (by simp)
          simpa using h0
        have hIH := ih hinf' 0 (fun u hu hfree => by
          have h1 := hinf' u hu.isInfix hfree
          omega)
        rw [hc, hP] at hIH
        have hexp : (c + 1) * (A + 1) = P + (A + 1) := by
          rw [← hP]; ring
        rw [hcount, hexp]
        simp only [List.length_cons]
        clear hexp hP hc
        omega
      · have hqx' : q x = false := by simpa using hqx
        have hcount : (x :: t).countP q = c := by
          simp [hqx', hc]
        have hIH := ih hinf' (k + 1) (fun u hu hfree => by
          have hpc : x :: u <+: x :: t := by
            obtain ⟨e, he⟩ := hu
            exact ⟨e, by rw [← he]; simp⟩
          have h1 := hpre (x :: u) hpc (by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hqx'
            · exact hfree y hy')
          simp only [List.length_cons] at h1
          omega)
        rw [hc, hP] at hIH
        rw [hcount, hP]
        simp only [List.length_cons]
        clear hP hc
        omega

/-- **The block count controls the length.**  If every separator-free stretch of
`w` is at most `A` long, then `w` is at most `(#separators)·(A + 1) + A` long. -/
theorem length_le_of_runs_bounded {β : Type*} (q : β → Bool) (A : ℕ) (w : List β)
    (hruns : ∀ u : List β, u <:+: w → (∀ x ∈ u, q x = false) → u.length ≤ A) :
    w.length ≤ w.countP q * (A + 1) + A := by
  have h := length_add_le_aux q A w hruns 0
    (fun u hu hfree => by
      have h1 := hruns u hu.isInfix hfree
      omega)
  simpa using h

/-- **A window with at most `k` separators is short.**  A window carrying `k`
separators meets at most `k + 1` runs, so it is at most `k·(A + 1) + A` long. -/
theorem length_le_of_countP_le {β : Type*} (q : β → Bool) (A : ℕ) {w : List β}
    {k : ℕ} (hcount : w.countP q ≤ k)
    (hruns : ∀ u : List β, u <:+: w → (∀ x ∈ u, q x = false) → u.length ≤ A) :
    w.length ≤ k * (A + 1) + A := by
  have h := length_le_of_runs_bounded q A w hruns
  have h2 : w.countP q * (A + 1) ≤ k * (A + 1) :=
    Nat.mul_le_mul hcount (Nat.le_refl (A + 1))
  obtain ⟨P, hP⟩ : ∃ P, w.countP q * (A + 1) = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, k * (A + 1) = Q := ⟨_, rfl⟩
  rw [hP] at h h2
  rw [hQ] at h2 ⊢
  clear hP hQ
  omega

/-- **A long window carries many separators.**  The contrapositive of
`length_le_of_countP_le`, and the shape the piece bound consumes: a window
longer than `k·(A + 1) + A` meets more than `k` separators, hence spans more
than `k − 1` complete runs. -/
theorem lt_countP_of_length {β : Type*} (q : β → Bool) (A : ℕ) {w : List β}
    {k : ℕ}
    (hruns : ∀ u : List β, u <:+: w → (∀ x ∈ u, q x = false) → u.length ≤ A)
    (hlen : k * (A + 1) + A < w.length) : k < w.countP q := by
  by_contra hcon
  have hle : w.countP q ≤ k := by omega
  have h := length_le_of_countP_le q A hle hruns
  omega

/-! ## 2.  Junction control (design property (a))

Two arithmetic facts about the code `(ν, j) ↦ K·ν + j`, `1 ≤ j ≤ L ≤ K`.  The
first says the code is injective, so no exponent is ambiguous anywhere in the
system; the second says a junction leaves a nonzero, code-sized run behind. -/

/-- The stride step: crossing one avatar index costs at least a full block
range. -/
theorem mul_add_le_mul_of_lt {K L a b : ℕ} (hKL : L ≤ K) (hab : a < b) :
    K * a + L ≤ K * b := by
  have h0 : K * (a + 1) ≤ K * b := Nat.mul_le_mul (Nat.le_refl K) (by omega)
  rw [mul_add, mul_one] at h0
  exact le_trans (Nat.add_le_add (Nat.le_refl (K * a)) hKL) h0

/-- **The exponent code is injective.**  With blocks indexed by `1 ≤ j ≤ L` and
a stride `K` at least as large as `L`, the exponent `K·ν + j` determines both the
avatar `ν` and the block `j`.  This is the note's "globally distinct
`y₂`-exponents", and it is what makes a single run pin a position. -/
theorem code_injective {K L ν ν' j j' : ℕ} (hKL : L ≤ K)
    (hj : 1 ≤ j) (hjL : j ≤ L) (hj' : 1 ≤ j') (hj'L : j' ≤ L)
    (h : K * ν + j = K * ν' + j') : ν = ν' ∧ j = j' := by
  have hνν : ν = ν' := by
    rcases Nat.lt_trichotomy ν ν' with hlt | heq | hgt
    · exfalso
      have hle := mul_add_le_mul_of_lt hKL hlt
      obtain ⟨A, hA⟩ : ∃ A, K * ν = A := ⟨_, rfl⟩
      obtain ⟨Bv, hB⟩ : ∃ Bv, K * ν' = Bv := ⟨_, rfl⟩
      rw [hA, hB] at hle
      rw [hA, hB] at h
      clear hA hB
      omega
    · exact heq
    · exfalso
      have hle := mul_add_le_mul_of_lt hKL hgt
      obtain ⟨A, hA⟩ : ∃ A, K * ν = A := ⟨_, rfl⟩
      obtain ⟨Bv, hB⟩ : ∃ Bv, K * ν' = Bv := ⟨_, rfl⟩
      rw [hA, hB] at hle
      rw [hA, hB] at h
      clear hA hB
      omega
  refine ⟨hνν, ?_⟩
  rw [hνν] at h
  exact Nat.add_left_cancel h

/-- **The exponent code, at the zero-based origin.**  The explicit family indexes
its blocks by `j < L` and reads the exponent as `K·ν + (j + 1)`.  That is
`code_injective` shifted by one, recorded here so neither file has to re-index at
the seam; note the hypothesis is still `L ≤ K`, which `K = 2·L` satisfies with
room. -/
theorem code_injective_succ {K L ν ν' j j' : ℕ} (hKL : L ≤ K)
    (hj : j < L) (hj' : j' < L)
    (h : K * ν + (j + 1) = K * ν' + (j' + 1)) : ν = ν' ∧ j = j' := by
  obtain ⟨hν, hjj⟩ :=
    code_injective hKL (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ L)
      (by omega : 1 ≤ j' + 1) (by omega : j' + 1 ≤ L) h
  exact ⟨hν, by omega⟩

/-- **Junction control.**  At a junction between avatars `x' < x ≤ V` the two
`y₂`-runs that meet cancel against one another and leave a single run of
exponent `K·x − K·x'`.  That residue is *positive*, so the cancellation stops
inside the run: the junction never eats through to the neighbouring `y₁`, and one
normalization pass therefore returns a cyclically reduced word of the nominal
shape.  It is also at most `K·V`, so a junction run is no longer than a code run
and the run ceiling of the rewritten relator is the code's own. -/
theorem junction_residue {K V x x' : ℕ} (hK : 0 < K) (hx : x ≤ V) (hlt : x' < x) :
    0 < K * x - K * x' ∧ K * x - K * x' ≤ K * V := by
  have h1 : K * x' + K ≤ K * x := by
    have h0 : K * (x' + 1) ≤ K * x := Nat.mul_le_mul (Nat.le_refl K) (by omega)
    rwa [mul_add, mul_one] at h0
  have h2 : K * x ≤ K * V := Nat.mul_le_mul (Nat.le_refl K) hx
  obtain ⟨A, hA⟩ : ∃ A, K * x = A := ⟨_, rfl⟩
  obtain ⟨Bv, hB⟩ : ∃ Bv, K * x' = Bv := ⟨_, rfl⟩
  obtain ⟨Cv, hC⟩ : ∃ Cv, K * V = Cv := ⟨_, rfl⟩
  rw [hA] at h1 h2 ⊢
  rw [hB] at h1 ⊢
  rw [hC] at h2 ⊢
  clear hA hB hC
  omega

/-- **A junction residue is never a code exponent.**  A junction leaves a run of
length `K·|x − x'|`, a multiple of the stride; a code run has length `K·ν + j`
with `1 ≤ j ≤ L < K`, which is never a multiple of the stride.  So the two kinds
of run live in different residue classes mod `K` and a normalization pass cannot
disguise one as the other.

This is what forces the piece threshold to be *three* separators rather than
two.  A window spanning a single complete run pins nothing if that run happens
to be a junction residue — `K·3` is left by the pair `(5,2)` and by `(7,4)`
alike — whereas a window spanning two consecutive complete runs meets at most
one residue, since each junction leaves at most one, and so always meets a code
run. -/
theorem code_ne_mul_stride {K L a ν j : ℕ} (hLK : L < K)
    (hj : 1 ≤ j) (hjL : j ≤ L) : K * a ≠ K * ν + j := by
  intro h
  obtain ⟨X, hX⟩ : ∃ X, K * a = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, K * ν = Y := ⟨_, rfl⟩
  rcases Nat.lt_or_ge ν a with hlt | hge
  · have h1 : K * (ν + 1) ≤ K * a := Nat.mul_le_mul (Nat.le_refl K) (by omega)
    rw [mul_add, mul_one] at h1
    rw [hX, hY] at h1 h
    clear hX hY
    omega
  · have h2 : K * a ≤ K * ν := Nat.mul_le_mul (Nat.le_refl K) hge
    rw [hX, hY] at h2 h
    clear hX hY
    omega

/-! ## 3.  A unique cyclic mark forbids block powers (design property (c))

The exponent sequence of an avatar word is strictly increasing along its blocks,
so every exponent occurs at exactly one cyclic position of the relator.  A
nontrivial rotation fixing the word would translate that position onto a
different one carrying the same exponent — and there is none.

This is the whole of (c).  Note that the design note's alternative shortcut, that
an overlap exceeding half the word forces a block power, is **false**:
`PeriodicOverlap.not_isProperPower_of_two_mul_length_le` refutes it by machine
check, and no constant fraction of the length can replace it.  The translation
argument below has no length hypothesis at all. -/

/-- The length of the positive `y₂`-run at the front of a word. -/
def leadRun (w : List (Fin 2 × Bool)) : ℕ :=
  (w.takeWhile (fun c => decide (c = genTwo))).length

/-- **The exponent read at a cyclic position.**  A word that begins with a
positive `y₁` reports the exponent of the block it opens; any other word reports
nothing.  Reading this at every rotation of a relator enumerates exactly the
relator's blocks, so `leadCode` is the concrete form of the code the design
assigns. -/
def leadCode (w : List (Fin 2 × Bool)) : Option ℕ :=
  match w with
  | [] => none
  | c :: t => if c = genOne then some (leadRun t) else none

/-- **A uniquely marked cyclic position forbids a block power.**  If a property
of the cyclic word holds at exactly one of its cyclic positions, no nontrivial
rotation can fix the word, so the word is not a block power.

The proof is the translation argument: a rotation by `d` fixing `w` carries the
marked position `p` to `(p + d) mod n`, which is marked as well, hence equal to
`p`, hence `d` is a multiple of `n` — and `0 < d < n`. -/
theorem not_isProperPower_of_unique_mark {β : Type*} {w : List β} (hw : w ≠ [])
    (f : List β → Prop) {p : ℕ} (hp : p < w.length) (hfp : f (w.rotate p))
    (huniq : ∀ q, q < w.length → f (w.rotate q) → q = p) :
    ¬ PeriodicOverlap.IsProperPower w := by
  intro hpp
  obtain ⟨d, hd0, hdlt, hrot⟩ :=
    (PeriodicOverlap.isProperPower_iff_exists_rotate hw).mp hpp
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  have hmod : (p + d) % w.length < w.length := Nat.mod_lt _ hn
  have hval : w.rotate ((p + d) % w.length) = w.rotate p := by
    rw [List.rotate_mod]
    calc w.rotate (p + d) = w.rotate (d + p) := by rw [Nat.add_comm p d]
      _ = (w.rotate d).rotate p := (List.rotate_rotate w d p).symm
      _ = w.rotate p := by rw [hrot]
  have heq : (p + d) % w.length = p := huniq _ hmod (by rw [hval]; exact hfp)
  rcases Nat.lt_or_ge (p + d) w.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hsub : p + d - w.length < w.length := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at heq
    omega

/-! ## 4.  Symmetrization preserves length

Both the piece bound and the protected ball are stated against the symmetrized
family, while the family's own length floor is stated on its relators.  Rotation
and formal inversion are length-preserving, so the two floors agree. -/

/-- Every member of the symmetrization has the length of a relator. -/
theorem length_eq_of_mem_symmetrization {α : Type*} {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    ∃ r ∈ R, w.length = r.length := by
  obtain ⟨r, hr, n, h | h⟩ := hw
  · exact ⟨r, hr, by rw [h, List.length_rotate]⟩
  · exact ⟨r, hr, by rw [h, List.length_rotate, FreeGroup.invRev_length]⟩

/-- **A rotation is a window of the doubled word.**  Read the other way: to
bound the runs of every rotation of `w` it is enough to bound the runs of
`w ++ w`, which is a statement about one explicit word. -/
theorem rotate_infix_append_self {β : Type*} (w : List β) (n : ℕ) :
    w.rotate n <:+: w ++ w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hpos : 0 < w.length := List.length_pos_iff.mpr hw
  have hk : n % w.length ≤ w.length := (Nat.mod_lt _ hpos).le
  have hrot : w.rotate n = w.drop (n % w.length) ++ w.take (n % w.length) := by
    rw [← List.rotate_mod, List.rotate_eq_drop_append_take hk]
  refine ⟨w.take (n % w.length), w.drop (n % w.length), ?_⟩
  have h1 : w.take (n % w.length) ++ w.drop (n % w.length) = w :=
    List.take_append_drop _ _
  rw [hrot, List.append_assoc, List.append_assoc, h1, ← List.append_assoc, h1]

/-- **The run ceiling, transported to the symmetrization.**  A run bound checked
on the doubled relator and on the doubled inverted relator — two explicit words
per relator — gives the bound on every symmetrized member.  This is offered so
that the family's own check never has to quantify over rotations. -/
theorem runs_short_of_doubled {A : ℕ} {R : Set (List (Fin 2 × Bool))}
    (h : ∀ r ∈ R, ∀ u : List (Fin 2 × Bool),
      (u <:+: (r ++ r) ∨ u <:+: (FreeGroup.invRev r ++ FreeGroup.invRev r)) →
      (∀ c ∈ u, isGenOne c = false) → u.length ≤ A) :
    ∀ w ∈ symmetrization R, ∀ u : List (Fin 2 × Bool), u <:+: w →
      (∀ c ∈ u, isGenOne c = false) → u.length ≤ A := by
  rintro w ⟨r, hr, n, rfl | rfl⟩ u hu hfree
  · exact h r hr u (Or.inl (hu.trans (rotate_infix_append_self r n))) hfree
  · exact h r hr u (Or.inr (hu.trans (rotate_infix_append_self _ n))) hfree

/-! ## 5.  The checkable bundle

Everything an exponent-code family owes, in the form a finite explicit family
can be inspected for.  The design parameters `L`, `K`, `V` and the padding floor
enter only through the three numbers `maxExponent`, `relatorFloor` and
`protectedLength` and the two margins between them, so the results below are
generic in the design and survive any retuning of the constants. -/

/-- **The avatar family's verification data.**  `maxExponent` is `A_max = K·V + L`
of the design note, `relatorFloor` is the §1 padding floor read on the rewritten
relators, and `protectedLength` bounds the protected target word. -/
structure AvatarMetricData where
  /-- The relator family, as letter lists over the two-generator alphabet. -/
  relators : Set (List (Fin 2 × Bool))
  /-- `A_max`: the ceiling on the `y₂`-runs the code and its junctions produce. -/
  maxExponent : ℕ
  /-- The common length floor of the family, from §1's padding step. -/
  relatorFloor : ℕ
  /-- A ceiling for the length of the protected target word. -/
  protectedLength : ℕ
  /-- Every relator meets the floor. -/
  relators_long : ∀ r ∈ relators, relatorFloor ≤ r.length
  /-- **The run ceiling.**  No `y₂`-run of a symmetrized relator exceeds the top
  exponent — for code runs because the code stops at `A_max`, for junction runs
  by `junction_residue`.  `runs_short_of_doubled` reduces this to two explicit
  words per relator. -/
  runs_short : ∀ w ∈ symmetrization relators, ∀ u : List (Fin 2 × Bool),
    u <:+: w → (∀ c ∈ u, isGenOne c = false) → u.length ≤ maxExponent
  /-- **Piece pinning.**  A window carrying three `y₁`-letters spans two
  consecutive complete `y₂`-runs, at least one of which is a code run
  (`code_ne_mul_stride`: each junction leaves at most one residue run, and a
  residue is never a code exponent).  By `code_injective` that run's exponent
  names its avatar and block, so the window is pinned to one place in the
  system and cannot prefix two different symmetrized relators.

  **This is the field with real content, and it is a condition on the family,
  not a consequence of the code.**  Pinning the block does not by itself pin the
  *relator*: two distinct relators may legitimately contain the same avatar, and
  if they share a long run of avatars — the same padding tail, say — they share a
  long piece and this fails. The family must therefore be built so that no two
  distinct symmetrized relators agree across two consecutive blocks, which for
  the padding step means a per-relator padding rather than a common one. -/
  pinned : ∀ p : List (Fin 2 × Bool), 3 ≤ p.countP isGenOne →
    ∀ w₁ ∈ symmetrization relators, ∀ w₂ ∈ symmetrization relators,
      p <+: w₁ → p <+: w₂ → w₁ = w₂
  /-- **The unique cyclic mark.**  Each relator has a cyclic position whose
  exponent is read nowhere else in that relator — the strictly increasing
  exponent sequence, localized to one relator. -/
  uniqueMark : ∀ r ∈ relators, ∃ e p : ℕ, p < r.length ∧
    leadCode (r.rotate p) = some e ∧
    ∀ q, q < r.length → leadCode (r.rotate q) = some e → q = p
  /-- The metric margin: eight piece ceilings fit inside one relator floor.

  It is satisfiable at the note's constants, with room.  Writing `P = V + 1`,
  `L = 16·P` and `K = 2·L = 32·P`, an avatar is at least `128·P² + 24·P` long
  while a junction costs at most `2·A_max + 2 = 64·P² − 96·P + 2`, so a relator
  rewritten from `n` avatar letters is at least `n·(64·P² + 120·P − 2)` long
  against a requirement of `8·(3·A_max + 3) = 768·P² − 1152·P + 24`.  Twelve
  letters suffice for every `P ≥ 1`, so the note's padding floor of thirty
  clears it.  The junction cost is the per-junction bound of `junction_residue`,
  which is what a normalization pass removes when the source relator is itself a
  reduced word; a source relator with a cancelling adjacency would cascade and is
  excluded by that reducedness, not by this arithmetic. -/
  metric_margin : 8 * (3 * maxExponent + 3) ≤ relatorFloor
  /-- The protected-ball margin, which is §1's reason for padding at all. -/
  protected_margin : 2 * protectedLength ≤ relatorFloor

namespace AvatarMetricData

variable (C : AvatarMetricData)

/-- The floor holds on the symmetrization too. -/
theorem floor_le_length {w : List (Fin 2 × Bool)}
    (hw : w ∈ symmetrization C.relators) : C.relatorFloor ≤ w.length := by
  obtain ⟨r, hr, hlen⟩ := length_eq_of_mem_symmetrization hw
  rw [hlen]
  exact C.relators_long r hr

/-- The metric margin alone forces a positive floor, which is all the
nonemptiness arguments below need. -/
theorem zero_lt_floor : 0 < C.relatorFloor := by
  have h := C.metric_margin
  omega

/-- Relators are nonempty — derived, not assumed. -/
theorem relator_ne_nil {r : List (Fin 2 × Bool)} (hr : r ∈ C.relators) : r ≠ [] := by
  have h1 := C.relators_long r hr
  have h2 := C.zero_lt_floor
  have h3 : 0 < r.length := by omega
  exact List.length_pos_iff.mp h3

/-! ### (b)  Piece pinning gives the piece ceiling and `C'(1/8)` -/

/-- **Pieces are shorter than `3·A_max + 3`.**  A piece prefixes two *different*
symmetrized relators; were it that long it would carry three `y₁`-letters, hence
span two consecutive complete runs, hence pin the two relators to be equal. -/
theorem piece_length_lt {p : List (Fin 2 × Bool)}
    (hp : IsPiece (symmetrization C.relators) p) :
    p.length < 3 * C.maxExponent + 3 := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, hp₁, hp₂⟩ := hp
  by_contra hcon
  have hlen : 2 * (C.maxExponent + 1) + C.maxExponent < p.length := by omega
  have hcount : 2 < p.countP isGenOne :=
    lt_countP_of_length isGenOne C.maxExponent
      (fun u hu hfree => C.runs_short w₁ hw₁ u (hu.trans hp₁.isInfix) hfree) hlen
  exact hne (C.pinned p (by omega) w₁ hw₁ w₂ hw₂ hp₁ hp₂)

/-- **The family is `C'(1/8)`.**  The piece ceiling against the relator floor,
with the margin clearing the denominator once. -/
theorem metric_eighth : MetricSmallCancellation C.relators (1 / 8) := by
  intro p hp w hw _
  have h1 : p.length < 3 * C.maxExponent + 3 := C.piece_length_lt hp
  have h2 : C.relatorFloor ≤ w.length := C.floor_le_length hw
  have h3 := C.metric_margin
  have hnat : 8 * p.length < w.length := by omega
  have hq : (8 : ℚ) * (p.length : ℚ) < (w.length : ℚ) := by exact_mod_cast hnat
  linarith

/-- **The landed `metric` field.**  Monotonicity in the constant, spent in the
only direction it runs.  The `C'(1/8)` proof above is what the gate call gets;
this weaker reading is what the structure field stores. -/
theorem metric_sixth : MetricSmallCancellation C.relators (1 / 6) :=
  BespokeRouter.metricSmallCancellation_mono
    (show (1 : ℚ) / 8 ≤ 1 / 6 by norm_num) C.metric_eighth

/-! ### (c)  No relator is a block power -/

/-- **No relator is a block power**, in the router's shape. -/
theorem noProperPower : BespokeRouter.NoProperPower C.relators := by
  intro r hr
  obtain ⟨e, p, hp, hcode, huniq⟩ := C.uniqueMark r hr
  exact not_isProperPower_of_unique_mark (C.relator_ne_nil hr)
    (fun z => leadCode z = some e) hp hcode huniq

/-- The same, in the gate file's shape.  The two predicates are definitionally
equal — `BespokeRouter.RouterRelatorDesign.noProperPower_eq_gate` records that —
so no adapter is involved. -/
theorem noProperPower_gate : GreendlingerFreeGate.NoProperPower C.relators :=
  C.noProperPower

/-! ### (d)  The protected ball -/

/-- **The protected ball condition.**  Twice the protected element's reduced
length fits inside every symmetrized relator, by the padding floor. -/
theorem protectedBall {g : FreeGroup (Fin 2)}
    (hg : FreeGroup.norm g ≤ C.protectedLength)
    {r : List (Fin 2 × Bool)} (hr : r ∈ symmetrization C.relators) :
    2 * FreeGroup.norm g ≤ r.length := by
  have h1 := C.floor_le_length hr
  have h2 := C.protected_margin
  omega

/-- The same, in the shape the design's `protectedBall` field is stated in. -/
theorem protectedBall_field {g : FreeGroup (Fin 2)}
    (hg : FreeGroup.norm g ≤ C.protectedLength) :
    ∀ r ∈ symmetrization C.relators, 2 * FreeGroup.norm g ≤ r.length :=
  fun _ hr => C.protectedBall hg hr

/-- **The protected ball from a word bound.**  In practice the protected target
word is written down, so its *word* length is what is known; the reduced length
never exceeds it. -/
theorem protectedBall_of_word {P : List (Fin 2 × Bool)}
    (hP : P.length ≤ C.protectedLength) :
    ∀ r ∈ symmetrization C.relators,
      2 * FreeGroup.norm (FreeGroup.mk P) ≤ r.length :=
  C.protectedBall_field (le_trans FreeGroup.norm_mk_le hP)

end AvatarMetricData

/-! ## 6.  Positive words need no normalization pass

The design note's §2(a) asks for "one normalization pass" because a junction
`W_x^{+} W_{x'}^{-}` or `W_x^{-} W_{x'}^{+}` cancels.  Those are the only two
junction types that do, and both arise from a *sign change* in the source
relator: writing `f` for the first generator of every avatar and `l` for the
last, the four seams are `(l,+)(f,+)`, `(l,+)(l,-)`, `(f,-)(f,+)` and
`(f,-)(l,-)`, of which the middle two collide for **every** choice of `f` and
`l` — no reshaping of the avatar avoids them, since `W · W⁻¹` cancels whatever
`W` is.

So the pass is unavoidable *given sign changes*, and avoidable entirely without
them: a word all of whose letters are positive is cyclically reduced outright,
because reducedness is the chain condition `a.1 = b.1 → a.2 = b.2` and a
positive pair satisfies the conclusion without ever testing the hypothesis.
Every finitely presented group has a finite presentation whose relators are all
positive words — adjoin a generator `x̄` for each `x` with the (positive) relator
`x·x̄`, and rewrite each `x⁻¹` as `x̄` — so this is a presentational choice, of
exactly the kind §1's padding step already is.

These lemmas are stated for an arbitrary alphabet because they are facts about
signs, not about the avatar code. -/

/-- **A letter-positive word is reduced.**  Reducedness is
`List.IsChain (fun a b => a.1 = b.1 → a.2 = b.2)`; when every letter carries the
sign `true` the conclusion holds outright, so the hypothesis is never tested. -/
theorem isReduced_of_forall_positive {α : Type*} {w : List (α × Bool)}
    (h : ∀ c ∈ w, c.2 = true) : FreeGroup.IsReduced w := by
  refine List.isChain_iff_getElem.mpr ?_
  intro i hi _
  have h1 : w[i] ∈ w := List.getElem_mem (by omega)
  have h2 : w[i + 1] ∈ w := List.getElem_mem hi
  rw [h _ h1, h _ h2]

/-- **A letter-positive word is cyclically reduced.**  The wrap seam is tested by
the same condition, and `List.isChain_append` reads both components off the
reducedness of `w ++ w` — which is again a letter-positive word. -/
theorem isCyclicallyReduced_of_forall_positive {α : Type*} {w : List (α × Bool)}
    (h : ∀ c ∈ w, c.2 = true) : FreeGroup.IsCyclicallyReduced w := by
  have happ : ∀ c ∈ w ++ w, c.2 = true := by
    intro c hc
    rcases List.mem_append.mp hc with hc' | hc' <;> exact h c hc'
  have hred : FreeGroup.IsReduced (w ++ w) := isReduced_of_forall_positive happ
  exact ⟨(List.isChain_append.mp hred).1, (List.isChain_append.mp hred).2.2⟩

/-- **A positive word is its own reduced form.**  `toWord ∘ mk` is the identity
on reduced words, and a letter-positive word is reduced.

This is the half of "normalizing a positive word changes nothing" that does not
touch the cyclic layer.  It matters because a family whose members are *defined*
as a normalization has opaque lengths and opaque letters: a length bound proved
about `w` says nothing about `normalize w` until the two are known equal, and
`relatorFloor` and `runs_short` are both length-and-letter statements.  A
positive family should therefore either drop the normalization or prove it
inert; this lemma reduces the second option to the cyclic step alone. -/
theorem toWord_mk_of_forall_positive {α : Type*} [DecidableEq α]
    {w : List (α × Bool)} (h : ∀ c ∈ w, c.2 = true) :
    (FreeGroup.mk w).toWord = w := by
  rw [FreeGroup.toWord_mk, (isReduced_of_forall_positive h).reduce_eq]

/-- **The design's cyclic-reducedness field, for a positive family.**  This is
`RouterRelatorDesign.relators_cyclicallyReduced` outright, with no normalization
pass and no hypothesis beyond the presentational one.

It applies to the rewrites of the padded source and partner relators.  The four
tying relators are *not* positive — each is one generator letter against the
formal inverse of a rewrite — so their two seams are checked separately, by the
sign rule the family module records at `defectTieWord`. -/
theorem relators_cyclicallyReduced_of_positive {R : Set (List (Fin 2 × Bool))}
    (h : ∀ r ∈ R, ∀ c ∈ r, c.2 = true) :
    ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r :=
  fun r hr => isCyclicallyReduced_of_forall_positive (h r hr)

/-- **A positive rewrite of a positive word.**  Concatenating positive blocks
keeps every letter positive, which is the hypothesis the two lemmas above want;
stated on `List.flatten` so that it matches an avatar substitution's shape
without naming it. -/
theorem forall_positive_flatten {α : Type*} {ls : List (List (α × Bool))}
    (h : ∀ u ∈ ls, ∀ c ∈ u, c.2 = true) :
    ∀ c ∈ ls.flatten, c.2 = true := by
  intro c hc
  obtain ⟨u, hu, hcu⟩ := List.mem_flatten.mp hc
  exact h u hu c hcu

/-- **Cyclic reduction fixes a cyclically reduced word.**  Mathlib gives the
conjugating decomposition `conjugator L ++ reduceCyclically L ++ invRev
(conjugator L) = L` but not, as far as this development uses it, the fixed-point
statement.  It follows from the decomposition alone: a nonempty conjugator would
put a letter at the head of `L` and its formal inverse at the tail, which is
precisely what cyclic reducedness forbids, so the conjugator is empty and the
decomposition collapses.

This is the keystone for any family whose members are *defined* as a
normalization.  Together with `toWord_mk_of_forall_positive` it says that
normalizing a letter-positive word returns it unchanged, so length and letter
statements proved before the normalization survive it — without which a relator
floor and a run ceiling proved about the raw rewrite say nothing about the family
actually stored. -/
theorem reduceCyclically_eq_self {α : Type*} [DecidableEq α]
    {L : List (α × Bool)} (h : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.reduceCyclically L = L := by
  have hc := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  rcases eq_or_ne (FreeGroup.reduceCyclically.conjugator L) [] with hnil | hne
  · rw [hnil] at hc
    simpa using hc
  exfalso
  obtain ⟨a, ha⟩ : ∃ a, (FreeGroup.reduceCyclically.conjugator L).head? = some a := by
    cases hcc : FreeGroup.reduceCyclically.conjugator L with
    | nil => exact absurd hcc hne
    | cons x t => exact ⟨x, by rw [hcc]; rfl⟩
  have hinvne : FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L) ≠ [] := by
    intro hz
    apply hne
    have h2 := congrArg FreeGroup.invRev hz
    rwa [FreeGroup.invRev_invRev, invRev_nil] at h2
  have hLhead : L.head? = some a := by
    rw [← hc, List.head?_append, List.head?_append, ha, Option.some_or, Option.some_or]
  have hLlast : L.getLast? = some (invLetter a) := by
    rw [← hc, List.getLast?_append_of_ne_nil _ hinvne, getLast?_invRev, ha]
    rfl
  have hstep := h.2 (invLetter a) (Option.mem_def.mpr hLlast) a
    (Option.mem_def.mpr hLhead)
  have hsnd := hstep rfl
  rcases a with ⟨x, b⟩
  cases b <;> simp [invLetter] at hsnd

/-! ## 7.  Threading into the router

Two consumers, one proof.  `RouterRelatorDesign.metric` stores `C'(1/6)`, which
`metric_sixth` supplies; `routerConclusions_of_sharpGate` needs a constant at
most `1/8`, which `metric_eighth` supplies.  The reverse — reading `1/8` off the
stored `1/6` — is not available and is not attempted. -/

/-- **Both word-combinatorial fields of the router interface**, from the check
bundle and the one open gate.  The design's relator family is the checked one;
everything else about the design is untouched. -/
theorem routerConclusions_of_check {E : Type} [Group E] {N : Subgroup E} {s : E}
    {B : Type} [Group B] (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    D.RouterConclusions :=
  D.routerConclusions_of_sharpGate hgate (le_refl ((1 : ℚ) / 8))
    (by rw [hrel]; exact C.metric_eighth)

/-- **The endpoint's hypothesis, discharged at the checked family.**  Whoever
exhibits a design whose relators pass the check has produced the frozen router
output, modulo the gate and nothing else. -/
theorem nonempty_routingLemmaData_of_check {E : Type} [Group E] {N : Subgroup E}
    [N.Normal] {s : E} {B : Type} [Group B]
    (D : BespokeRouter.RouterRelatorDesign E N s B)
    (C : AvatarMetricData) (hrel : D.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  D.nonempty_routingLemmaData_of_sharpGate hgate (le_refl ((1 : ℚ) / 8))
    (by rw [hrel]; exact C.metric_eighth)

end AvatarMetricCheck
end GroupApproximation
