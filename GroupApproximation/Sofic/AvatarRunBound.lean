import GroupApproximation.Sofic.AvatarWordFamily

/-!
# The run bound: a block word has no long separator-free window

`AvatarMetricCheck.AvatarMetricData.runs_short` asks that no `y₂`-run of a
symmetrized relator exceed the top exponent.  For the avatar family this is not
an assumption about the caller's words but a consequence of their *shape*: every
relator is a concatenation of blocks `y₁·y₂^e` with `e` a code exponent, and a
window carrying no `y₁` therefore sits inside a single block.

This file proves that, by induction, and hands the result to the family.

## The shape, and why it is stated from the left

`BlockShape A w` says `w` reads as `y₂^{m₀} y₁ y₂^{m₁} y₁ …` with every run at
most `A`, ending either at a separator or in a final run.  Two things make this
the right predicate rather than "a flatten of `blockWord`s".

* It admits a **leading partial run**.  The tying relator `y_j·T_j` begins with a
  bare generator letter, and when `j = 1` that letter is a `y₂` sitting outside
  any block.  A predicate demanding that the word start at a block boundary would
  not cover it.
* It is closed under the operation the proof actually needs.  The induction is on
  the word from the left, so the recursive call is on the tail after a separator,
  which is again a `BlockShape` — whereas an append-based formulation would need
  a decomposition lemma for infixes of a concatenation, which is where this kind
  of proof usually goes wrong.

Everything is reduced to two cons decompositions (`infix_cons_cases`,
`prefix_cons_cases`), each proved from the raw existential by destructuring the
witness and taking `List.tail` of the defining equation.  No lemma about infixes
of appends is used anywhere.

## What is concluded, and what is left

`runBounded_avatarSubst` gives the bound for every rewritten relator, and
`runBounded_blockFlatten_append` gives it for the doubled word `r ++ r` **when
`r` starts at a block boundary** — which covers `R_E`, `R_B`, and the tying
relators with `j = 0`, since `[y₁]` is exactly `blockWord 0`.

The one case not closed here is the doubled tying relator with `j = 1`.  There
`r = y₂ · B`, so `r ++ r` carries a junction run of length (last exponent of `B`)
`+ 1`, which exceeds `A_max` by one and is exactly what the `+ 1` in
`AvatarRouterInstance.maxExponent` was reserved for.  Closing it needs either a
trailing-run bound or the observation that `B ++ [y₂]` is `blockFlatten` of `B`'s
exponent list with its last entry incremented; both are list surgery on the last
element, and neither is written here.  The `Inputs.runs_short` field therefore
still stands, now with three of its four branches discharged by this file.
-/

namespace GroupApproximation
namespace AvatarRunBound

open AvatarMetricCheck
open BespokeRouter.AvatarWordFamily

/-! ## 1.  Two cons decompositions

Both are proved from the definition of `IsInfix`/`IsPrefix` as an existential,
by destructuring the witness and applying `List.tail` to the defining equation.
Nothing about appends is needed. -/

/-- An infix of `x :: t` either starts at the head — and so is a prefix — or
misses the head entirely, and so is an infix of `t`. -/
theorem infix_cons_cases {β : Type*} {u : List β} {x : β} {t : List β}
    (h : u <:+: x :: t) : u <+: x :: t ∨ u <:+: t := by
  obtain ⟨p, e, hpe⟩ := h
  cases p with
  | nil =>
      left
      exact ⟨e, by simpa using hpe⟩
  | cons y p' =>
      right
      refine ⟨p', e, ?_⟩
      have h2 := congrArg List.tail hpe
      simpa using h2

/-- A prefix of `x :: t` is either empty or begins with `x`. -/
theorem prefix_cons_cases {β : Type*} {u : List β} {x : β} {t : List β}
    (h : u <+: x :: t) : u = [] ∨ ∃ u', u = x :: u' ∧ u' <+: t := by
  obtain ⟨e, he⟩ := h
  cases u with
  | nil => exact Or.inl rfl
  | cons a u' =>
      refine Or.inr ⟨u', ?_, ?_⟩
      · have h1 := congrArg List.head? he
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h1
        rw [h1]
      · refine ⟨e, ?_⟩
        have h2 := congrArg List.tail he
        simpa using h2

/-! ## 2.  The run bound, and its cons step -/

/-- **No separator-free window of `w` exceeds `A`.**  This is exactly the shape
`AvatarMetricData.runs_short` asks for, on one word. -/
def RunBounded (A : ℕ) (w : List (Fin 2 × Bool)) : Prop :=
  ∀ u, u <:+: w → (∀ c ∈ u, isGenOne c = false) → u.length ≤ A

theorem runBounded_nil (A : ℕ) : RunBounded A [] := by
  intro u hu _
  have h := hu.length_le
  simp only [List.length_nil, Nat.le_zero] at h
  omega

/-- The cons step: a window either starts at the head, and is then a prefix, or
lies in the tail. -/
theorem runBounded_cons {A : ℕ} {x : Fin 2 × Bool} {t : List (Fin 2 × Bool)}
    (hlead : ∀ u, u <+: x :: t → (∀ c ∈ u, isGenOne c = false) → u.length ≤ A)
    (htail : RunBounded A t) : RunBounded A (x :: t) := by
  intro u hu hfree
  rcases infix_cons_cases hu with hp | hi
  · exact hlead u hp hfree
  · exact htail u hi hfree

/-- A separator-free prefix of a word that begins with a separator is empty. -/
theorem length_le_of_prefix_genOne {A : ℕ} {w : List (Fin 2 × Bool)}
    {u : List (Fin 2 × Bool)} (hu : u <+: genOne :: w)
    (hfree : ∀ c ∈ u, isGenOne c = false) : u.length ≤ A := by
  rcases prefix_cons_cases hu with rfl | ⟨u', hu', -⟩
  · simp
  · exfalso
    have hg := hfree genOne (by rw [hu']; simp)
    simp [isGenOne, genOne] at hg

/-! ## 3.  A leading run, bounded by its own length -/

/-- **The leading run of `y₂^m · y₁ · w` is `m`.**  Read as a bound: a
separator-free prefix cannot reach past the `y₁`, so it is at most `m` long. -/
theorem leadBound_replicate_cons (w : List (Fin 2 × Bool)) :
    ∀ m : ℕ, ∀ u, u <+: List.replicate m genTwo ++ (genOne :: w) →
      (∀ c ∈ u, isGenOne c = false) → u.length ≤ m := by
  intro m
  induction m with
  | zero =>
      intro u hu hfree
      simp only [List.replicate_zero, List.nil_append] at hu
      exact length_le_of_prefix_genOne hu hfree
  | succ m ih =>
      intro u hu hfree
      rw [List.replicate_succ, List.cons_append] at hu
      rcases prefix_cons_cases hu with rfl | ⟨u', hu', hpre⟩
      · simp
      · have h1 := ih u' hpre (fun c hc => hfree c (by rw [hu']; simp [hc]))
        rw [hu']
        simp only [List.length_cons]
        omega

/-- **The run bound for one block, given it for the rest.** -/
theorem runBounded_replicate_cons {A : ℕ} {w : List (Fin 2 × Bool)}
    (hw : RunBounded A w) : ∀ m : ℕ, m ≤ A →
      RunBounded A (List.replicate m genTwo ++ (genOne :: w)) := by
  intro m
  induction m with
  | zero =>
      intro _
      simp only [List.replicate_zero, List.nil_append]
      exact runBounded_cons (fun u hu hfree => length_le_of_prefix_genOne hu hfree) hw
  | succ m ih =>
      intro hm
      rw [List.replicate_succ, List.cons_append]
      refine runBounded_cons ?_ (ih (by omega))
      intro u hu hfree
      have hu2 : u <+: List.replicate (m + 1) genTwo ++ (genOne :: w) := by
        rw [List.replicate_succ, List.cons_append]
        exact hu
      have h1 := leadBound_replicate_cons w (m + 1) u hu2 hfree
      omega

/-! ## 4.  The block shape -/

/-- **A word read as blocks from the left**: a run of at most `A` `y₂`-letters,
then either the end of the word or a `y₁` and another such word. -/
inductive BlockShape (A : ℕ) : List (Fin 2 × Bool) → Prop
  | tail (m : ℕ) (hm : m ≤ A) : BlockShape A (List.replicate m genTwo)
  | run (m : ℕ) (hm : m ≤ A) {w : List (Fin 2 × Bool)} (hw : BlockShape A w) :
      BlockShape A (List.replicate m genTwo ++ (genOne :: w))

/-- **The theorem.**  A block word has no separator-free window longer than its
largest run. -/
theorem runBounded_of_blockShape {A : ℕ} {w : List (Fin 2 × Bool)}
    (h : BlockShape A w) : RunBounded A w := by
  induction h with
  | tail m hm =>
      intro u hu _
      have h1 := hu.length_le
      rw [List.length_replicate] at h1
      omega
  | run m hm _ ih => exact runBounded_replicate_cons ih m hm

/-! ## 5.  Block words from exponent lists -/

/-- The word spelled by a list of exponents. -/
def blockFlatten (es : List ℕ) : List (Fin 2 × Bool) := (es.map blockWord).flatten

theorem blockFlatten_nil : blockFlatten [] = [] := rfl

theorem blockFlatten_cons (e : ℕ) (es : List ℕ) :
    blockFlatten (e :: es) = blockWord e ++ blockFlatten es := by
  simp [blockFlatten]

/-- Concatenating exponent lists concatenates the words — which is why doubling a
relator that starts at a block boundary costs nothing. -/
theorem blockFlatten_append (es es' : List ℕ) :
    blockFlatten (es ++ es') = blockFlatten es ++ blockFlatten es' := by
  simp [blockFlatten]

theorem blockShape_replicate_blockFlatten (A : ℕ) :
    ∀ es : List ℕ, (∀ e ∈ es, e ≤ A) → ∀ m : ℕ, m ≤ A →
      BlockShape A (List.replicate m genTwo ++ blockFlatten es) := by
  intro es
  induction es with
  | nil =>
      intro _ m hm
      rw [blockFlatten_nil, List.append_nil]
      exact BlockShape.tail m hm
  | cons e es ih =>
      intro hes m hm
      rw [blockFlatten_cons]
      have hb : blockWord e ++ blockFlatten es
          = genOne :: (List.replicate e genTwo ++ blockFlatten es) := by
        simp [blockWord, genOne, genTwo]
      rw [hb]
      exact BlockShape.run m hm
        (ih (fun x hx => hes x (List.mem_cons_of_mem _ hx)) e (hes e (by simp)))

theorem blockShape_blockFlatten (A : ℕ) {es : List ℕ} (hes : ∀ e ∈ es, e ≤ A) :
    BlockShape A (blockFlatten es) := by
  have h := blockShape_replicate_blockFlatten A es hes 0 (Nat.zero_le A)
  simpa using h

/-- **Doubling is free at a block boundary.**  `r ++ r` is again a block word, so
the doubled form `runs_short_of_doubled` consumes needs no junction analysis —
provided `r` starts at a boundary. -/
theorem runBounded_blockFlatten_append (A : ℕ) {es es' : List ℕ}
    (hes : ∀ e ∈ es, e ≤ A) (hes' : ∀ e ∈ es', e ≤ A) :
    RunBounded A (blockFlatten es ++ blockFlatten es') := by
  rw [← blockFlatten_append]
  refine runBounded_of_blockShape (blockShape_blockFlatten A ?_)
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hes e h
  · exact hes' e h

/-! ## 6.  The family's words are block words -/

/-- Nesting exponent lists nests their words. -/
theorem blockFlatten_flatten : ∀ ls : List (List ℕ),
    blockFlatten ls.flatten = (ls.map blockFlatten).flatten := by
  intro ls
  induction ls with
  | nil => simp [blockFlatten]
  | cons e es ih =>
      rw [List.flatten_cons, blockFlatten_append, ih, List.map_cons, List.flatten_cons]

/-- **The exponent list of a balanced avatar**: the low and high member of each
block pair, in order.  Under the length-balanced code every avatar carries
`L / 2` such pairs, each summing to `V·L + 1`, which is what makes the avatar
length constant in `ν`. -/
def avatarExps (V L ν : ℕ) : List ℕ :=
  ((List.range (L / 2)).map fun k => [codeLow V ν k, codeHigh V L ν k]).flatten

theorem blockFlatten_avatarWord (V L ν : ℕ) :
    avatarWord V L ν = blockFlatten (avatarExps V L ν) := by
  rw [avatarExps, blockFlatten_flatten]
  simp [avatarWord, pairWord, blockFlatten, List.map_map, Function.comp_def]

/-- The avatar's exponents meet a ceiling as soon as both halves of the code do.
The two hypotheses are exactly `codeLow_le_max` and `codeHigh_le_max` of the
family module, taken as arguments so that this file cites no name that a
retuning of the code could move. -/
theorem avatarExps_le {V L ν A : ℕ}
    (hlow : ∀ k, k < L / 2 → codeLow V ν k ≤ A)
    (hhigh : ∀ k, k < L / 2 → codeHigh V L ν k ≤ A) :
    ∀ e ∈ avatarExps V L ν, e ≤ A := by
  intro e he
  rw [avatarExps, List.mem_flatten] at he
  obtain ⟨u, hu, heu⟩ := he
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
  have hkk : k < L / 2 := List.mem_range.mp hk
  rcases List.mem_cons.mp heu with rfl | he2
  · exact hlow k hkk
  · have hhe : e = codeHigh V L ν k := by simpa using he2
    rw [hhe]
    exact hhigh k hkk

theorem exists_blockFlatten_avatarWord {A : ℕ} (V L ν : ℕ)
    (h : ∀ e ∈ avatarExps V L ν, e ≤ A) :
    ∃ es, (∀ e ∈ es, e ≤ A) ∧ avatarWord V L ν = blockFlatten es :=
  ⟨avatarExps V L ν, h, blockFlatten_avatarWord V L ν⟩

/-- **A positive rewrite is a block word.**  Each positive letter contributes its
avatar unchanged, and avatars are block words, so the exponent lists concatenate.
The negative branch of `avatarSubstLetter` is never reached. -/
theorem exists_blockFlatten_avatarSubst {α : Type} (A : ℕ)
    (Aw : α → List (Fin 2 × Bool))
    (hAw : ∀ i, ∃ es, (∀ e ∈ es, e ≤ A) ∧ Aw i = blockFlatten es) :
    ∀ w : List (α × Bool), (∀ x ∈ w, x.2 = true) →
      ∃ es, (∀ e ∈ es, e ≤ A) ∧ avatarSubst Aw w = blockFlatten es := by
  intro w
  induction w with
  | nil =>
      intro _
      exact ⟨[], by simp, by rw [avatarSubst_nil, blockFlatten_nil]⟩
  | cons x t ih =>
      intro hw
      obtain ⟨es', hes', heq'⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      obtain ⟨x1, x2⟩ := x
      have hx2 : x2 = true := hw (x1, x2) (by simp)
      subst hx2
      obtain ⟨es, hes, heq⟩ := hAw x1
      refine ⟨es ++ es', ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with h | h
        · exact hes e h
        · exact hes' e h
      · rw [avatarSubst_cons, blockFlatten_append, heq', ← heq]
        rfl

/-- **The run bound for a rewritten relator.** -/
theorem runBounded_avatarSubst {α : Type} {A : ℕ} (Aw : α → List (Fin 2 × Bool))
    (hAw : ∀ i, ∃ es, (∀ e ∈ es, e ≤ A) ∧ Aw i = blockFlatten es)
    {w : List (α × Bool)} (hw : ∀ x ∈ w, x.2 = true) :
    RunBounded A (avatarSubst Aw w) := by
  obtain ⟨es, hes, heq⟩ := exists_blockFlatten_avatarSubst A Aw hAw w hw
  rw [heq]
  exact runBounded_of_blockShape (blockShape_blockFlatten A hes)

/-! ## 7.  The code exponents are bounded

Under the length-balanced code the two halves of a block pair are bounded
separately — `codeLow` below the midpoint `V·(L/2)`, `codeHigh` above it, and
both by `V·L`, which is the run ceiling.  Those are facts of the family module
and are taken here as arguments, so that retuning the code moves no name in this
file.  The earlier arithmetic version, keyed to `K·ν + j + 1`, went out with the
stride. -/

/-- **The avatars of the family are block words** at any ceiling both halves of
the code respect.  This is the hypothesis `runBounded_avatarSubst` asks for. -/
theorem exists_blockFlatten_of_bounds {A V L ν : ℕ}
    (hlow : ∀ k, k < L / 2 → codeLow V ν k ≤ A)
    (hhigh : ∀ k, k < L / 2 → codeHigh V L ν k ≤ A) :
    ∃ es, (∀ e ∈ es, e ≤ A) ∧ avatarWord V L ν = blockFlatten es :=
  exists_blockFlatten_avatarWord V L ν (avatarExps_le hlow hhigh)

/-! ## 8.  Transfer to the formal inverse

`runs_short_of_doubled` asks for the bound on `invRev r ++ invRev r` as well.
Formal inversion is an anti-automorphism of lists that preserves the first
coordinate of every letter, so it moves separator-free windows to
separator-free windows of the same length. -/

theorem runBounded_invRev {A : ℕ} {w : List (Fin 2 × Bool)} (h : RunBounded A w) :
    RunBounded A (FreeGroup.invRev w) := by
  intro u hu hfree
  obtain ⟨p, q, hpq⟩ := hu
  have h1 := congrArg FreeGroup.invRev hpq
  rw [FreeGroup.invRev_invRev] at h1
  rw [FreeGroup.invRev_append, FreeGroup.invRev_append, ← List.append_assoc] at h1
  have hinf : FreeGroup.invRev u <:+: w :=
    ⟨FreeGroup.invRev q, FreeGroup.invRev p, h1⟩
  have hfree' : ∀ c ∈ FreeGroup.invRev u, isGenOne c = false := by
    intro c hc
    simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have hcf := hfree c' hc'
    simpa [isGenOne] using hcf
  have h2 := h _ hinf hfree'
  rwa [FreeGroup.invRev_length] at h2

/-! ## 9.  The trailing run, and the last doubled case

The one case §5 left open is the doubled tying relator at `j = 1`, where
`r = y₂ · B` and the junction of `r ++ r` merges `B`'s final run with the leading
`y₂`.  Rather than track trailing runs, note that appending `y₂^t` to a block
word is the *same* block word with its last exponent raised by `t` — so the
merged word is again a `blockFlatten`, and §4's theorem applies unchanged.

`incrLast` is that operation on exponent lists.  The bound it needs is uniform
(`e + t ≤ A` for every exponent, not just the last), which costs nothing: with
`t = 1` it asks that exponents miss the ceiling by one, and the `+ 1` already
built into `AvatarRouterInstance.maxExponent` is exactly that headroom. -/

/-- Raise the last exponent of a list by `t`. -/
def incrLast (t : ℕ) : List ℕ → List ℕ
  | [] => []
  | [e] => [e + t]
  | e :: f :: es => e :: incrLast t (f :: es)

/-- **Appending a run raises the last exponent.** -/
theorem blockFlatten_incrLast (t : ℕ) : ∀ es : List ℕ, es ≠ [] →
    blockFlatten (incrLast t es) = blockFlatten es ++ List.replicate t genTwo := by
  intro es
  induction es with
  | nil => intro h; exact absurd rfl h
  | cons e es ih =>
      intro _
      cases es with
      | nil =>
          have hstep : incrLast t [e] = [e + t] := rfl
          rw [hstep, blockFlatten_cons (e + t) [], blockFlatten_cons e [],
            blockFlatten_nil, List.append_nil, List.append_nil]
          rw [blockWord, blockWord, List.replicate_add]
          rfl
      | cons f es' =>
          have hstep : incrLast t (e :: f :: es') = e :: incrLast t (f :: es') := rfl
          rw [hstep, blockFlatten_cons e (incrLast t (f :: es')),
            blockFlatten_cons e (f :: es'), ih (by simp), List.append_assoc]

/-- The raised exponents still meet the ceiling. -/
theorem mem_incrLast_le {A t : ℕ} : ∀ es : List ℕ, (∀ e ∈ es, e + t ≤ A) →
    ∀ e ∈ incrLast t es, e ≤ A := by
  intro es
  induction es with
  | nil => intro _ e he; simp [incrLast] at he
  | cons a es ih =>
      intro hes e he
      cases es with
      | nil =>
          have hstep : incrLast t [a] = [a + t] := rfl
          rw [hstep] at he
          have hae : e = a + t := by simpa using he
          have := hes a (by simp)
          omega
      | cons f es' =>
          have hstep : incrLast t (a :: f :: es') = a :: incrLast t (f :: es') := rfl
          rw [hstep] at he
          rcases List.mem_cons.mp he with rfl | he'
          · have := hes e (by simp)
            omega
          · exact ih (fun x hx => hes x (List.mem_cons_of_mem _ hx)) e he'

/-- **The last doubled case.**  For a word `y₂^t · B` with `B` a block word, the
doubling `r ++ r` is again `y₂^t` followed by a block word — the merged junction
run being the last exponent of `B` raised by `t`. -/
theorem runBounded_replicate_blockFlatten_double (A t : ℕ) {es : List ℕ}
    (hne : es ≠ []) (hes : ∀ e ∈ es, e + t ≤ A) (ht : t ≤ A) :
    RunBounded A ((List.replicate t genTwo ++ blockFlatten es) ++
      (List.replicate t genTwo ++ blockFlatten es)) := by
  have hkey : (List.replicate t genTwo ++ blockFlatten es) ++
      (List.replicate t genTwo ++ blockFlatten es)
      = List.replicate t genTwo ++ blockFlatten (incrLast t es ++ es) := by
    rw [blockFlatten_append, blockFlatten_incrLast t es hne, List.append_assoc,
      List.append_assoc]
  rw [hkey]
  refine runBounded_of_blockShape (blockShape_replicate_blockFlatten A _ ?_ t ht)
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact mem_incrLast_le es hes e h
  · have := hes e h
    omega

/-! ## 10.  Toward `uniqueMark`: rotation acts on the exponent list

`AvatarMetricData.uniqueMark` asks for an exponent read at exactly one cyclic
position, and its only consumer is `noProperPower`.  The route from the family's
`privateGen` field runs through the exponent list rather than through positions:

* the private generator occurs once in its source relator, so its avatar occurs
  once in the rewrite, so each of that avatar's exponents occurs **once** in the
  rewrite's exponent list;
* an exponent list with an element of count one is not a block power
  (`not_isProperPower_of_count_eq_one`);
* and rotation of the *word* by one block is rotation of the *list* by one entry
  (`blockFlatten_rotate_block`), which is what carries the second fact to the
  first.

The two ends are below.  What is not yet written is the middle: that a rotation
fixing `blockFlatten es` must carry block starts to block starts, hence is a
whole number of blocks, hence induces a rotation of `es`.  That step is genuinely
positional — it needs "the `y₁`-letters of `blockFlatten es` sit exactly at block
starts" — and it is the one place this file still owes work. -/

/-- **Rotating by one block rotates the exponent list.**  `List.rotate_append_length_eq`
does the work: a block word's length is its exponent plus one, and rotating a
concatenation by the length of its first part swaps the parts. -/
theorem blockFlatten_rotate_block (e : ℕ) (es : List ℕ) :
    (blockFlatten (e :: es)).rotate (e + 1) = blockFlatten (es ++ [e]) := by
  rw [blockFlatten_cons, blockFlatten_append]
  have hlen : (blockWord e).length = e + 1 := length_blockWord e
  rw [← hlen, List.rotate_append_length_eq]
  simp [blockFlatten]

/-- The count of a value in a block power is a multiple of its count in the
block. -/
theorem count_flatten_replicate (e : ℕ) (u : List ℕ) :
    ∀ m : ℕ, ((List.replicate m u).flatten).count e = m * u.count e := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, List.count_append, ih,
        add_mul, one_mul]
      exact Nat.add_comm _ _

/-- **An exponent list with a unique entry is not a block power.**  This is the
form `privateGen` delivers: the private generator's avatar contributes exponents
that occur exactly once in the relator's exponent list. -/
theorem not_isProperPower_of_count_eq_one {es : List ℕ} {e : ℕ}
    (h : es.count e = 1) : ¬ PeriodicOverlap.IsProperPower es := by
  rintro ⟨u, m, hm, rfl⟩
  rw [count_flatten_replicate e u m] at h
  obtain ⟨c, hc⟩ : ∃ c, u.count e = c := ⟨_, rfl⟩
  rw [hc] at h
  clear hc
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · omega
  · have h2 : 2 * 1 ≤ m * c := Nat.mul_le_mul hm hcpos
    obtain ⟨P, hP⟩ : ∃ P, m * c = P := ⟨_, rfl⟩
    rw [hP] at h h2
    clear hP
    omega

end AvatarRunBound
end GroupApproximation
