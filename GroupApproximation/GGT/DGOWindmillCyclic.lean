import GroupApproximation.GGT.DGOWindmillSpelling

/-!
# Cyclic reduction of windmill spellings

Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), no. 1156, §5.3, continued from `GGT/DGOWindmillSpelling.lean`.

The windmill induction reads its geometry off the broken path through the
developed apices of a spelling, and for that path to *close up* -- which is what
turns the estimate into a statement about the powers of the element, and so into
loxodromy -- the seam that wraps from the last syllable back to the first has to
be a seam like any other.  A spelling with that extra condition is *cyclically
reduced*, and every element of `G₂` is conjugate to one of three shapes.

## The normal form, and the convention `tail = 1`

`Spelling.normalize` conjugates a spelling by its own trailing letter, moving
that letter to the front:

    `e · (p₁ b₁ ⋯ p_k b_k · e) · e⁻¹ = (e p₁) b₁ p₂ b₂ ⋯ p_k b_k`.

The result has `tail = 1`, the same length, the same directions, and is still
reduced -- the seam relation `Seam u v` looks at `v.pre`, `v.dir` and `u.dir`,
and the *first* syllable never occupies the `v` slot, so changing its `pre`
changes no seam.  Fixing `tail = 1` rather than `head = 1` is what makes the
`n`-th power a literal concatenation: with `tail = 1` the value is
`p₁ b₁ ⋯ p_k b_k` and the value of the `n`-th power is that word written `n`
times, so the syllable list of `gⁿ` is `List.replicate n l |>.flatten` on the
nose.  With DGO's convention (trivial head, letter `a_k` at the end) the copies
would be separated by an `a_k` that has to be folded into the next copy's first
letter at every seam, and the concatenation would not be literal.

## The three terminal shapes

`isCyclicOutcome_of_isValid` is the whole content: for every `g ∈ G₂` one of

1. `g` is conjugate into `G_W`;
2. `g` is conjugate into `Rot d` for some apex `d ∈ C₁`;
3. `g` is conjugate to the value of a **cyclically reduced** spelling with at
   least one syllable and trivial tail.

The induction is on the length of a spelling.  Given a reduced spelling with
trivial tail whose cyclic seam *fails* -- `p₁ • d₁ = d_k`, DGO's
`a_k · d₁ = d_k` -- conjugating by the last syllable `b_k` (that is, by
`p_k b_k`) rotates the word,

    `(p_k b_k) · (p₁ b₁ ⋯ p_{k-1} b_{k-1} p_k b_k) · (p_k b_k)⁻¹
       = p_k b_k p₁ b₁ ⋯ p_{k-1} b_{k-1}`,

and the failed cyclic seam is now the *ordinary* seam between the first two
syllables of the rotated word.  So `exists_isValid_shorter_of_seam` applies at
position zero, the length drops, and the induction hypothesis finishes.

The two short cases are where the hypotheses are spent.

* `k = 0`: the element is the trailing letter, which lies in `G_W`.  Shape 1.
* `k = 1`: the cyclic seam is `p₁ • d₁ ≠ d₁`.  If it fails then `p₁` is an
  element of `G_W` fixing an apex of `C₁`, so **`hfree` forces `p₁ = 1`** and
  the element is the bare rotation `b₁ ∈ Rot d₁`.  Shape 2.  If it holds the
  word is already cyclically reduced, which is shape 3; note that when
  `p₁ ≠ 1` this is *automatic* from `hfree`, so a one-syllable word with a
  nontrivial letter is never in shape 2.

`hfree` -- *no nontrivial element of `G_W` fixes an apex of `C₁`* -- is the only
new hypothesis, and it is genuinely needed rather than convenient: at the
one-point model `G_W` fixes the single direction, `hfree` fails, and the `k = 1`
seam fails for every `p₁`, so without it shape 3 would be empty and the
conclusion false.  It is discharged geometrically at each stage of the windmill
induction, where the apices of `C₁` lie outside the windmill and `G_W` preserves
the windmill.

## Powers

`Spelling.exists_cyclicallyReduced_pow`: for a cyclically reduced `s` with
`tail = 1`, the spelling of `s.eval ^ n` is the `n`-fold concatenation of its
syllable list, it is again cyclically reduced, and its length is `n` times the
original.  The proof is `List.isChain_flatten` over `List.replicate n l`: the
chains inside the copies are the reducedness of `s`, and the chain *between* the
copies is exactly the cyclic seam, applied at every junction by
`List.isChain_replicate_of_rel`.  This is the same argument, in the same
vocabulary, as `FreeGroup.IsCyclicallyReduced.flatten_replicate` in Mathlib.

This lemma is what the geometry consumes: `s.eval ^ n` has a reduced spelling
with `n · k` syllables, hence with `n · k` adjacent-distinct developed apices,
so the broken path grows without bound and `s.eval` has infinite order.  Drawing
that conclusion needs the separation of the family and is not done here.

## Model tests

*The one-point space.*  As in the previous module, `Seam` is identically false
there.  So `CyclicSeam` fails for every nonempty spelling, no spelling is
cyclically reduced, and shape 3 is empty; the theorem then says that every
element of `G₂` is conjugate into `G_W` or into the rotation subgroup.  That is
true there: `G₂ = Rot d · G_W` with `Rot d` normal, so an element is `b a` with
`b ∈ Rot d`, `a ∈ G_W`, and the `k ≤ 1` analysis lands it in shape 1 or 2.
`hfree` fails at that model whenever `G_W ≠ 1`, and the theorem does not claim
otherwise -- it is a hypothesis, so the statement there is about the `G_W = 1`
sub-case, where indeed every element is a bare rotation.

*The infinite dihedral model.*  `G_W = {1, σ₀}`, `C₁ = {p}`, `Rot p = {1, σ_p}`.
`hfree` holds: `σ₀ • p = -p ≠ p`.  The cyclically reduced spellings with
`tail = 1` are the words `σ₀ σ_p σ₀ σ_p ⋯ σ₀ σ_p` -- every `p_j = σ₀`, including
`p₁`, since the cyclic seam is the condition at `p₁` -- and their values are the
translations `(σ₀ σ_p)^k`, which is precisely the set of elements of `⟨σ₀, σ_p⟩`
conjugate to neither a reflection nor `1`.  Shape 1 catches `1` and `σ₀`, shape
2 catches the reflections, and the concatenation lemma says the spelling of
`((σ₀σ_p)^k)^n` has `nk` syllables, which is right.
-/

namespace GroupApproximation
namespace DGOWindmill

universe u v

/-! ## Normalisation: moving the trailing letter to the front -/

section Normalize

variable {G : Type u} [Group G] {X : Type v}
  {Rot : X → Subgroup G} {C₁ : Set X} {GW : Subgroup G}

/-- **Conjugate a spelling by its own trailing letter**, so that the trailing
letter becomes trivial.  On the empty list there is nothing to move and the
spelling is returned unchanged. -/
def Spelling.normalize : Spelling G X → Spelling G X
  | ⟨[], e⟩ => ⟨[], e⟩
  | ⟨w :: l, e⟩ => ⟨{ w with pre := e * w.pre } :: l, 1⟩

@[simp]
theorem Spelling.normalize_nil (e : G) :
    (⟨[], e⟩ : Spelling G X).normalize = ⟨[], e⟩ := rfl

@[simp]
theorem Spelling.normalize_cons (w : Syll G X) (l : List (Syll G X)) (e : G) :
    (⟨w :: l, e⟩ : Spelling G X).normalize
      = ⟨{ w with pre := e * w.pre } :: l, 1⟩ := rfl

@[simp]
theorem Spelling.length_sylls_normalize (s : Spelling G X) :
    s.normalize.sylls.length = s.sylls.length := by
  obtain ⟨l, e⟩ := s
  cases l with
  | nil => simp
  | cons w l => simp

theorem Spelling.normalize_nil_or_tail_one (s : Spelling G X) :
    s.normalize.sylls = [] ∨ s.normalize.tail = 1 := by
  obtain ⟨l, e⟩ := s
  cases l with
  | nil => exact Or.inl rfl
  | cons w l => exact Or.inr rfl

/-- **Normalisation is a conjugation.** -/
theorem Spelling.eval_normalize (s : Spelling G X) :
    s.normalize.eval = s.tail * s.eval * s.tail⁻¹ := by
  obtain ⟨l, e⟩ := s
  cases l with
  | nil =>
      simp only [Spelling.normalize_nil, Spelling.eval_mk, listEval_nil]
      group
  | cons w l =>
      simp only [Spelling.normalize_cons, Spelling.eval_mk, listEval_cons]
      group

theorem Spelling.isValid_normalize {s : Spelling G X} (hs : s.IsValid Rot C₁ GW) :
    s.normalize.IsValid Rot C₁ GW := by
  obtain ⟨l, e⟩ := s
  cases l with
  | nil => exact hs
  | cons w l =>
      refine ⟨GW.one_mem, ?_⟩
      intro x hx
      simp only [Spelling.normalize_cons, List.mem_cons] at hx
      have hw : w.IsValid Rot C₁ GW := hs.sylls_valid w (by simp)
      rcases hx with rfl | hx'
      · exact ⟨GW.mul_mem hs.tail_mem hw.pre_mem, hw.dir_mem, hw.rot_mem,
          hw.rot_ne_one⟩
      · exact hs.sylls_valid x (by simp [hx'])

end Normalize

/-! ## Powers: the concatenation of a syllable list with itself -/

section Powers

variable {G : Type u} [Group G] {X : Type v}
  {Rot : X → Subgroup G} {C₁ : Set X} {GW : Subgroup G}

theorem length_flatten_replicate {α : Type*} (l : List α) (n : ℕ) :
    ((List.replicate n l).flatten).length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
      ring

theorem listEval_flatten_replicate (l : List (Syll G X)) (n : ℕ) :
    listEval ((List.replicate n l).flatten) = (listEval l) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, listEval_append, ih, pow_succ]
      exact (pow_mul_comm' _ _).symm

theorem Spelling.eval_flatten_replicate {s : Spelling G X} (htail : s.tail = 1)
    (n : ℕ) :
    (⟨(List.replicate n s.sylls).flatten, 1⟩ : Spelling G X).eval = s.eval ^ n := by
  rw [Spelling.eval_mk, mul_one, listEval_flatten_replicate, Spelling.eval_def,
    htail, mul_one]

theorem Spelling.isValid_flatten_replicate {s : Spelling G X}
    (hs : s.IsValid Rot C₁ GW) (n : ℕ) :
    (⟨(List.replicate n s.sylls).flatten, 1⟩ : Spelling G X).IsValid Rot C₁ GW := by
  refine ⟨GW.one_mem, ?_⟩
  intro x hx
  simp only [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hl] at hxl
  exact hs.sylls_valid x hxl

end Powers

/-! ## Cyclically reduced spellings -/

section Cyclic

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
  {Rot : X → Subgroup G} {C₁ : Set X} {GW : Subgroup G}

/-- Changing the `pre` of the leading syllable changes no seam: the leading
syllable never occupies the right-hand slot of `Seam`, and the left-hand slot
looks only at the direction. -/
theorem reducedList_cons_congr {w w' : Syll G X} {l : List (Syll G X)}
    (hdir : w'.dir = w.dir) (h : ReducedList (w :: l)) : ReducedList (w' :: l) := by
  have h' : List.IsChain Seam (w :: l) := h
  rw [List.isChain_cons] at h'
  show List.IsChain Seam (w' :: l)
  rw [List.isChain_cons]
  refine ⟨fun y hy => ?_, h'.2⟩
  have hy' : y.pre • y.dir ≠ w.dir := h'.1 y hy
  show y.pre • y.dir ≠ w'.dir
  rw [hdir]
  exact hy'

theorem Spelling.reduced_normalize {s : Spelling G X} (hred : s.Reduced) :
    s.normalize.Reduced := by
  obtain ⟨l, e⟩ := s
  cases l with
  | nil => exact hred
  | cons w l =>
      have hred' : ReducedList (w :: l) := hred
      show ReducedList ({ w with pre := e * w.pre } :: l)
      -- Both syllables must be pinned: `rfl` alone would unify the source
      -- syllable with the target one and ask `hred'` for the wrong list.
      exact reducedList_cons_congr (w := w) (w' := { w with pre := e * w.pre })
        rfl hred'

/-- **The wrap-around seam.**  The last syllable and the first must not merge
when the word is read cyclically.  Stated in the shape of Mathlib's
`FreeGroup.IsCyclicallyReduced`, so that the concatenation lemma below is a
direct citation of `List.isChain_flatten`. -/
def Spelling.CyclicSeam (s : Spelling G X) : Prop :=
  ∀ z ∈ s.sylls.getLast?, ∀ f ∈ s.sylls.head?, Seam z f

/-- A spelling is **cyclically reduced** when it is reduced and its wrap-around
seam holds. -/
def Spelling.CyclicallyReduced (s : Spelling G X) : Prop :=
  s.Reduced ∧ s.CyclicSeam

theorem Spelling.cyclicSeam_def (s : Spelling G X) :
    s.CyclicSeam ↔ ∀ z ∈ s.sylls.getLast?, ∀ f ∈ s.sylls.head?, Seam z f := Iff.rfl

/-- The wrap-around seam, checked at the actual first and last syllables. -/
theorem Spelling.cyclicSeam_of_head_getLast {s : Spelling G X} {f z : Syll G X}
    (hh : s.sylls.head? = some f) (hz : s.sylls.getLast? = some z) (h : Seam z f) :
    s.CyclicSeam := by
  intro zz hzz ff hff
  rw [hz] at hzz
  rw [hh] at hff
  have e1 : z = zz := Option.mem_some_iff.mp hzz
  have e2 : f = ff := Option.mem_some_iff.mp hff
  rw [← e1, ← e2]
  exact h

/-- A spelling with no syllables has a vacuous wrap-around seam. -/
theorem Spelling.cyclicSeam_of_sylls_nil {s : Spelling G X} (h : s.sylls = []) :
    s.CyclicSeam := by
  intro zz hzz
  rw [h, List.getLast?_nil] at hzz
  simp at hzz

/-! ### The `n`-th power of a cyclically reduced spelling -/

theorem reducedList_flatten_replicate {l : List (Syll G X)} (hne : l ≠ [])
    (hred : ReducedList l)
    (hcyc : ∀ z ∈ l.getLast?, ∀ f ∈ l.head?, Seam z f) (n : ℕ) :
    ReducedList ((List.replicate n l).flatten) := by
  have hnotmem : ([] : List (Syll G X)) ∉ List.replicate n l := by
    simp only [List.mem_replicate, not_and]
    intro _
    exact fun h => hne h.symm
  show List.IsChain Seam _
  rw [List.isChain_flatten hnotmem]
  refine ⟨?_, ?_⟩
  · intro l' hl'
    rw [List.eq_of_mem_replicate hl']
    exact hred
  · exact List.isChain_replicate_of_rel n hcyc

theorem Spelling.cyclicallyReduced_flatten_replicate {s : Spelling G X}
    (hne : s.sylls ≠ []) (hcr : s.CyclicallyReduced) (n : ℕ) :
    (⟨(List.replicate n s.sylls).flatten, 1⟩ : Spelling G X).CyclicallyReduced := by
  refine ⟨reducedList_flatten_replicate hne hcr.1 hcr.2 n, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Spelling.cyclicSeam_of_sylls_nil ?_
    simp
  · have hn0 : n ≠ 0 := by omega
    intro z hz f hf
    have hz' : z ∈ ((List.replicate n s.sylls).flatten).getLast? := hz
    have hf' : f ∈ ((List.replicate n s.sylls).flatten).head? := hf
    rw [List.getLast?_flatten_replicate hn0] at hz'
    rw [List.head?_flatten_replicate hn0] at hf'
    exact hcr.2 z hz' f hf'

/-- **The spelling of `gⁿ` for a cyclically reduced `g`** is the `n`-fold
concatenation of its syllable list, and is again cyclically reduced. -/
theorem Spelling.exists_cyclicallyReduced_pow {s : Spelling G X}
    (hs : s.IsValid Rot C₁ GW) (hne : s.sylls ≠ []) (htail : s.tail = 1)
    (hcr : s.CyclicallyReduced) (n : ℕ) :
    ∃ t : Spelling G X, t.IsValid Rot C₁ GW ∧ t.CyclicallyReduced ∧ t.tail = 1 ∧
      t.eval = s.eval ^ n ∧ t.sylls.length = n * s.sylls.length :=
  ⟨⟨(List.replicate n s.sylls).flatten, 1⟩,
    Spelling.isValid_flatten_replicate hs n,
    Spelling.cyclicallyReduced_flatten_replicate hne hcr n,
    rfl,
    Spelling.eval_flatten_replicate htail n,
    length_flatten_replicate s.sylls n⟩

/-! ### The three terminal shapes -/

/-- The trichotomy that cyclic reduction produces: an element of `G₂` is
conjugate into `G_W`, or into a rotation subgroup, or to the value of a
cyclically reduced spelling with at least one syllable. -/
def IsCyclicOutcome (Rot : X → Subgroup G) (C₁ : Set X) (GW : Subgroup G)
    (g : G) : Prop :=
  (∃ c : G, c ∈ stepGroup Rot C₁ GW ∧ c * g * c⁻¹ ∈ GW) ∨
  (∃ (c : G) (d : X), c ∈ stepGroup Rot C₁ GW ∧ d ∈ C₁ ∧
    c * g * c⁻¹ ∈ Rot d) ∨
  (∃ (c : G) (t : Spelling G X), c ∈ stepGroup Rot C₁ GW ∧
    t.IsValid Rot C₁ GW ∧ t.CyclicallyReduced ∧ t.tail = 1 ∧
      t.sylls ≠ [] ∧ t.eval = c * g * c⁻¹)

/-- The outcome is preserved by conjugation inside the stage group.  Recording
this membership is load-bearing in the growth step: it is what later moves a
rotation apex into the invariant next windmill. -/
theorem IsCyclicOutcome.conj (a : G) (ha : a ∈ stepGroup Rot C₁ GW)
    {g h : G} (hgh : g = a * h * a⁻¹)
    (H : IsCyclicOutcome Rot C₁ GW g) : IsCyclicOutcome Rot C₁ GW h := by
  have key : ∀ c : G, c * g * c⁻¹ = (c * a) * h * (c * a)⁻¹ := by
    intro c
    rw [hgh]
    group
  rcases H with ⟨c, hcStep, hc⟩ | ⟨c, d, hcStep, hd, hc⟩ |
      ⟨c, t, hcStep, ht, htcr, httail, htne, hte⟩
  · exact Or.inl ⟨c * a, (stepGroup Rot C₁ GW).mul_mem hcStep ha,
      by rw [← key c]; exact hc⟩
  · exact Or.inr (Or.inl ⟨c * a, d, (stepGroup Rot C₁ GW).mul_mem hcStep ha,
      hd, by rw [← key c]; exact hc⟩)
  · refine Or.inr (Or.inr ⟨c * a, t, (stepGroup Rot C₁ GW).mul_mem hcStep ha,
      ht, htcr, httail, htne, ?_⟩)
    rw [hte]
    exact key c

/-- **Cyclic reduction.**  Every element of `G₂` falls into one of the three
shapes, up to conjugacy.

The induction is on the length of a spelling: a failed cyclic seam is turned
into an ordinary failed seam by the cyclic permutation, and the merge of
`exists_isValid_shorter_of_seam` then drops the length. -/
theorem isCyclicOutcome_of_isValid
    (hconj : ∀ (a : G) (d : X), d ∈ C₁ → ∀ b ∈ Rot d, a * b * a⁻¹ ∈ Rot (a • d))
    (hfree : ∀ a ∈ GW, ∀ d ∈ C₁, a • d = d → a = 1)
    {s : Spelling G X} (hs : s.IsValid Rot C₁ GW) :
    IsCyclicOutcome Rot C₁ GW s.eval := by
  suffices H : ∀ n : ℕ, ∀ s : Spelling G X, s.IsValid Rot C₁ GW →
      s.sylls.length ≤ n → IsCyclicOutcome Rot C₁ GW s.eval by
    exact H s.sylls.length s hs le_rfl
  intro n
  induction n with
  | zero =>
      intro s hs hlen
      have hnil : s.sylls = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      refine Or.inl ⟨1, (stepGroup Rot C₁ GW).one_mem, ?_⟩
      have heq : s.eval = s.tail := by
        rw [Spelling.eval_def, hnil, listEval_nil, one_mul]
      rw [heq]
      simpa using hs.tail_mem
  | succ n ih =>
      intro s hs hlen
      obtain ⟨t, ht, hte, htred, htlen⟩ := exists_reduced_of_isValid hconj hs
      have ht' : (t.normalize).IsValid Rot C₁ GW := Spelling.isValid_normalize ht
      have ht'red : (t.normalize).Reduced := Spelling.reduced_normalize htred
      have ht'eval : (t.normalize).eval = t.tail * s.eval * t.tail⁻¹ := by
        rw [Spelling.eval_normalize, hte]
      have ht'len : (t.normalize).sylls.length = t.sylls.length :=
        Spelling.length_sylls_normalize t
      by_cases hcyc : (t.normalize).CyclicSeam
      · rcases eq_or_ne (t.normalize).sylls [] with hnil | hne
        · refine Or.inl ⟨t.tail, gw_le_stepGroup ht.tail_mem, ?_⟩
          have heq : (t.normalize).eval = (t.normalize).tail := by
            rw [Spelling.eval_def, hnil, listEval_nil, one_mul]
          rw [← ht'eval, heq]
          exact ht'.tail_mem
        · have ht'tail : (t.normalize).tail = 1 :=
            (Spelling.normalize_nil_or_tail_one t).resolve_left hne
          exact Or.inr (Or.inr ⟨t.tail, t.normalize, gw_le_stepGroup ht.tail_mem,
            ht', ⟨ht'red, hcyc⟩, ht'tail, hne, ht'eval⟩)
      · -- The cyclic seam fails.
        have hne : (t.normalize).sylls ≠ [] := fun hnil =>
          hcyc (Spelling.cyclicSeam_of_sylls_nil hnil)
        have ht'tail : (t.normalize).tail = 1 :=
          (Spelling.normalize_nil_or_tail_one t).resolve_left hne
        obtain ⟨f0, m, hfm⟩ : ∃ a l, (t.normalize).sylls = a :: l := by
          cases hc : (t.normalize).sylls with
          | nil => exact absurd hc hne
          | cons a l => exact ⟨a, l, rfl⟩
        have hhead : (t.normalize).sylls.head? = some f0 := by rw [hfm]; simp
        have hf0valid : f0.IsValid Rot C₁ GW :=
          ht'.sylls_valid f0 (by rw [hfm]; simp)
        rcases List.eq_nil_or_concat' m with hmnil | ⟨m', z', hmz⟩
        · -- One syllable: `hfree` forces the letter to be trivial.
          subst hmnil
          have hlast : (t.normalize).sylls.getLast? = some f0 := by rw [hfm]; simp
          have hfixed : f0.pre • f0.dir = f0.dir := by
            by_contra hcon
            exact hcyc (Spelling.cyclicSeam_of_head_getLast hhead hlast hcon)
          have hpre1 : f0.pre = 1 :=
            hfree f0.pre hf0valid.pre_mem f0.dir hf0valid.dir_mem hfixed
          refine Or.inr (Or.inl ⟨t.tail, f0.dir, gw_le_stepGroup ht.tail_mem,
            hf0valid.dir_mem, ?_⟩)
          have heq : (t.normalize).eval = f0.rot := by
            rw [Spelling.eval_def, hfm, ht'tail, listEval_cons, listEval_nil,
              hpre1]
            group
          rw [← ht'eval, heq]
          exact hf0valid.rot_mem
        · -- Two or more syllables: rotate, merge, and shorten.
          have hsylls : (t.normalize).sylls = (f0 :: m') ++ [z'] := by
            rw [hfm, hmz]
            simp
          have hlast : (t.normalize).sylls.getLast? = some z' := by
            rw [hsylls]
            exact List.getLast?_concat
          have hseamfail : f0.pre • f0.dir = z'.dir := by
            by_contra hcon
            exact hcyc (Spelling.cyclicSeam_of_head_getLast hhead hlast hcon)
          have hrvalid : (⟨z' :: f0 :: m', 1⟩ : Spelling G X).IsValid Rot C₁ GW := by
            refine ⟨GW.one_mem, ?_⟩
            intro x hx
            simp only [List.mem_cons] at hx
            refine ht'.sylls_valid x ?_
            rw [hsylls]
            rcases hx with rfl | rfl | hx'
            · simp
            · simp
            · simp [hx']
          have hdecomp : (⟨z' :: f0 :: m', 1⟩ : Spelling G X).sylls
              = [] ++ z' :: f0 :: m' := by simp
          have ht'val : (t.normalize).eval = listEval ((f0 :: m') ++ [z']) := by
            rw [Spelling.eval_def, hsylls, ht'tail, mul_one]
          have hr_eval : (⟨z' :: f0 :: m', 1⟩ : Spelling G X).eval
              = (z'.pre * z'.rot) * (t.normalize).eval * (z'.pre * z'.rot)⁻¹ := by
            rw [ht'val]
            simp only [Spelling.eval_mk, listEval_cons, listEval_append,
              listEval_nil, mul_one]
            group
          obtain ⟨q, hq, hqe, hql⟩ :=
            exists_isValid_shorter_of_seam hconj hrvalid hdecomp hseamfail
          have hlenA : (⟨z' :: f0 :: m', 1⟩ : Spelling G X).sylls.length
              = m'.length + 2 := by
            simp only [List.length_cons]
          have hlenB : (t.normalize).sylls.length = m'.length + 2 := by
            rw [hsylls]
            simp only [List.length_append, List.length_cons, List.length_nil]
          have hqlen : q.sylls.length ≤ n := by omega
          have hz'valid : z'.IsValid Rot C₁ GW :=
            hrvalid.sylls_valid z' (by simp)
          have haStep : z'.pre * z'.rot * t.tail ∈ stepGroup Rot C₁ GW :=
            (stepGroup Rot C₁ GW).mul_mem
              ((stepGroup Rot C₁ GW).mul_mem
                (gw_le_stepGroup hz'valid.pre_mem)
                (rot_le_stepGroup hz'valid.dir_mem hz'valid.rot_mem))
              (gw_le_stepGroup ht.tail_mem)
          refine IsCyclicOutcome.conj (z'.pre * z'.rot * t.tail) haStep ?_
            (ih q hq hqlen)
          rw [hqe, hr_eval, ht'eval]
          group

/-- **Cyclic reduction, from membership in `G₂`.** -/
theorem isCyclicOutcome_of_mem_stepGroup
    (hconj : ∀ (a : G) (d : X), d ∈ C₁ → ∀ b ∈ Rot d, a * b * a⁻¹ ∈ Rot (a • d))
    (hfree : ∀ a ∈ GW, ∀ d ∈ C₁, a • d = d → a = 1)
    {g : G} (hg : g ∈ stepGroup Rot C₁ GW) :
    IsCyclicOutcome Rot C₁ GW g := by
  obtain ⟨s, hs, hse⟩ := exists_isValid_of_mem_stepGroup hg
  rw [← hse]
  exact isCyclicOutcome_of_isValid hconj hfree hs

end Cyclic

end DGOWindmill
end GroupApproximation
