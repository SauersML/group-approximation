import GroupApproximation.Higman.HigmanAddition

/-!
# Primitive recursion, by running the transition device

`Higman/HigmanAddition.lean` runs the adjacent-block transition device once, on
the smallest computation there is: the counter climbs (or descends), the running
value moves with it, and the trace certifies `z = x + y`.  This module runs the
same device with an arbitrary step relation, and so reaches Higman's Lemma 2.4
in full:

> if the base relation `G` and the step relation `H` are generated, so is the
> relation "`z` is what `H` reaches from a `G`-start after `y` steps".

The recursion variable ranges over `ℕ`, so unlike addition there is only one
mode: the counter climbs.  Everything else --- the one-sided trace, the carried
copies, the invariant, the first non-running step --- is the addition argument
with the successor atom replaced by `H` and the anchoring equation `W₀ = V₀`
replaced by `G`.

## The format

Blocks of width `k`, any power of two with `k ≥ p + 5`, where `p` is the number
of parameters.  Block `i` occupies the coordinates `k·i` to `k·i + k - 1` and
carries

* `k·i`                     --- the **value** track `V`, which the projection reads;
* `k·i + 1`                 --- a carried copy `Y` of the recursion variable;
* `k·i + 2`                 --- a carried copy `Z` of the answer;
* `k·i + 3`                 --- the **counter** `C`;
* `k·i + 4 … k·i + p + 3`   --- carried copies of the `p` parameters;
* `k·i + p + 4`             --- the **running value** `W`.

The output is the arity-`p+2` relation on `(x̄, y, z)`, supported on
`[0, p + 2)`; the value track carries `x̄` at the blocks `0, …, p-1`, then `y`,
then `z`.  That is why the trace is built out to the block `y + p + 1` even
when the computation stops at the block `y`: the output tuple has to fit.

## Why the counter is the load-bearing track

The step relation sees one pair of blocks and cannot know where on the line it
sits.  The counter repairs that: pinned to `0` at the origin and advanced by
every running step, it reads the block index (`Seq.recRunning_invariant`), so
`H` is applied at `0, 1, 2, …` in order, and the stopping step --- which
compares the counter with the carried `Y` --- fires exactly at the block `y`.

## Why the statement is relational

Higman's lemma is about functions, but the trace certifies something weaker and
more useful: that *some* run of `H` joins a `G`-start to `z` in `y` steps.
`Seq.recRun` says exactly that, with the run given as a function `v : ℤ → ℤ`
read off the running-value track.  When `G` and `H` are graphs of functions the
run is unique and `recRun` is the graph of the primitive recursion; that
specialization needs no trace and is not done here.

## What is assumed

Three things, all of them the variable calculus of Higman's Section 2:

* `hEq` and `hSucc`, the arity-two relations of `Higman/HigmanAddition.lean`;
* `hPlace`, the **placement principle** --- an arity-`n` generated relation may
  be imposed at any `n` distinct coordinates, every other coordinate being left
  free (`Seq.placeAt`).

`hSucc` is `hPlace` applied to `Sset` and `hEq` is `hPlace` applied to the
diagonal; they are kept separate so that this module composes with
`Higman/HigmanAddition.lean` unchanged.  Everything else is proved here,
including the assembly of a sequence with prescribed blocks (`Seq.blockSeq`),
which the addition module had only at the fixed width eight.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  Blocks of a symbolic width -/

theorem block_ediv (m q d : ℤ) (hm : 0 < m) (hd0 : 0 ≤ d) (hdm : d < m) :
    (m * q + d) / m = q := by
  have e : m * q + d = d + m * q := by ring
  rw [e, Int.add_mul_ediv_left d q hm.ne', Int.ediv_eq_zero_of_lt hd0 hdm, zero_add]

theorem block_emod (m q d : ℤ) (hd0 : 0 ≤ d) (hdm : d < m) : (m * q + d) % m = d := by
  have e : m * q + d = d + m * q := by ring
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hd0 hdm]

/-- The function carrying `entry q d` at the coordinate `m * q + d`, for
`0 ≤ q ≤ N` and `0 ≤ d < m`, and vanishing everywhere else. -/
def blockFun (m N : ℤ) (entry : ℤ → ℤ → ℤ) (i : ℤ) : ℤ :=
  if 0 ≤ i ∧ i < m * (N + 1) then entry (i / m) (i % m) else 0

theorem blockFun_mem_Ico (m N : ℤ) (entry : ℤ → ℤ → ℤ) (i : ℤ)
    (h : blockFun m N entry i ≠ 0) : i ∈ Finset.Ico (0 : ℤ) (m * (N + 1)) := by
  rw [Finset.mem_Ico]
  by_contra hcon
  refine h ?_
  simp only [blockFun, if_neg hcon]

/-- **A sequence with prescribed blocks.** -/
noncomputable def blockSeq (m N : ℤ) (entry : ℤ → ℤ → ℤ) : E :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) (m * (N + 1))) (blockFun m N entry)
    fun i hi => blockFun_mem_Ico m N entry i hi

theorem blockSeq_apply (m N : ℤ) (entry : ℤ → ℤ → ℤ) (i : ℤ) :
    blockSeq m N entry i = blockFun m N entry i := by
  simp only [blockSeq, Finsupp.onFinset_apply]

theorem blockSeq_in (m N : ℤ) (entry : ℤ → ℤ → ℤ) (q d : ℤ) (hm : 0 < m)
    (hq0 : 0 ≤ q) (hqN : q ≤ N) (hd0 : 0 ≤ d) (hdm : d < m) :
    blockSeq m N entry (m * q + d) = entry q d := by
  have hmq : 0 ≤ m * q := mul_nonneg hm.le hq0
  have hle : m * q ≤ m * N := mul_le_mul_of_nonneg_left hqN hm.le
  have hexp : m * (N + 1) = m * N + m := by ring
  have hpos : 0 ≤ m * q + d ∧ m * q + d < m * (N + 1) := ⟨by linarith, by linarith⟩
  rw [blockSeq_apply]
  simp only [blockFun, if_pos hpos]
  rw [block_ediv m q d hm hd0 hdm, block_emod m q d hd0 hdm]

theorem blockSeq_neg (m N : ℤ) (entry : ℤ → ℤ → ℤ) (i : ℤ) (hi : i < 0) :
    blockSeq m N entry i = 0 := by
  have hcon : ¬ (0 ≤ i ∧ i < m * (N + 1)) := by
    rintro ⟨h1, -⟩
    omega
  rw [blockSeq_apply]
  simp only [blockFun, if_neg hcon]

theorem blockSeq_out (m N : ℤ) (entry : ℤ → ℤ → ℤ) (q d : ℤ) (hm : 0 < m)
    (hq : N < q) (hd0 : 0 ≤ d) (hdm : d < m) :
    blockSeq m N entry (m * q + d) = 0 := by
  have hge : m * (N + 1) ≤ m * q := mul_le_mul_of_nonneg_left (by omega) hm.le
  have hcon : ¬ (0 ≤ m * q + d ∧ m * q + d < m * (N + 1)) := by
    rintro ⟨-, h2⟩
    linarith
  rw [blockSeq_apply]
  simp only [blockFun, if_neg hcon]

/-! ## 2.  Placing a relation at prescribed coordinates -/

/-- An arity-`n` relation, read off the window `[0, n)`, imposed at the
coordinates `c 0, …, c (n-1)`, with every other coordinate free. -/
def placeAt (n : ℕ) (c : ℕ → ℤ) (R : Set E) : Set E :=
  {f | ∃ w ∈ R, ∀ j : ℕ, j < n → f (c j) = w (j : ℤ)}

/-- Where the base relation is placed: the `p` parameter tracks of block `0`,
and then its running value. -/
def baseCoord (p : ℕ) (j : ℕ) : ℤ := if j < p then (4 : ℤ) + (j : ℤ) else (p : ℤ) + 4

/-- Where the step relation is placed inside a pair of adjacent blocks: the
parameter tracks, the counter and the running value of the left block, and the
running value of the right one. -/
def stepCoord (p k : ℕ) (j : ℕ) : ℤ :=
  if j < p then (4 : ℤ) + (j : ℤ)
  else if j = p then 3
  else if j = p + 1 then (p : ℤ) + 4
  else (k : ℤ) + ((p : ℤ) + 4)

theorem baseCoord_param (p j : ℕ) (hj : j < p) : baseCoord p j = 4 + (j : ℤ) := by
  simp only [baseCoord, if_pos hj]

theorem baseCoord_last (p : ℕ) : baseCoord p p = (p : ℤ) + 4 := by
  have h1 : ¬ (p < p) := by omega
  simp only [baseCoord, if_neg h1]

theorem stepCoord_param (p k j : ℕ) (hj : j < p) : stepCoord p k j = 4 + (j : ℤ) := by
  simp only [stepCoord, if_pos hj]

theorem stepCoord_count (p k : ℕ) : stepCoord p k p = 3 := by
  have h1 : ¬ (p < p) := by omega
  simp only [stepCoord, if_neg h1, if_pos rfl]

theorem stepCoord_left (p k : ℕ) : stepCoord p k (p + 1) = (p : ℤ) + 4 := by
  have h1 : ¬ (p + 1 < p) := by omega
  have h2 : ¬ (p + 1 = p) := by omega
  simp only [stepCoord, if_neg h1, if_neg h2, if_pos rfl]

theorem stepCoord_right (p k : ℕ) : stepCoord p k (p + 2) = (k : ℤ) + ((p : ℤ) + 4) := by
  have h1 : ¬ (p + 2 < p) := by omega
  have h2 : ¬ (p + 2 = p) := by omega
  have h3 : ¬ (p + 2 = p + 1) := by omega
  simp only [stepCoord, if_neg h1, if_neg h2, if_neg h3]

theorem baseCoord_injOn (p : ℕ) : ∀ i j : ℕ, i < p + 1 → j < p + 1 →
    baseCoord p i = baseCoord p j → i = j := by
  intro i j hi hj hij
  by_cases h1 : i < p
  · by_cases h2 : j < p
    · rw [baseCoord_param p i h1, baseCoord_param p j h2] at hij
      omega
    · have hjp : j = p := by omega
      rw [baseCoord_param p i h1, hjp, baseCoord_last p] at hij
      omega
  · by_cases h2 : j < p
    · have hip : i = p := by omega
      rw [baseCoord_param p j h2, hip, baseCoord_last p] at hij
      omega
    · omega

theorem stepCoord_eval (p k : ℕ) : ∀ i : ℕ, i < p + 3 →
    (i < p ∧ stepCoord p k i = 4 + (i : ℤ)) ∨ (i = p ∧ stepCoord p k i = 3) ∨
      (i = p + 1 ∧ stepCoord p k i = (p : ℤ) + 4) ∨
      (i = p + 2 ∧ stepCoord p k i = (k : ℤ) + ((p : ℤ) + 4)) := by
  intro i hi
  by_cases h1 : i < p
  · exact Or.inl ⟨h1, stepCoord_param p k i h1⟩
  · by_cases h2 : i = p
    · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact stepCoord_count p k⟩)
    · by_cases h3 : i = p + 1
      · exact Or.inr (Or.inr (Or.inl ⟨h3, by rw [h3]; exact stepCoord_left p k⟩))
      · have h4 : i = p + 2 := by omega
        exact Or.inr (Or.inr (Or.inr ⟨h4, by rw [h4]; exact stepCoord_right p k⟩))

theorem stepCoord_injOn (p k : ℕ) (hk : p + 5 ≤ k) : ∀ i j : ℕ, i < p + 3 → j < p + 3 →
    stepCoord p k i = stepCoord p k j → i = j := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  intro i j hi hj hij
  rcases stepCoord_eval p k i hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases stepCoord_eval p k j hj with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      rw [a2, b2] at hij <;> omega

/-! ## 3.  The step relation, the anchor, and the trace -/

/-- The tracks a running step copies: everything but the value track, the
counter, and the running value. -/
def recCarried (p : ℕ) : Finset ℤ := (Finset.Icc (1 : ℤ) ((p : ℤ) + 3)).erase 3

/-- The tracks a blank block must clear. -/
def recActive (p : ℕ) : Finset ℤ := Finset.Icc (1 : ℤ) ((p : ℤ) + 4)

theorem mem_recCarried_iff (p : ℕ) (d : ℤ) :
    d ∈ recCarried p ↔ d ≠ 3 ∧ 1 ≤ d ∧ d ≤ (p : ℤ) + 3 := by
  show d ∈ (Finset.Icc (1 : ℤ) ((p : ℤ) + 3)).erase 3 ↔ _
  rw [Finset.mem_erase, Finset.mem_Icc]

theorem mem_recActive_iff (p : ℕ) (d : ℤ) :
    d ∈ recActive p ↔ 1 ≤ d ∧ d ≤ (p : ℤ) + 4 := by
  show d ∈ Finset.Icc (1 : ℤ) ((p : ℤ) + 4) ↔ _
  rw [Finset.mem_Icc]

theorem mem_recCarried_one (p : ℕ) : (1 : ℤ) ∈ recCarried p :=
  (mem_recCarried_iff p 1).mpr ⟨by omega, by omega, by omega⟩

theorem mem_recCarried_two (p : ℕ) : (2 : ℤ) ∈ recCarried p :=
  (mem_recCarried_iff p 2).mpr ⟨by omega, by omega, by omega⟩

theorem mem_recCarried_param (p j : ℕ) (hj : j < p) : (4 + (j : ℤ)) ∈ recCarried p := by
  have hjz : (j : ℤ) < (p : ℤ) := by exact_mod_cast hj
  exact (mem_recCarried_iff p _).mpr ⟨by omega, by omega, by omega⟩

/-- The carried data are copied from the left block to the right one. -/
def recCopy (p k : ℕ) : Set E := ⋂ d ∈ recCarried p, eqCoord ((k : ℤ) + d) d

/-- The right block is blank. -/
def recBlankRight (p k : ℕ) : Set E := ⋂ d ∈ recActive p, pinAt ((k : ℤ) + d) 0

/-- The left block is blank. -/
def recBlankLeft (p : ℕ) : Set E := ⋂ d ∈ recActive p, pinAt d 0

/-- The running step: the carried data are copied, the counter advances, and the
running value moves along `H`. -/
def recStepRel (p k : ℕ) (H : Set E) : Set E :=
  recCopy p k ∩ succCoord 3 ((k : ℤ) + 3) ∩ placeAt (p + 3) (stepCoord p k) H

/-- The stopping step: the counter has met the carried recursion variable, the
running value has met the carried answer, and the next block is blank. -/
def recStopRel (p k : ℕ) : Set E :=
  eqCoord 3 1 ∩ eqCoord ((p : ℤ) + 4) 2 ∩ recBlankRight p k

/-- **The relation between adjacent blocks.** -/
def recStep (p k : ℕ) (H : Set E) : Set E :=
  recStepRel p k H ∪ recStopRel p k ∪ recBlankLeft p

/-- The value track carries the parameters, then the recursion variable, then
the answer. -/
def recValue (p k : ℕ) : Set E :=
  (⋂ j ∈ Finset.range p, eqCoord ((k : ℤ) * (j : ℤ)) (4 + (j : ℤ))) ∩
    eqCoord ((k : ℤ) * (p : ℤ)) 1 ∩ eqCoord ((k : ℤ) * ((p : ℤ) + 1)) 2

/-- **The global conditions.** -/
def recAnchor (p k : ℕ) (G : Set E) : Set E :=
  vanishBelow 0 ∩ pinAt 3 0 ∩ placeAt (p + 1) (baseCoord p) G ∩ recValue p k

/-- The traces. -/
def recTrace (p k : ℕ) (G H : Set E) : Set E :=
  transitionSet k (recStep p k H) ∩ recAnchor p k G

/-- The value track of a trace. -/
def recProj (p k : ℕ) (G H : Set E) : Set E :=
  {f : E | ∃ g ∈ recTrace p k G H, ∀ i : ℤ, f i = g ((k : ℤ) * i)}

/-! ## 4.  The relation a trace computes -/

/-- The base relation holds of the parameters `x` and the value `u`. -/
def recBaseAt (p : ℕ) (G : Set E) (x : ℕ → ℤ) (u : ℤ) : Prop :=
  ∃ w ∈ G, (∀ j : ℕ, j < p → w (j : ℤ) = x j) ∧ w (p : ℤ) = u

/-- The step relation holds of the parameters `x`, the index `n`, and the pair
`(u, v)`. -/
def recStepAt (p : ℕ) (H : Set E) (x : ℕ → ℤ) (n u v : ℤ) : Prop :=
  ∃ w ∈ H, (∀ j : ℕ, j < p → w (j : ℤ) = x j) ∧ w (p : ℤ) = n ∧
    w ((p : ℤ) + 1) = u ∧ w ((p : ℤ) + 2) = v

/-- **The primitive recursion, relationally.**  Some run of `H` joins a
`G`-start to `z` in `y` steps. -/
def recRun (p : ℕ) (G H : Set E) (x : ℕ → ℤ) (y z : ℤ) : Prop :=
  0 ≤ y ∧ ∃ v : ℤ → ℤ, recBaseAt p G x (v 0) ∧
    (∀ i : ℤ, 0 ≤ i → i < y → recStepAt p H x i (v i) (v (i + 1))) ∧ v y = z

/-- **The graph of the primitive recursion, as an arity-`p+2` relation.** -/
def recGraph (p : ℕ) (G H : Set E) : Set E :=
  {f : E | (∀ i : ℤ, i < 0 → f i = 0) ∧ (∀ i : ℤ, (p : ℤ) + 2 ≤ i → f i = 0) ∧
    recRun p G H (fun j : ℕ => f (j : ℤ)) (f (p : ℤ)) (f ((p : ℤ) + 1))}

/-! ## 5.  The step relation and the anchor are generated -/

theorem higmanGenerated_recCopy (p k : ℕ)
    (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂)) : HigmanGenerated (recCopy p k) :=
  higmanGenerated_biInter (recCarried p) (fun d => eqCoord ((k : ℤ) + d) d)
    fun d _ => hEq ((k : ℤ) + d) d

theorem higmanGenerated_recBlankRight (p k : ℕ) : HigmanGenerated (recBlankRight p k) :=
  higmanGenerated_biInter (recActive p) (fun d => pinAt ((k : ℤ) + d) 0)
    fun d _ => higmanGenerated_pinAt ((k : ℤ) + d) 0

theorem higmanGenerated_recBlankLeft (p : ℕ) : HigmanGenerated (recBlankLeft p) :=
  higmanGenerated_biInter (recActive p) (fun d => pinAt d 0)
    fun d _ => higmanGenerated_pinAt d 0

theorem higmanGenerated_recValue (p k : ℕ)
    (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂)) : HigmanGenerated (recValue p k) :=
  HigmanGenerated.inter
    (HigmanGenerated.inter
      (higmanGenerated_biInter (Finset.range p)
        (fun j => eqCoord ((k : ℤ) * (j : ℤ)) (4 + (j : ℤ)))
        fun j _ => hEq ((k : ℤ) * (j : ℤ)) (4 + (j : ℤ)))
      (hEq ((k : ℤ) * (p : ℤ)) 1))
    (hEq ((k : ℤ) * ((p : ℤ) + 1)) 2)

theorem higmanGenerated_recStep (p k : ℕ) (hk : p + 5 ≤ k) (H : Set E)
    (hH : HigmanGenerated H) (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂))
    (hPlace : ∀ (n : ℕ) (c : ℕ → ℤ), (∀ i j : ℕ, i < n → j < n → c i = c j → i = j) →
      ∀ R : Set E, HigmanGenerated R → HigmanGenerated (placeAt n c R)) :
    HigmanGenerated (recStep p k H) :=
  HigmanGenerated.union
    (HigmanGenerated.union
      (HigmanGenerated.inter
        (HigmanGenerated.inter (higmanGenerated_recCopy p k hEq) (hSucc 3 ((k : ℤ) + 3)))
        (hPlace (p + 3) (stepCoord p k) (stepCoord_injOn p k hk) H hH))
      (HigmanGenerated.inter
        (HigmanGenerated.inter (hEq 3 1) (hEq ((p : ℤ) + 4) 2))
        (higmanGenerated_recBlankRight p k)))
    (higmanGenerated_recBlankLeft p)

theorem higmanGenerated_recAnchor (p k : ℕ) (G : Set E) (hG : HigmanGenerated G)
    (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hPlace : ∀ (n : ℕ) (c : ℕ → ℤ), (∀ i j : ℕ, i < n → j < n → c i = c j → i = j) →
      ∀ R : Set E, HigmanGenerated R → HigmanGenerated (placeAt n c R)) :
    HigmanGenerated (recAnchor p k G) :=
  HigmanGenerated.inter
    (HigmanGenerated.inter
      (HigmanGenerated.inter (higmanGenerated_vanishBelow 0) (higmanGenerated_pinAt 3 0))
      (hPlace (p + 1) (baseCoord p) (baseCoord_injOn p) G hG))
    (higmanGenerated_recValue p k hEq)

/-- **The value track of a trace is generated.**  This is the transition device
and the `θᵗ` projection, with no correctness content at all. -/
theorem higmanGenerated_recProj (p k t : ℕ) (hk : p + 5 ≤ k) (hkt : (2 : ℤ) ^ t = (k : ℤ))
    (G H : Set E) (hG : HigmanGenerated G) (hH : HigmanGenerated H)
    (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂))
    (hPlace : ∀ (n : ℕ) (c : ℕ → ℤ), (∀ i j : ℕ, i < n → j < n → c i = c j → i = j) →
      ∀ R : Set E, HigmanGenerated R → HigmanGenerated (placeAt n c R)) :
    HigmanGenerated (recProj p k G H) := by
  refine higmanGenerated_of_transitionProjection (t := t) (k := k) (by omega)
    (higmanGenerated_recStep p k hk H hH hEq hSucc hPlace)
    (higmanGenerated_recAnchor p k G hG hEq hPlace) ?_
  intro f
  rw [hkt]
  exact Iff.rfl

/-! ## 6.  Reading a pair of adjacent blocks -/

theorem windowAt_block_eval (k : ℕ) (g : E) (r j : ℤ) (h0 : 0 ≤ j) (hj : j < 2 * (k : ℤ)) :
    windowAt (2 * k) ((k : ℤ) * r) g j = g ((k : ℤ) * r + j) := by
  have hmem : j ∈ Finset.Ico (0 : ℤ) ((2 * k : ℕ) : ℤ) := by
    rw [Finset.mem_Ico]
    refine ⟨h0, ?_⟩
    push_cast
    omega
  rw [windowAt_apply, if_pos hmem]

theorem window_left (k : ℕ) (g : E) (r d : ℤ) (h0 : 0 ≤ d) (hd : d < (k : ℤ)) :
    windowAt (2 * k) ((k : ℤ) * r) g d = g ((k : ℤ) * r + d) :=
  windowAt_block_eval k g r d h0 (by omega)

theorem window_right (k : ℕ) (g : E) (r d : ℤ) (h0 : 0 ≤ d) (hd : d < (k : ℤ)) :
    windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d) = g ((k : ℤ) * (r + 1) + d) := by
  have e : (k : ℤ) * (r + 1) + d = (k : ℤ) * r + ((k : ℤ) + d) := by ring
  rw [windowAt_block_eval k g r ((k : ℤ) + d) (by omega) (by omega), e]

/-- A running step, read on the tracks. -/
def recRunning (p k : ℕ) (H : Set E) (g : E) (r : ℤ) : Prop :=
  (∀ d : ℤ, d ∈ recCarried p → g ((k : ℤ) * (r + 1) + d) = g ((k : ℤ) * r + d)) ∧
    g ((k : ℤ) * (r + 1) + 3) = g ((k : ℤ) * r + 3) + 1 ∧
    ∃ w ∈ H, (∀ j : ℕ, j < p → g ((k : ℤ) * r + (4 + (j : ℤ))) = w (j : ℤ)) ∧
      g ((k : ℤ) * r + 3) = w (p : ℤ) ∧
      g ((k : ℤ) * r + ((p : ℤ) + 4)) = w ((p : ℤ) + 1) ∧
      g ((k : ℤ) * (r + 1) + ((p : ℤ) + 4)) = w ((p : ℤ) + 2)

/-- A stopping step, read on the tracks. -/
def recStopped (p k : ℕ) (g : E) (r : ℤ) : Prop :=
  g ((k : ℤ) * r + 3) = g ((k : ℤ) * r + 1) ∧
    g ((k : ℤ) * r + ((p : ℤ) + 4)) = g ((k : ℤ) * r + 2) ∧
    ∀ d : ℤ, d ∈ recActive p → g ((k : ℤ) * (r + 1) + d) = 0

/-- An idle step, read on the tracks. -/
def recIdled (p k : ℕ) (g : E) (r : ℤ) : Prop :=
  ∀ d : ℤ, d ∈ recActive p → g ((k : ℤ) * r + d) = 0

/-- **The step relation, read on the tracks.** -/
theorem mem_recStep_window (p k : ℕ) (hk : p + 5 ≤ k) (H : Set E) (g : E) (r : ℤ) :
    windowAt (2 * k) ((k : ℤ) * r) g ∈ recStep p k H ↔
      recRunning p k H g r ∨ recStopped p k g r ∨ recIdled p k g r := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hL : ∀ d : ℤ, 0 ≤ d → d < (k : ℤ) →
      windowAt (2 * k) ((k : ℤ) * r) g d = g ((k : ℤ) * r + d) := fun d h1 h2 =>
    window_left k g r d h1 h2
  have hR : ∀ d : ℤ, 0 ≤ d → d < (k : ℤ) →
      windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d) = g ((k : ℤ) * (r + 1) + d) :=
    fun d h1 h2 => window_right k g r d h1 h2
  constructor
  · rintro (⟨⟨hcopy, hcnt⟩, hplace⟩ | ⟨⟨he1, he2⟩, hblank⟩) | hblank
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · intro d hd
        obtain ⟨-, b1, b2⟩ := (mem_recCarried_iff p d).mp hd
        have hval : windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d)
            = windowAt (2 * k) ((k : ℤ) * r) g d := Set.mem_iInter₂.mp hcopy d hd
        rw [hL d (by omega) (by omega), hR d (by omega) (by omega)] at hval
        exact hval
      · have hval : windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + 3)
            = windowAt (2 * k) ((k : ℤ) * r) g 3 + 1 := hcnt
        rw [hL 3 (by omega) (by omega), hR 3 (by omega) (by omega)] at hval
        exact hval
      · obtain ⟨v, hv, hvc⟩ := hplace
        refine ⟨v, hv, ?_, ?_, ?_, ?_⟩
        · intro j hj
          have hjz : (j : ℤ) < (p : ℤ) := by exact_mod_cast hj
          have hc := hvc j (by omega)
          rw [stepCoord_param p k j hj, hL (4 + (j : ℤ)) (by omega) (by omega)] at hc
          exact hc
        · have hc := hvc p (by omega)
          rw [stepCoord_count p k, hL 3 (by omega) (by omega)] at hc
          exact hc
        · have hc := hvc (p + 1) (by omega)
          rw [stepCoord_left p k, hL ((p : ℤ) + 4) (by omega) (by omega),
            show ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 from by omega] at hc
          exact hc
        · have hc := hvc (p + 2) (by omega)
          rw [stepCoord_right p k, hR ((p : ℤ) + 4) (by omega) (by omega),
            show ((p + 2 : ℕ) : ℤ) = (p : ℤ) + 2 from by omega] at hc
          exact hc
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · have hval : windowAt (2 * k) ((k : ℤ) * r) g 3
            = windowAt (2 * k) ((k : ℤ) * r) g 1 := he1
        rw [hL 3 (by omega) (by omega), hL 1 (by omega) (by omega)] at hval
        exact hval
      · have hval : windowAt (2 * k) ((k : ℤ) * r) g ((p : ℤ) + 4)
            = windowAt (2 * k) ((k : ℤ) * r) g 2 := he2
        rw [hL ((p : ℤ) + 4) (by omega) (by omega), hL 2 (by omega) (by omega)] at hval
        exact hval
      · intro d hd
        obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
        have hval : windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d) = 0 :=
          Set.mem_iInter₂.mp hblank d hd
        rw [hR d (by omega) (by omega)] at hval
        exact hval
    · refine Or.inr (Or.inr ?_)
      intro d hd
      obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
      have hval : windowAt (2 * k) ((k : ℤ) * r) g d = 0 := Set.mem_iInter₂.mp hblank d hd
      rw [hL d (by omega) (by omega)] at hval
      exact hval
  · rintro (⟨hcopy, hcnt, v, hv, hx, hn, hu, hu'⟩ | ⟨he1, he2, hblank⟩ | hblank)
    · refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · refine Set.mem_iInter₂.mpr fun d hd => ?_
        obtain ⟨-, b1, b2⟩ := (mem_recCarried_iff p d).mp hd
        show windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d)
          = windowAt (2 * k) ((k : ℤ) * r) g d
        rw [hL d (by omega) (by omega), hR d (by omega) (by omega)]
        exact hcopy d hd
      · show windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + 3)
          = windowAt (2 * k) ((k : ℤ) * r) g 3 + 1
        rw [hL 3 (by omega) (by omega), hR 3 (by omega) (by omega)]
        exact hcnt
      · refine ⟨v, hv, fun j hj => ?_⟩
        rcases lt_trichotomy j p with h1 | h1 | h1
        · have hjz : (j : ℤ) < (p : ℤ) := by exact_mod_cast h1
          rw [stepCoord_param p k j h1, hL (4 + (j : ℤ)) (by omega) (by omega)]
          exact hx j h1
        · rw [h1, stepCoord_count p k, hL 3 (by omega) (by omega)]
          exact hn
        · rcases eq_or_ne j (p + 1) with hj1 | hj1
          · rw [hj1, stepCoord_left p k, hL ((p : ℤ) + 4) (by omega) (by omega),
              show ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 from by omega]
            exact hu
          · have hj2 : j = p + 2 := by omega
            rw [hj2, stepCoord_right p k, hR ((p : ℤ) + 4) (by omega) (by omega),
              show ((p + 2 : ℕ) : ℤ) = (p : ℤ) + 2 from by omega]
            exact hu'
    · refine Or.inl (Or.inr ⟨⟨?_, ?_⟩, ?_⟩)
      · show windowAt (2 * k) ((k : ℤ) * r) g 3 = windowAt (2 * k) ((k : ℤ) * r) g 1
        rw [hL 3 (by omega) (by omega), hL 1 (by omega) (by omega)]
        exact he1
      · show windowAt (2 * k) ((k : ℤ) * r) g ((p : ℤ) + 4)
          = windowAt (2 * k) ((k : ℤ) * r) g 2
        rw [hL ((p : ℤ) + 4) (by omega) (by omega), hL 2 (by omega) (by omega)]
        exact he2
      · refine Set.mem_iInter₂.mpr fun d hd => ?_
        obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
        show windowAt (2 * k) ((k : ℤ) * r) g ((k : ℤ) + d) = 0
        rw [hR d (by omega) (by omega)]
        exact hblank d hd
    · refine Or.inr (Set.mem_iInter₂.mpr fun d hd => ?_)
      obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
      show windowAt (2 * k) ((k : ℤ) * r) g d = 0
      rw [hL d (by omega) (by omega)]
      exact hblank d hd

theorem recStep_cases (p k : ℕ) (hk : p + 5 ≤ k) {H : Set E} {g : E}
    (hg : g ∈ transitionSet k (recStep p k H)) (r : ℤ) :
    recRunning p k H g r ∨ recStopped p k g r ∨ recIdled p k g r :=
  (mem_recStep_window p k hk H g r).mp (hg r)

/-! ## 7.  Soundness: a trace computes a run -/

/-- **A run cannot go on for ever.**  A running step advances the counter, so a
counter that runs for ever is nonzero at infinitely many blocks, and a sequence
has finite support. -/
theorem exists_recStop (p k : ℕ) (hk : p + 5 ≤ k) (H : Set E) (g : E) :
    ∃ n : ℕ, (∀ j : ℕ, j < n → recRunning p k H g (j : ℤ)) ∧
      ¬ recRunning p k H g (n : ℤ) := by
  classical
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hex : ∃ n : ℕ, ¬ recRunning p k H g (n : ℤ) := by
    obtain ⟨_a, b, _ha, hb⟩ := exists_support_bounds g
    refine ⟨b.toNat + 1, ?_⟩
    rintro ⟨-, hcnt, -⟩
    have hgt : b < ((b.toNat + 1 : ℕ) : ℤ) := by omega
    have hT0 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) := by omega
    have hT1 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) + 1 := by omega
    have hprod : ((b.toNat + 1 : ℕ) : ℤ) ≤ (k : ℤ) * ((b.toNat + 1 : ℕ) : ℤ) := by
      have h := mul_le_mul_of_nonneg_right hk1 hT0
      rwa [one_mul] at h
    have hprod2 : ((b.toNat + 1 : ℕ) : ℤ) + 1
        ≤ (k : ℤ) * (((b.toNat + 1 : ℕ) : ℤ) + 1) := by
      have h := mul_le_mul_of_nonneg_right hk1 hT1
      rwa [one_mul] at h
    have hc0 : g ((k : ℤ) * ((b.toNat + 1 : ℕ) : ℤ) + 3) = 0 := hb _ (by linarith)
    have hc1 : g ((k : ℤ) * (((b.toNat + 1 : ℕ) : ℤ) + 1) + 3) = 0 := hb _ (by linarith)
    omega
  exact ⟨Nat.find hex, fun j hj => not_not.mp (Nat.find_min hex hj), Nat.find_spec hex⟩

/-- **What a run preserves.**  The carried data are unchanged, and the counter
reads the block index. -/
theorem recRunning_invariant (p k : ℕ) {H : Set E} {g : E} {n : ℕ}
    (hrun : ∀ j : ℕ, j < n → recRunning p k H g (j : ℤ)) (hc0 : g 3 = 0) :
    ∀ j : ℕ, j ≤ n →
      (∀ d : ℤ, d ∈ recCarried p →
          g ((k : ℤ) * (j : ℤ) + d) = g ((k : ℤ) * ((0 : ℕ) : ℤ) + d)) ∧
        g ((k : ℤ) * (j : ℤ) + 3) = (j : ℤ) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨fun d _ => rfl, ?_⟩
      simpa using hc0
  | succ i ih =>
      intro hi
      obtain ⟨q1, q2⟩ := ih (by omega)
      obtain ⟨s1, s2, -⟩ := hrun i (by omega)
      have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by omega
      rw [hcast]
      refine ⟨fun d hd => ?_, ?_⟩
      · rw [s1 d hd]
        exact q1 d hd
      · rw [s2, q2]

/-- **The run a trace certifies.** -/
theorem recTrace_run (p k : ℕ) (hk : p + 5 ≤ k) (G H : Set E) {g : E}
    (hg : g ∈ recTrace p k G H) :
    recRun p G H (fun j : ℕ => g ((k : ℤ) * (j : ℤ))) (g ((k : ℤ) * (p : ℤ)))
      (g ((k : ℤ) * ((p : ℤ) + 1))) := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hzc : ((0 : ℕ) : ℤ) = 0 := by omega
  obtain ⟨hT, hA⟩ := hg
  have hc0 : g 3 = 0 := hA.1.1.2
  have hbase : g ∈ placeAt (p + 1) (baseCoord p) G := hA.1.2
  have hvalx : ∀ j : ℕ, j < p → g ((k : ℤ) * (j : ℤ)) = g (4 + (j : ℤ)) := fun j hj =>
    Set.mem_iInter₂.mp hA.2.1.1 j (Finset.mem_range.mpr hj)
  have hvaly : g ((k : ℤ) * (p : ℤ)) = g 1 := hA.2.1.2
  have hvalz : g ((k : ℤ) * ((p : ℤ) + 1)) = g 2 := hA.2.2
  obtain ⟨n, hrun, hstop⟩ := exists_recStop p k hk H g
  obtain ⟨inv1, inv2⟩ := recRunning_invariant p k hrun hc0 n le_rfl
  have hcar : ∀ d : ℤ, d ∈ recCarried p → g ((k : ℤ) * (n : ℤ) + d) = g d := by
    intro d hd
    have h := inv1 d hd
    rw [hzc, mul_zero, zero_add] at h
    exact h
  have hbaseAt : recBaseAt p G (fun j : ℕ => g ((k : ℤ) * (j : ℤ)))
      (g ((k : ℤ) * 0 + ((p : ℤ) + 4))) := by
    obtain ⟨w, hw, hwc⟩ := hbase
    refine ⟨w, hw, fun j hj => ?_, ?_⟩
    · show w (j : ℤ) = g ((k : ℤ) * (j : ℤ))
      have h1 := hwc j (by omega)
      rw [baseCoord_param p j hj] at h1
      rw [← h1]
      exact (hvalx j hj).symm
    · have h2 := hwc p (by omega)
      rw [baseCoord_last p] at h2
      rw [mul_zero, zero_add]
      exact h2.symm
  have hstepAt : ∀ j : ℕ, j < n →
      recStepAt p H (fun jj : ℕ => g ((k : ℤ) * (jj : ℤ))) (j : ℤ)
        (g ((k : ℤ) * (j : ℤ) + ((p : ℤ) + 4)))
        (g ((k : ℤ) * ((j : ℤ) + 1) + ((p : ℤ) + 4))) := by
    intro j hj
    obtain ⟨-, -, w, hw, hx, hn, hu, hu'⟩ := hrun j hj
    obtain ⟨inv1j, inv2j⟩ := recRunning_invariant p k hrun hc0 j (by omega)
    refine ⟨w, hw, fun jj hjj => ?_, ?_, hu.symm, hu'.symm⟩
    · show w (jj : ℤ) = g ((k : ℤ) * (jj : ℤ))
      rw [← hx jj hjj, inv1j (4 + (jj : ℤ)) (mem_recCarried_param p jj hjj), hzc,
        mul_zero, zero_add, hvalx jj hjj]
    · rw [← hn, inv2j]
  rcases recStep_cases p k hk hT (n : ℤ) with hr | hs | hidle
  · exact absurd hr hstop
  · obtain ⟨s1, s2, -⟩ := hs
    have hn1 : g ((k : ℤ) * (n : ℤ) + 1) = g 1 := hcar 1 (mem_recCarried_one p)
    have hn2 : g ((k : ℤ) * (n : ℤ) + 2) = g 2 := hcar 2 (mem_recCarried_two p)
    have hy : g ((k : ℤ) * (p : ℤ)) = (n : ℤ) := by
      rw [hvaly, ← hn1, ← s1, inv2]
    have hz : g ((k : ℤ) * ((p : ℤ) + 1))
        = g ((k : ℤ) * (n : ℤ) + ((p : ℤ) + 4)) := by
      rw [hvalz, ← hn2, ← s2]
    refine ⟨?_, fun i => g ((k : ℤ) * i + ((p : ℤ) + 4)), ?_, ?_, ?_⟩
    · rw [hy]
      omega
    · exact hbaseAt
    · intro i hi0 hiy
      rw [hy] at hiy
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) := ⟨i.toNat, by omega⟩
      exact hstepAt j (by omega)
    · show g ((k : ℤ) * g ((k : ℤ) * (p : ℤ)) + ((p : ℤ) + 4))
        = g ((k : ℤ) * ((p : ℤ) + 1))
      rw [hy, ← hz]
  · have hA3 : (3 : ℤ) ∈ recActive p := (mem_recActive_iff p 3).mpr ⟨by omega, by omega⟩
    have hA1 : (1 : ℤ) ∈ recActive p := (mem_recActive_iff p 1).mpr ⟨by omega, by omega⟩
    have hA2 : (2 : ℤ) ∈ recActive p := (mem_recActive_iff p 2).mpr ⟨by omega, by omega⟩
    have hA4 : ((p : ℤ) + 4) ∈ recActive p :=
      (mem_recActive_iff p _).mpr ⟨by omega, by omega⟩
    have hn0 : (n : ℤ) = 0 := by
      rw [← inv2]
      exact hidle 3 hA3
    have hy : g ((k : ℤ) * (p : ℤ)) = 0 := by
      rw [hvaly, ← hcar 1 (mem_recCarried_one p)]
      exact hidle 1 hA1
    have hz : g ((k : ℤ) * ((p : ℤ) + 1)) = 0 := by
      rw [hvalz, ← hcar 2 (mem_recCarried_two p)]
      exact hidle 2 hA2
    have hw0 : g ((k : ℤ) * 0 + ((p : ℤ) + 4)) = 0 := by
      have h := hidle ((p : ℤ) + 4) hA4
      rw [hn0] at h
      exact h
    refine ⟨le_of_eq hy.symm, fun i => g ((k : ℤ) * i + ((p : ℤ) + 4)), ?_, ?_, ?_⟩
    · exact hbaseAt
    · intro i hi0 hiy
      rw [hy] at hiy
      exact absurd hi0 (by omega)
    · show g ((k : ℤ) * g ((k : ℤ) * (p : ℤ)) + ((p : ℤ) + 4))
        = g ((k : ℤ) * ((p : ℤ) + 1))
      rw [hy, hz, hw0]

/-! ## 8.  The trace of a given run -/

/-- The entry at track `d` of block `q` of the trace built from a run. -/
def recEntry (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q d : ℤ) : ℤ :=
  if d = 0 then (if 0 ≤ q ∧ q ≤ (p : ℤ) + 1 then f q else 0)
  else if q ≤ y then
    (if d = 1 then y
     else if d = 2 then z
     else if d = 3 then q
     else if d = (p : ℤ) + 4 then v q
     else if 4 ≤ d ∧ d ≤ (p : ℤ) + 3 then f (d - 4) else 0)
  else 0

theorem recEntry_val (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ) (h0 : 0 ≤ q)
    (h1 : q ≤ (p : ℤ) + 1) : recEntry p f y z v q 0 = f q := by
  have h : 0 ≤ q ∧ q ≤ (p : ℤ) + 1 := ⟨h0, h1⟩
  simp [recEntry, h]

theorem recEntry_val_out (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ)
    (h : ¬ (0 ≤ q ∧ q ≤ (p : ℤ) + 1)) : recEntry p f y z v q 0 = 0 := by
  simp [recEntry, h]

theorem recEntry_Y (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ) (hq : q ≤ y) :
    recEntry p f y z v q 1 = y := by simp [recEntry, hq]

theorem recEntry_Z (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ) (hq : q ≤ y) :
    recEntry p f y z v q 2 = z := by simp [recEntry, hq]

theorem recEntry_C (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ) (hq : q ≤ y) :
    recEntry p f y z v q 3 = q := by simp [recEntry, hq]

theorem recEntry_W (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q : ℤ) (hq : q ≤ y) :
    recEntry p f y z v q ((p : ℤ) + 4) = v q := by
  have e0 : ¬ ((p : ℤ) + 4 = 0) := by omega
  have e1 : ¬ ((p : ℤ) + 4 = 1) := by omega
  have e2 : ¬ ((p : ℤ) + 4 = 2) := by omega
  have e3 : ¬ ((p : ℤ) + 4 = 3) := by omega
  simp [recEntry, hq, e0, e1, e2, e3]

theorem recEntry_X (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q d : ℤ) (hq : q ≤ y)
    (hd4 : 4 ≤ d) (hdp : d ≤ (p : ℤ) + 3) : recEntry p f y z v q d = f (d - 4) := by
  have e0 : ¬ (d = 0) := by omega
  have e1 : ¬ (d = 1) := by omega
  have e2 : ¬ (d = 2) := by omega
  have e3 : ¬ (d = 3) := by omega
  have e4 : ¬ (d = (p : ℤ) + 4) := by omega
  have e5 : 4 ≤ d ∧ d ≤ (p : ℤ) + 3 := ⟨hd4, hdp⟩
  simp [recEntry, hq, e0, e1, e2, e3, e4, e5]

theorem recEntry_off (p : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q d : ℤ) (hq : y < q)
    (hd : d ≠ 0) : recEntry p f y z v q d = 0 := by
  have h : ¬ (q ≤ y) := by omega
  simp [recEntry, hd, h]

/-- **The trace of a run.**  Blocks `0` to `y` carry the computation; the value
track carries the output tuple at the blocks `0` to `p+1`, which is why the
trace is built out to the block `y + p + 1`. -/
noncomputable def recWitness (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) : E :=
  blockSeq (k : ℤ) (y + (p : ℤ) + 1) (recEntry p f y z v)

theorem recWitness_in (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q d : ℤ) (hk : 0 < (k : ℤ))
    (hq0 : 0 ≤ q) (hqN : q ≤ y + (p : ℤ) + 1) (hd0 : 0 ≤ d) (hdk : d < (k : ℤ)) :
    recWitness p k f y z v ((k : ℤ) * q + d) = recEntry p f y z v q d :=
  blockSeq_in (k : ℤ) (y + (p : ℤ) + 1) (recEntry p f y z v) q d hk hq0 hqN hd0 hdk

theorem recWitness_neg (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (i : ℤ) (hi : i < 0) :
    recWitness p k f y z v i = 0 :=
  blockSeq_neg (k : ℤ) (y + (p : ℤ) + 1) (recEntry p f y z v) i hi

/-- A coordinate in a block at a negative index is itself negative. -/
theorem block_coord_of_neg (k : ℕ) (q d : ℤ) (hk : 0 < (k : ℤ)) (hq : q < 0) (hd0 : 0 ≤ d)
    (hdk : d < (k : ℤ)) : (k : ℤ) * q + d < 0 := by
  have hmul : (k : ℤ) * q ≤ (k : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  have he : (k : ℤ) * (-1) = -(k : ℤ) := by ring
  linarith

/-- Every block strictly beyond the computation is blank, whether or not the
builder reached it. -/
theorem recWitness_blank (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (q d : ℤ)
    (hk : 0 < (k : ℤ)) (hq : y < q) (hd : d ≠ 0) (hd0 : 0 ≤ d) (hdk : d < (k : ℤ)) :
    recWitness p k f y z v ((k : ℤ) * q + d) = 0 := by
  rcases lt_or_le q 0 with hneg | hpos
  · exact recWitness_neg p k f y z v _ (block_coord_of_neg k q d hk hneg hd0 hdk)
  · rcases le_or_lt q (y + (p : ℤ) + 1) with hin | hout
    · rw [recWitness_in p k f y z v q d hk hpos hin hd0 hdk]
      exact recEntry_off p f y z v q d hq hd
    · exact blockSeq_out (k : ℤ) (y + (p : ℤ) + 1) (recEntry p f y z v) q d hk hout hd0 hdk

/-- The value track of the trace of a run. -/
theorem recWitness_value (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (hk : 0 < (k : ℤ))
    (hy : 0 ≤ y) (i : ℤ) (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + 1) :
    recWitness p k f y z v ((k : ℤ) * i) = f i := by
  have e : (k : ℤ) * i = (k : ℤ) * i + 0 := by ring
  rw [e, recWitness_in p k f y z v i 0 hk h0 (by omega) (by omega) (by omega),
    recEntry_val p f y z v i h0 h1]

theorem recWitness_value_out (p k : ℕ) (f : E) (y z : ℤ) (v : ℤ → ℤ) (hk : 0 < (k : ℤ))
    (i : ℤ) (h : ¬ (0 ≤ i ∧ i ≤ (p : ℤ) + 1)) :
    recWitness p k f y z v ((k : ℤ) * i) = 0 := by
  have e : (k : ℤ) * i = (k : ℤ) * i + 0 := by ring
  rcases lt_or_le i 0 with hneg | hpos
  · rw [e]
    exact recWitness_neg p k f y z v _ (block_coord_of_neg k i 0 hk hneg (by omega) (by omega))
  · rcases le_or_lt i (y + (p : ℤ) + 1) with hin | hout
    · rw [e, recWitness_in p k f y z v i 0 hk hpos hin (by omega) (by omega),
        recEntry_val_out p f y z v i h]
    · rw [e]
      exact blockSeq_out (k : ℤ) (y + (p : ℤ) + 1) (recEntry p f y z v) i 0 hk hout
        (by omega) (by omega)

/-! ## 9.  The trace of a run is a trace -/

theorem recWitness_mem_anchor (p k : ℕ) (hk : p + 5 ≤ k) (G : Set E) (f : E)
    (y z : ℤ) (v : ℤ → ℤ) (hy : 0 ≤ y)
    (hbase : recBaseAt p G (fun j : ℕ => f (j : ℤ)) (v 0))
    (hyv : f (p : ℤ) = y) (hzv : f ((p : ℤ) + 1) = z) :
    recWitness p k f y z v ∈ recAnchor p k G := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by omega
  have hpar : ∀ j : ℕ, j < p → recWitness p k f y z v (4 + (j : ℤ)) = f (j : ℤ) := by
    intro j hj
    have hjz : (j : ℤ) < (p : ℤ) := by exact_mod_cast hj
    have e : (4 : ℤ) + (j : ℤ) = (k : ℤ) * 0 + (4 + (j : ℤ)) := by ring
    rw [e, recWitness_in p k f y z v 0 (4 + (j : ℤ)) hk0 (by omega) (by omega)
        (by omega) (by omega),
      recEntry_X p f y z v 0 (4 + (j : ℤ)) hy (by omega) (by omega),
      show (4 : ℤ) + (j : ℤ) - 4 = (j : ℤ) from by ring]
  have hrun0 : recWitness p k f y z v ((p : ℤ) + 4) = v 0 := by
    have e : (p : ℤ) + 4 = (k : ℤ) * 0 + ((p : ℤ) + 4) := by ring
    rw [e, recWitness_in p k f y z v 0 ((p : ℤ) + 4) hk0 (by omega) (by omega)
        (by omega) (by omega),
      recEntry_W p f y z v 0 hy]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    exact recWitness_neg p k f y z v i hi
  · show recWitness p k f y z v 3 = 0
    have e : (3 : ℤ) = (k : ℤ) * 0 + 3 := by ring
    rw [e, recWitness_in p k f y z v 0 3 hk0 (by omega) (by omega) (by omega) (by omega),
      recEntry_C p f y z v 0 hy]
  · obtain ⟨w, hw, hwx, hwu⟩ := hbase
    refine ⟨w, hw, fun j hj => ?_⟩
    rcases lt_or_le j p with h1 | h1
    · rw [baseCoord_param p j h1, hpar j h1]
      exact (hwx j h1).symm
    · have hjp : j = p := by omega
      rw [hjp, baseCoord_last p, hrun0]
      exact hwu.symm
  · refine Set.mem_iInter₂.mpr fun j hj => ?_
    have hjp : j < p := Finset.mem_range.mp hj
    show recWitness p k f y z v ((k : ℤ) * (j : ℤ)) = recWitness p k f y z v (4 + (j : ℤ))
    rw [hpar j hjp, recWitness_value p k f y z v hk0 hy (j : ℤ) (by omega) (by omega)]
  · show recWitness p k f y z v ((k : ℤ) * (p : ℤ)) = recWitness p k f y z v 1
    have e : (1 : ℤ) = (k : ℤ) * 0 + 1 := by ring
    rw [recWitness_value p k f y z v hk0 hy (p : ℤ) (by omega) (by omega), e,
      recWitness_in p k f y z v 0 1 hk0 (by omega) (by omega) (by omega) (by omega),
      recEntry_Y p f y z v 0 hy]
    exact hyv
  · show recWitness p k f y z v ((k : ℤ) * ((p : ℤ) + 1)) = recWitness p k f y z v 2
    have e : (2 : ℤ) = (k : ℤ) * 0 + 2 := by ring
    rw [recWitness_value p k f y z v hk0 hy ((p : ℤ) + 1) (by omega) (by omega), e,
      recWitness_in p k f y z v 0 2 hk0 (by omega) (by omega) (by omega) (by omega),
      recEntry_Z p f y z v 0 hy]
    exact hzv

theorem recWitness_mem_transition (p k : ℕ) (hk : p + 5 ≤ k) (H : Set E) (f : E)
    (y z : ℤ) (v : ℤ → ℤ)
    (hstep : ∀ i : ℤ, 0 ≤ i → i < y →
      recStepAt p H (fun j : ℕ => f (j : ℤ)) i (v i) (v (i + 1)))
    (hend : v y = z) :
    recWitness p k f y z v ∈ transitionSet k (recStep p k H) := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by omega
  have hact : ∀ q d : ℤ, 0 ≤ q → q ≤ y → 1 ≤ d → d ≤ (p : ℤ) + 4 →
      recWitness p k f y z v ((k : ℤ) * q + d) = recEntry p f y z v q d :=
    fun q d h1 h2 h3 h4 =>
      recWitness_in p k f y z v q d hk0 h1 (by omega) (by omega) (by omega)
  intro r
  rw [mem_recStep_window p k hk]
  rcases lt_or_le r 0 with hr | hr
  · refine Or.inr (Or.inr ?_)
    intro d hd
    obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
    exact recWitness_neg p k f y z v _
      (block_coord_of_neg k r d hk0 hr (by omega) (by omega))
  · rcases lt_or_le y r with hfar | hnear
    · refine Or.inr (Or.inr ?_)
      intro d hd
      obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
      exact recWitness_blank p k f y z v r d hk0 hfar (by omega) (by omega) (by omega)
    · rcases eq_or_lt_of_le hnear with heq | hlt
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · rw [hact r 3 hr (by omega) (by omega) (by omega),
            hact r 1 hr (by omega) (by omega) (by omega),
            recEntry_C p f y z v r (by omega), recEntry_Y p f y z v r (by omega)]
          omega
        · rw [hact r ((p : ℤ) + 4) hr (by omega) (by omega) (by omega),
            hact r 2 hr (by omega) (by omega) (by omega),
            recEntry_W p f y z v r (by omega), recEntry_Z p f y z v r (by omega), heq]
          exact hend
        · intro d hd
          obtain ⟨b1, b2⟩ := (mem_recActive_iff p d).mp hd
          exact recWitness_blank p k f y z v (r + 1) d hk0 (by omega) (by omega)
            (by omega) (by omega)
      · have hr1 : (0 : ℤ) ≤ r + 1 := by omega
        have hn1 : r + 1 ≤ y := by omega
        refine Or.inl ⟨?_, ?_, ?_⟩
        · intro d hd
          obtain ⟨b3, b1, b2⟩ := (mem_recCarried_iff p d).mp hd
          rw [hact (r + 1) d hr1 hn1 (by omega) (by omega),
            hact r d hr (by omega) (by omega) (by omega)]
          rcases eq_or_ne d 1 with rfl | hd1
          · rw [recEntry_Y p f y z v (r + 1) hn1, recEntry_Y p f y z v r (by omega)]
          · rcases eq_or_ne d 2 with rfl | hd2
            · rw [recEntry_Z p f y z v (r + 1) hn1, recEntry_Z p f y z v r (by omega)]
            · rw [recEntry_X p f y z v (r + 1) d hn1 (by omega) (by omega),
                recEntry_X p f y z v r d (by omega) (by omega) (by omega)]
        · rw [hact (r + 1) 3 hr1 hn1 (by omega) (by omega),
            hact r 3 hr (by omega) (by omega) (by omega),
            recEntry_C p f y z v (r + 1) hn1, recEntry_C p f y z v r (by omega)]
        · obtain ⟨w, hw, hwx, hwn, hwu, hwu'⟩ := hstep r hr hlt
          refine ⟨w, hw, fun j hj => ?_, ?_, ?_, ?_⟩
          · have hjz : (j : ℤ) < (p : ℤ) := by exact_mod_cast hj
            rw [hact r (4 + (j : ℤ)) hr (by omega) (by omega) (by omega),
              recEntry_X p f y z v r (4 + (j : ℤ)) (by omega) (by omega) (by omega),
              show (4 : ℤ) + (j : ℤ) - 4 = (j : ℤ) from by ring]
            exact (hwx j hj).symm
          · rw [hact r 3 hr (by omega) (by omega) (by omega),
              recEntry_C p f y z v r (by omega)]
            exact hwn.symm
          · rw [hact r ((p : ℤ) + 4) hr (by omega) (by omega) (by omega),
              recEntry_W p f y z v r (by omega)]
            exact hwu.symm
          · rw [hact (r + 1) ((p : ℤ) + 4) hr1 hn1 (by omega) (by omega),
              recEntry_W p f y z v (r + 1) hn1]
            exact hwu'.symm

/-! ## 10.  The identification -/

/-- **The projection of the traces, cut down to the window, is the graph of the
primitive recursion.** -/
theorem recGraph_eq (p k : ℕ) (hk : p + 5 ≤ k) (G H : Set E) :
    recGraph p G H = recProj p k G H ∩ windowSupport (p + 2) := by
  have hkz : (p : ℤ) + 5 ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by omega
  have hcp : ((p + 2 : ℕ) : ℤ) = (p : ℤ) + 2 := by omega
  ext f
  constructor
  · rintro ⟨hlo, hhi, hy0, v, hbase, hstep, hend⟩
    refine ⟨⟨recWitness p k f (f (p : ℤ)) (f ((p : ℤ) + 1)) v, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact recWitness_mem_transition p k hk H f (f (p : ℤ)) (f ((p : ℤ) + 1)) v hstep hend
    · exact recWitness_mem_anchor p k hk G f (f (p : ℤ)) (f ((p : ℤ) + 1)) v hy0 hbase rfl rfl
    · intro i
      by_cases hi : 0 ≤ i ∧ i ≤ (p : ℤ) + 1
      · rw [recWitness_value p k f (f (p : ℤ)) (f ((p : ℤ) + 1)) v hk0 hy0 i hi.1 hi.2]
      · rw [recWitness_value_out p k f (f (p : ℤ)) (f ((p : ℤ) + 1)) v hk0 i hi]
        rcases lt_or_le i 0 with hneg | hpos
        · exact hlo i hneg
        · exact hhi i (by omega)
    · rw [mem_windowSupport_iff, hcp]
      exact ⟨hlo, hhi⟩
  · rintro ⟨⟨g, hg, hproj⟩, hw⟩
    rw [mem_windowSupport_iff, hcp] at hw
    have hfun : (fun j : ℕ => f ((j : ℕ) : ℤ)) = (fun j : ℕ => g ((k : ℤ) * (j : ℤ))) :=
      funext fun j => hproj (j : ℤ)
    refine ⟨hw.1, hw.2, ?_⟩
    rw [hfun, hproj (p : ℤ), hproj ((p : ℤ) + 1)]
    exact recTrace_run p k hk G H hg

/-- **Primitive recursion preserves generation.**  This is Higman's Lemma 2.4:
one run of the transition device, anchored at the origin, with `G` at the start
and `H` at every step. -/
theorem higmanGenerated_recGraph (p k t : ℕ) (hk : p + 5 ≤ k) (hkt : (2 : ℤ) ^ t = (k : ℤ))
    (G H : Set E) (hG : HigmanGenerated G) (hH : HigmanGenerated H)
    (hEq : ∀ d₁ d₂ : ℤ, HigmanGenerated (eqCoord d₁ d₂))
    (hSucc : ∀ d₁ d₂ : ℤ, HigmanGenerated (succCoord d₁ d₂))
    (hPlace : ∀ (n : ℕ) (c : ℕ → ℤ), (∀ i j : ℕ, i < n → j < n → c i = c j → i = j) →
      ∀ R : Set E, HigmanGenerated R → HigmanGenerated (placeAt n c R)) :
    HigmanGenerated (recGraph p G H) := by
  rw [recGraph_eq p k hk G H]
  exact HigmanGenerated.inter
    (higmanGenerated_recProj p k t hk hkt G H hG hH hEq hSucc hPlace)
    (higmanGenerated_windowSupport (p + 2))

end Seq
end Higman
end GroupApproximation
