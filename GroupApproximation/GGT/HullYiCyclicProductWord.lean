import GroupApproximation.GGT.HullYiCyclicProductAssembly
import GroupApproximation.GGT.HullYiCyclicOrientation
import GroupApproximation.GGT.DGOLemma421Statement

/-!
# The relative word for Hull's cyclic `yi` products

Hull applies DGO Lemma 4.21(b) to powers of the word

`a₀ a₁ ⋯ aₖ₋₁`,

where `aᵢ ∈ E(fᵢ)` and the factors are indexed in their natural cyclic
order.  This file constructs that word from the `Fin`-indexed letter family and
proves the facts needed at the 4.21 call site: its value is the ordered product,
all letters are admissible in the elementary-closure cone-off, and every power
of the word satisfies (W1)--(W3) once its letters are deep.

No component match is assumed here.  The only remaining geometric input after
this module is DGO Lemma 4.21(b) itself (and the depth supplied when the powers
are selected).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- A finite relative word whose `i`-th letter is placed in the peripheral
subgroup `index i`. -/
def indexedPeripheralWord {k : ℕ} {Λ : Type w} (index : Fin k → Λ)
    (a : Fin k → G) : List (RelLetter G Λ) :=
  List.ofFn (fun i ↦ RelLetter.comp (index i) (a i))

/-- The one-cycle relative word `a₀ a₁ ⋯ aₖ₋₁`, with the `i`-th
letter placed in the `i`-th peripheral subgroup. -/
def finPeripheralWord {k : ℕ} (a : Fin k → G) :
    List (RelLetter G (Fin k)) := indexedPeripheralWord id a

omit [Group G] in
@[simp] theorem length_finPeripheralWord {k : ℕ} (a : Fin k → G) :
    (finPeripheralWord a).length = k := by
  simp [finPeripheralWord, indexedPeripheralWord]

omit [Group G] in
@[simp] theorem finPeripheralWord_zero (a : Fin 0 → G) :
    finPeripheralWord a = [] := by
  simp [finPeripheralWord, indexedPeripheralWord]

omit [Group G] in
@[simp] theorem indexedPeripheralWord_zero {Λ : Type w}
    (index : Fin 0 → Λ) (a : Fin 0 → G) :
    indexedPeripheralWord index a = [] := by
  simp [indexedPeripheralWord]

omit [Group G] in
@[simp] theorem indexedPeripheralWord_succ {k : ℕ} {Λ : Type w}
    (index : Fin (k + 1) → Λ) (a : Fin (k + 1) → G) :
    indexedPeripheralWord index a = RelLetter.comp (index 0) (a 0) ::
      indexedPeripheralWord (fun i ↦ index i.succ) (fun i ↦ a i.succ) := by
  simp [indexedPeripheralWord, List.ofFn_succ]

omit [Group G] in
@[simp] theorem length_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) :
    (indexedPeripheralWord index a).length = k := by
  simp [indexedPeripheralWord]

omit [Group G] in
@[simp] theorem getElem?_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) (i : Fin k) :
    (indexedPeripheralWord index a)[i.val]? =
      some (RelLetter.comp (index i) (a i)) := by
  simp [indexedPeripheralWord]

/-- The ambient peripheral indices do not affect the value of the word. -/
@[simp] theorem listVal_indexedPeripheralWord :
    ∀ {k : ℕ} {Λ : Type w} (index : Fin k → Λ) (a : Fin k → G),
      RelLetter.listVal (indexedPeripheralWord index a) = orderedFinProduct a := by
  intro k Λ index a
  induction k with
  | zero => simp [indexedPeripheralWord, orderedFinProduct, RelLetter.listVal]
  | succ k ih =>
      rw [indexedPeripheralWord_succ, RelWord.listVal_cons]
      change a 0 * RelLetter.listVal
        (indexedPeripheralWord (fun i ↦ index i.succ) (fun i ↦ a i.succ)) = _
      rw [ih]
      rfl

/-- The relative word spells exactly the ordered product used by the algebraic
assembly. -/
@[simp] theorem listVal_finPeripheralWord {k : ℕ} (a : Fin k → G) :
    RelLetter.listVal (finPeripheralWord a) = orderedFinProduct a := by
  exact listVal_indexedPeripheralWord id a

omit [Group G] in
/-- Every letter in the cyclic word is the indicated peripheral letter. -/
theorem exists_eq_comp_of_mem_finPeripheralWord {k : ℕ} (a : Fin k → G)
    {c : RelLetter G (Fin k)} (hc : c ∈ finPeripheralWord a) :
    ∃ i : Fin k, c = RelLetter.comp i (a i) := by
  simpa [finPeripheralWord, indexedPeripheralWord, eq_comm] using hc

omit [Group G] in
/-- Membership in the ambient-index form. -/
theorem exists_eq_comp_of_mem_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) {c : RelLetter G Λ}
    (hc : c ∈ indexedPeripheralWord index a) :
    ∃ i : Fin k, c = RelLetter.comp (index i) (a i) := by
  simpa [indexedPeripheralWord, eq_comm] using hc

/-- If the `i`-th element belongs to the `i`-th subgroup, the cyclic word is
admissible in that relative generating set. -/
theorem isLetter_finPeripheralWord (D : RelGenSet G (Fin k)) (a : Fin k → G)
    (ha : ∀ i, a i ∈ D.fam i) :
    ∀ c ∈ finPeripheralWord a, D.IsLetter c := by
  intro c hc
  obtain ⟨i, rfl⟩ := exists_eq_comp_of_mem_finPeripheralWord a hc
  exact ha i

/-- Admissibility for the ambient-index form. -/
theorem isLetter_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (D : RelGenSet G Λ) (index : Fin k → Λ) (a : Fin k → G)
    (ha : ∀ i, a i ∈ D.fam (index i)) :
    ∀ c ∈ indexedPeripheralWord index a, D.IsLetter c := by
  intro c hc
  obtain ⟨i, rfl⟩ := exists_eq_comp_of_mem_indexedPeripheralWord index a hc
  exact ha i

omit [Group G] in
/-- The cyclic word contains no base letter. -/
theorem getElem?_finPeripheralWord_ne_base {k : ℕ} (a : Fin k → G)
    (j : ℕ) (y : G) :
    (finPeripheralWord a)[j]? ≠ some (RelLetter.base y) := by
  intro hj
  have hjlt : j < (finPeripheralWord a).length :=
    lt_length_of_getElem?_eq_some hj
  have hjmem : (finPeripheralWord a)[j]'hjlt ∈ finPeripheralWord a :=
    List.getElem_mem hjlt
  obtain ⟨i, hi⟩ := exists_eq_comp_of_mem_finPeripheralWord a hjmem
  have hget : (finPeripheralWord a)[j]? =
      some ((finPeripheralWord a)[j]'hjlt) := List.getElem?_eq_getElem hjlt
  rw [hget, hi] at hj
  simp at hj

omit [Group G] in
/-- The ambient-index word contains no base letter. -/
theorem getElem?_indexedPeripheralWord_ne_base {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) (j : ℕ) (y : G) :
    (indexedPeripheralWord index a)[j]? ≠ some (RelLetter.base y) := by
  intro hj
  have hjlt : j < (indexedPeripheralWord index a).length :=
    lt_length_of_getElem?_eq_some hj
  have hjmem : (indexedPeripheralWord index a)[j]'hjlt ∈
      indexedPeripheralWord index a := List.getElem_mem hjlt
  obtain ⟨i, hi⟩ := exists_eq_comp_of_mem_indexedPeripheralWord index a hjmem
  have hget : (indexedPeripheralWord index a)[j]? =
      some ((indexedPeripheralWord index a)[j]'hjlt) :=
    List.getElem?_eq_getElem hjlt
  rw [hget, hi] at hj
  simp at hj

omit [Group G] in
/-- Powers of the cyclic peripheral word satisfy (W1) automatically. -/
theorem isWOne_blockWord_finPeripheralWord {k : ℕ} (a : Fin (k + 1) → G)
    (n : ℕ) :
    WWord.IsWOne
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  exact isWOne_blockWord_of_noBase (Fin.last k)
    (getElem?_indexedPeripheralWord_ne_base
      (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
      (a (Fin.last k)) n

/-- Powers of the cyclic peripheral word satisfy (W2) when every letter is
outside the common relative-ball threshold. -/
theorem isWTwo_blockWord_finPeripheralWord (D : RelGenSet G (Fin (k + 1)))
    {C : ℕ} (a : Fin (k + 1) → G)
    (hdeep : ∀ i, a i ∉ D.relBall i C) (n : ℕ) :
    WWord.IsWTwo D C
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  apply isWTwo_blockWord_of_deep D (Fin.last k)
  · intro j mu g hj
    have hjlt : j <
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)).length :=
      lt_length_of_getElem?_eq_some hj
    have hjmem := List.getElem_mem
      (l := indexedPeripheralWord (fun i ↦ i.castSucc)
        (fun i ↦ a i.castSucc)) hjlt
    obtain ⟨i, hi⟩ :=
      exists_eq_comp_of_mem_indexedPeripheralWord
        (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc) hjmem
    have hget := List.getElem?_eq_getElem hjlt
    rw [hget, hi] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1, ← hj.2]
    exact hdeep i.castSucc
  · exact hdeep (Fin.last k)

/-- Powers of a cyclic peripheral word with at least two factors satisfy
(W3): adjacent letters have consecutive, hence distinct, `Fin` indices,
including at the last/prefix and wrap seams. -/
theorem isWThree_blockWord_finPeripheralWord (D : RelGenSet G (Fin (k + 1)))
    (hk : 1 ≤ k) (a : Fin (k + 1) → G) (n : ℕ) :
    WWord.IsWThree D
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  let pre : List (RelLetter G (Fin (k + 1))) :=
    indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
  apply isWThree_blockWord_of_cyclic D (Fin.last k)
  · intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · exact getElem?_indexedPeripheralWord_ne_base
      (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
  · intro j mu nu g₁ g₂ hj hj₁
    have hjlt : j < k := by
      have := lt_length_of_getElem?_eq_some hj
      simpa [pre] using this
    have hj₁lt : j + 1 < k := by
      have := lt_length_of_getElem?_eq_some hj₁
      simpa [pre] using this
    let i : Fin k := ⟨j, hjlt⟩
    let i₁ : Fin k := ⟨j + 1, hj₁lt⟩
    have hi := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i
    have hi₁ := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i₁
    change pre[j]? = _ at hi
    change pre[j + 1]? = _ at hi₁
    rw [hi] at hj
    rw [hi₁] at hj₁
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj hj₁
    rw [← hj.1, ← hj₁.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp [i, i₁] at hval
  · intro j mu g hjlen hj
    have hjlt : j < k := by
      have := lt_length_of_getElem?_eq_some hj
      simpa [pre] using this
    let i : Fin k := ⟨j, hjlt⟩
    have hi := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i
    change pre[j]? = _ at hi
    rw [hi] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp [i] at hval
    have hprelen : pre.length = k := by simp [pre]
    rw [hprelen] at hjlen
    omega
  · intro mu g hj
    have h0 := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc)
      ⟨0, hk⟩
    change pre[0]? = _ at h0
    rw [h0] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp at hval
    omega

/-! ## The direct DGO 4.21(b) call site -/

/-- The word consisting of `n` copies of one full cyclic peripheral run. -/
def cyclicPeripheralPowerWord {k : ℕ} (a : Fin (k + 1) → G) (n : ℕ) :
    List (RelLetter G (Fin (k + 1))) :=
  OsinComponents.blockWord (Fin.last k)
    (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
    (a (Fin.last k)) n

omit [Group G] in
@[simp] theorem length_cyclicPeripheralPowerWord {k : ℕ}
    (a : Fin (k + 1) → G) (n : ℕ) :
    (cyclicPeripheralPowerWord a n).length = n * (k + 1) := by
  simp [cyclicPeripheralPowerWord]

omit [Group G] in
/-- The peripheral index at position `j` is `j mod (k+1)`.  This is the exact
cyclic-index bridge used to read the component sequence returned by 4.21(b). -/
theorem getElem?_cyclicPeripheralPowerWord {k n j : ℕ}
    (a : Fin (k + 1) → G)
    (hj : j < (cyclicPeripheralPowerWord a n).length) :
    (cyclicPeripheralPowerWord a n)[j]? =
      some (RelLetter.comp
        ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩
        (a ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩)) := by
  have hj' : j < n * (k + 1) := by simpa using hj
  obtain ⟨t, r, rfl, htn, hr⟩ := exists_block_decomp k hj'
  by_cases hrk : r < k
  · have hidx : t * (k + 1) + r =
        t * ((indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc)).length + 1) + r := by simp
    rw [hidx, cyclicPeripheralPowerWord,
      getElem?_blockWord_pre (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) htn (by simpa using hrk)]
    rw [getElem?_indexedPeripheralWord
      (fun i : Fin k ↦ i.castSucc) (fun i : Fin k ↦ a i.castSucc) ⟨r, hrk⟩]
    simp only [length_indexedPeripheralWord]
    have hmod : (t * (k + 1) + r) % (k + 1) = r := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    simp only [hmod]
    have hfin : (⟨r, hrk⟩ : Fin k).castSucc =
        ⟨r, hr⟩ := Fin.ext rfl
    rw [hfin]
  · have hrEq : r = k := by omega
    subst r
    have hidx : t * (k + 1) + k =
        t * ((indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc)).length + 1) +
            (indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
              (fun i : Fin k ↦ a i.castSucc)).length := by simp
    rw [hidx, cyclicPeripheralPowerWord,
      getElem?_blockWord_comp (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) htn]
    simp only [length_indexedPeripheralWord]
    have hmod : (t * (k + 1) + k) % (k + 1) = k := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
    simp only [hmod]
    have hfin : Fin.last k =
        ⟨k, Nat.lt_succ_self k⟩ := Fin.ext rfl
    rw [hfin]

omit [Group G] in
/-- Every component returned by 4.21(b) on the cyclic word carries the index
predicted by its start position modulo the cycle length. -/
theorem componentIndex_cyclicPeripheralPowerWord {k n i q : ℕ}
    (a : Fin (k + 1) → G) {lam : Fin (k + 1)}
    (hcomp : IsComp lam (cyclicPeripheralPowerWord a n) i q) :
    lam = ⟨i % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩ := by
  obtain ⟨hiq, hq, hall, -, -⟩ := hcomp
  have hi : i < (cyclicPeripheralPowerWord a n).length := lt_of_lt_of_le hiq hq
  have hof : ((cyclicPeripheralPowerWord a n)[i]'hi).IsCompOf lam :=
    hall i le_rfl hiq hi
  obtain ⟨g, hg⟩ := getElem?_comp_of_isCompOf hi hof
  have hexact := getElem?_cyclicPeripheralPowerWord a hi
  rw [hexact] at hg
  simp only [Option.some.injEq, RelLetter.comp.injEq] at hg
  exact hg.1.symm

omit [Group G] in
/-- Since the cyclic peripheral word contains no base letters, the separator
between two consecutive distinguished components supplied by DGO 4.21(b)
cannot be an `X`-edge: it is a trivial path. -/
theorem eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord {k n q i : ℕ}
    (a : Fin (k + 1) → G)
    (h : BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n) q i) :
    i = q := by
  rcases h with h | ⟨x, hi, hx⟩
  · exact h
  · exact False.elim
      (getElem?_blockWord_ne_base (Fin.last k)
        (getElem?_indexedPeripheralWord_ne_base
          (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc))
        (a (Fin.last k)) n q x (by
          simpa [cyclicPeripheralPowerWord] using hx))

/-- Consecutive components supplied by DGO 4.21(b) on the cyclic peripheral
word advance through the peripheral factors in their natural cyclic order. -/
theorem cyclicSucc_componentIndex_of_consecutiveMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n K : ℕ)
    (ip kp : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcomp : ∀ t : ℕ, t < K →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hstep : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1))) :
    ∀ t : ℕ, t + 1 < K → lam (t + 1) = cyclicSucc (lam t) := by
  intro t ht
  have hkp : kp t = ip t + 1 :=
    isComp_succ_of_isWThree
      (isWThree_blockWord_finPeripheralWord D hk a n)
      (hcomp t (by omega))
  have hip : ip (t + 1) = kp t :=
    eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord a (hstep t ht)
  have hlam := componentIndex_cyclicPeripheralPowerWord a (hcomp t (by omega))
  have hlam1 := componentIndex_cyclicPeripheralPowerWord a (hcomp (t + 1) ht)
  rw [hlam, hlam1]
  apply Fin.ext
  simp [cyclicSucc, hip, hkp, Nat.add_mod]

/-- **The literal cyclic-product specialization of DGO Lemma 4.21(b).**

The constants `C,R` are chosen in exactly the order of the printed lemma.
After that, any two sufficiently long powers of deep cyclic peripheral words
whose endpoints are oriented `eps`-close have `K` consecutive component
matches.  All admissibility and (W1)--(W3) premises are discharged here from
the concrete word; the conclusion is DGO's raw component-index output, with no
connector or non-commensurability conclusion inserted. -/
theorem exists_consecutiveMatches_cyclicPeripheralPowerWord_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) {k : ℕ}
    (D : RelGenSet G (Fin (k + 1)))
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    (hk : 1 ≤ k) (eps : ℝ) (K : ℕ) (heps : 0 < eps) (hK : 0 < K) :
    ∃ C R : ℕ, 0 < R ∧
      ∀ (a b : Fin (k + 1) → G),
        (∀ i, a i ∈ D.fam i) → (∀ i, b i ∈ D.fam i) →
        (∀ i, a i ∉ D.relBall i C) →
        (∀ i, b i ∉ D.relBall i C) →
        ∀ n : ℕ, R ≤ n * (k + 1) → ∀ vp vq : G,
        (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
        (wordDist D.alphabet.carrier
          (vertex vp (cyclicPeripheralPowerWord a n)
            (cyclicPeripheralPowerWord a n).length)
          (vertex vq (cyclicPeripheralPowerWord b n)
            (cyclicPeripheralPowerWord b n).length) : ℝ) ≤ eps →
        ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1)),
          (∀ t : ℕ, t < K →
            IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t)) ∧
          (∀ t : ℕ, t < K →
            IsComp (lam t) (cyclicPeripheralPowerWord b n) (iq t) (kq t)) ∧
          (∀ t : ℕ, t + 1 < K →
            BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
              (kp t) (ip (t + 1))) ∧
          (∀ t : ℕ, t + 1 < K →
            BaseEdgeOrTrivial (cyclicPeripheralPowerWord b n)
              (kq t) (iq (t + 1))) ∧
          ∀ t : ℕ, t < K →
            (vertex vp (cyclicPeripheralPowerWord a n) (ip t))⁻¹ *
              vertex vq (cyclicPeripheralPowerWord b n) (iq t)
                ∈ D.fam (lam t) := by
  obtain ⟨C, hraw⟩ := h421b G (Fin (k + 1)) D hhyp
  obtain ⟨R, hR, hmatch⟩ := hraw eps K heps hK
  refine ⟨C, R, hR, ?_⟩
  intro a b ha hb hdeepA hdeepB n hn vp vq hstart hend
  apply hmatch vp vq (cyclicPeripheralPowerWord a n)
    (cyclicPeripheralPowerWord b n)
  · apply isLetter_of_mem_blockWord D (Fin.last k)
    · exact isLetter_indexedPeripheralWord D
        (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc) (fun i ↦ ha i.castSucc)
    · exact ha (Fin.last k)
  · apply isLetter_of_mem_blockWord D (Fin.last k)
    · exact isLetter_indexedPeripheralWord D
        (fun i ↦ i.castSucc) (fun i ↦ b i.castSucc) (fun i ↦ hb i.castSucc)
    · exact hb (Fin.last k)
  · exact isWOne_blockWord_finPeripheralWord a n
  · exact isWTwo_blockWord_finPeripheralWord D a hdeepA n
  · exact isWThree_blockWord_finPeripheralWord D hk a n
  · exact isWOne_blockWord_finPeripheralWord b n
  · exact isWTwo_blockWord_finPeripheralWord D b hdeepB n
  · exact isWThree_blockWord_finPeripheralWord D hk b n
  · simpa using hn
  · exact hstart
  · exact hend

end HullSC
end GroupApproximation
