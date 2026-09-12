import GroupApproximation.Higman.HigmanPlacement
import GroupApproximation.Higman.HigmanCodingDictionary

/-!
# Primitive-recursive graphs are Higman-generated

This file starts the structural induction that removes the last arithmetic
input from `Higman.BoundedWindowRE`.  Natural numbers are represented by their
nonnegative integer values in a finite coordinate window.  The atomic graphs
of zero, successor and projection are generated here without assumptions.

The later composition and primitive-recursion cases use the finite-coordinate
placement and recursion constructions from `HigmanPlacement`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open List.Vector

/-- The unary condition saying that coordinate `c` represents a natural
number.  It is imposed positionally, so all other coordinates remain free. -/
noncomputable def natAt (c : ℤ) : Set E :=
  placeAt 1 (fun _ => c) nonnegativeValues

theorem mem_natAt_iff (c : ℤ) (f : E) :
    f ∈ natAt c ↔ 0 ≤ f c := by
  constructor
  · rintro ⟨w, hw, hfw⟩
    have hw' := (mem_nonnegativeValues_iff w).mp hw
    have hcoord := hfw 0 (by omega)
    rw [hcoord]
    exact hw'.2
  · intro hf
    let w : E := Finsupp.single 0 (f c)
    refine ⟨w, (mem_nonnegativeValues_iff w).mpr ⟨?_, by simpa [w]⟩, ?_⟩
    · rw [mem_windowSupport_iff]
      constructor <;> intro i hi
      · have hi0 : i ≠ 0 := by omega
        simp [w, hi0]
      · have hi0 : i ≠ 0 := by omega
        simp [w, hi0]
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp [w]

theorem higmanGenerated_natAt (c : ℤ) : HigmanGenerated (natAt c) :=
  higmanGenerated_placeAt 1 (fun _ => c) nonnegativeValues
    higmanGenerated_nonnegativeValues

/-- Every one of the first `n` coordinates represents a natural number. -/
noncomputable def natInputs (n : ℕ) : Set E :=
  ⋂ i ∈ (Finset.univ : Finset (Fin n)), natAt (i.val : ℤ)

theorem mem_natInputs_iff (n : ℕ) (f : E) :
    f ∈ natInputs n ↔ ∀ i : Fin n, 0 ≤ f (i.val : ℤ) := by
  simp only [natInputs, Set.mem_iInter, Finset.mem_univ, forall_const, mem_natAt_iff]

theorem higmanGenerated_natInputs (n : ℕ) : HigmanGenerated (natInputs n) := by
  classical
  unfold natInputs
  exact higmanGenerated_biInter Finset.univ
    (fun i : Fin n => natAt (i.val : ℤ))
    (fun i _ => higmanGenerated_natAt (i.val : ℤ))

/-- The integer-coordinate graph of an `n`-ary natural-number function.
Inputs occupy `[0,n)` and the output occupies coordinate `n`. -/
def natGraph {n : ℕ} (F : List.Vector ℕ n → ℕ) : Set E :=
  {f | f ∈ windowSupport (n + 1) ∧
    (∀ i : Fin n, 0 ≤ f (i.val : ℤ)) ∧
    f (n : ℤ) = (F (List.Vector.ofFn fun i : Fin n => (f (i.val : ℤ)).toNat) : ℤ)}

/-- The canonical sequence carrying the graph point `(x,F(x))`. -/
def natGraphCoords {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : List.Vector ℕ n) : Fin (n + 1) → ℤ :=
  Fin.lastCases (F x : ℤ) (fun i : Fin n => (x.get i : ℤ))

noncomputable def natGraphSeq {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : List.Vector ℕ n) : E :=
  coordSeq (n + 1) (natGraphCoords F x)

@[simp] theorem natGraphSeq_input {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : List.Vector ℕ n) (i : Fin n) :
    natGraphSeq F x (i.val : ℤ) = (x.get i : ℤ) := by
  rw [natGraphSeq, coordSeq_apply_natCast (n + 1) (natGraphCoords F x) i.val (by omega)]
  have hi : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := Fin.ext rfl
  rw [hi]
  simp [natGraphCoords]

@[simp] theorem natGraphSeq_output {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : List.Vector ℕ n) :
    natGraphSeq F x (n : ℤ) = (F x : ℤ) := by
  rw [natGraphSeq, coordSeq_apply_natCast (n + 1) (natGraphCoords F x) n (by omega)]
  have hn : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
  rw [hn]
  simp [natGraphCoords]

/-- Every actual input tuple supplies a canonical member of its natural graph. -/
theorem natGraphSeq_mem {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : List.Vector ℕ n) : natGraphSeq F x ∈ natGraph F := by
  refine ⟨coordSeq_mem_windowSupport (n + 1) (natGraphCoords F x), ?_, ?_⟩
  · intro i
    simp
  · rw [natGraphSeq_output]
    congr 2
    apply List.Vector.eq
    simp

/-- The zero graph is exactly a pin at the sole output coordinate. -/
theorem natGraph_zero_eq :
    natGraph (n := 0) (fun _ => 0) = windowSupport 1 ∩ pinAt 0 0 := by
  ext f
  simp [natGraph, pinAt]

theorem higmanGenerated_natGraph_zero :
    HigmanGenerated (natGraph (n := 0) fun _ => 0) := by
  rw [natGraph_zero_eq]
  exact HigmanGenerated.inter (higmanGenerated_windowSupport 1)
    (higmanGenerated_pinAt 0 0)

/-- The successor graph is the successor atom, with its input restricted to
the natural-number domain. -/
theorem natGraph_succ_eq :
    natGraph (fun v : List.Vector ℕ 1 => Nat.succ v.head) =
      windowSupport 2 ∩ natAt 0 ∩ succPair 0 1 := by
  ext f
  simp only [natGraph, Set.mem_setOf_eq, Set.mem_inter_iff, mem_natAt_iff,
    mem_succPair_iff]
  constructor
  · rintro ⟨hw, hn, hout⟩
    have hn0 : 0 ≤ f 0 := by simpa using hn 0
    refine ⟨⟨hw, hn0⟩, ?_⟩
    calc
      f 1 = (((f 0).toNat.succ : ℕ) : ℤ) := hout
      _ = ((f 0).toNat : ℤ) + 1 := by push_cast; rfl
      _ = f 0 + 1 := by rw [Int.toNat_of_nonneg hn0]
  · rintro ⟨⟨hw, hn⟩, hs⟩
    refine ⟨hw, fun i => ?_, ?_⟩
    · simpa [Fin.eq_zero i] using hn
    · change f 1 = ((f 0).toNat.succ : ℕ)
      rw [Int.natCast_succ, Int.toNat_of_nonneg hn]
      exact hs

theorem higmanGenerated_natGraph_succ :
    HigmanGenerated (natGraph fun v : List.Vector ℕ 1 => Nat.succ v.head) := by
  rw [natGraph_succ_eq]
  exact HigmanGenerated.inter
    (HigmanGenerated.inter (higmanGenerated_windowSupport 2)
      (higmanGenerated_natAt 0))
    (higmanGenerated_succPair 0 1)

/-- A projection graph is equality between the selected input and the output,
with all inputs restricted to natural values. -/
theorem natGraph_get_eq {n : ℕ} (i : Fin n) :
    natGraph (fun v : List.Vector ℕ n => v.get i) =
      windowSupport (n + 1) ∩ natInputs n ∩ eqRel (i.val : ℤ) (n : ℤ) := by
  ext f
  simp only [natGraph, Set.mem_setOf_eq, Set.mem_inter_iff, mem_natInputs_iff,
    mem_eqRel_iff]
  constructor
  · rintro ⟨hw, hn, hout⟩
    refine ⟨⟨hw, hn⟩, ?_⟩
    simpa [Int.toNat_of_nonneg (hn i)] using hout.symm
  · rintro ⟨⟨hw, hn⟩, heq⟩
    refine ⟨hw, hn, ?_⟩
    simpa [Int.toNat_of_nonneg (hn i)] using heq.symm

theorem higmanGenerated_natGraph_get {n : ℕ} (i : Fin n) :
    HigmanGenerated (natGraph fun v : List.Vector ℕ n => v.get i) := by
  rw [natGraph_get_eq]
  exact HigmanGenerated.inter
    (HigmanGenerated.inter (higmanGenerated_windowSupport (n + 1))
      (higmanGenerated_natInputs n))
    (higmanGenerated_eqRel (i.val : ℤ) (n : ℤ))

/-! ## N-ary composition

The original `m` inputs stay in coordinates `[0,m)`, the result stays at
coordinate `m`, and the `n` intermediate values occupy the fresh interval
`[m+1,m+n+1)`.  Each inner graph and the outer graph are placed into this wide
window; the fresh interval is then existentially forgotten in one operation.
-/

/-- Placement of the `i`-th inner graph: its `m` inputs remain in place and
its output is written into the `i`-th fresh coordinate. -/
def natCompInnerCoord (m : ℕ) (i : ℕ) (j : ℕ) : ℤ :=
  if j < m then (j : ℤ) else ((m + 1 + i : ℕ) : ℤ)

/-- Placement of the outer graph: its arguments are the fresh intermediate
coordinates and its output is the retained coordinate `m`. -/
def natCompOuterCoord (m n : ℕ) (j : ℕ) : ℤ :=
  if j < n then ((m + 1 + j : ℕ) : ℤ) else (m : ℤ)

@[simp] theorem natCompInnerCoord_input (m i j : ℕ) (hj : j < m) :
    natCompInnerCoord m i j = (j : ℤ) := by simp [natCompInnerCoord, hj]

@[simp] theorem natCompInnerCoord_output (m i : ℕ) :
    natCompInnerCoord m i m = ((m + 1 + i : ℕ) : ℤ) := by
  simp [natCompInnerCoord]

@[simp] theorem natCompOuterCoord_input (m n j : ℕ) (hj : j < n) :
    natCompOuterCoord m n j = ((m + 1 + j : ℕ) : ℤ) := by
  simp [natCompOuterCoord, hj]

@[simp] theorem natCompOuterCoord_output (m n : ℕ) :
    natCompOuterCoord m n n = (m : ℤ) := by simp [natCompOuterCoord]

/-- The wide relation simultaneously carrying all inner computations and the
outer computation. -/
noncomputable def natCompAssembly {m n : ℕ}
    (F : List.Vector ℕ n → ℕ) (G : Fin n → List.Vector ℕ m → ℕ) : Set E :=
  (⋂ i ∈ (Finset.univ : Finset (Fin n)),
      placeAt (m + 1) (natCompInnerCoord m i.val) (natGraph (G i))) ∩
    placeAt (n + 1) (natCompOuterCoord m n) (natGraph F)

/-- The relation produced by the composition construction. -/
noncomputable def natCompGraph {m n : ℕ}
    (F : List.Vector ℕ n → ℕ) (G : Fin n → List.Vector ℕ m → ℕ) : Set E :=
  (freeAux n (m + 1) (natCompAssembly F G) ∩ windowSupport (m + 1)) ∩
    natInputs m

/-- Generated natural graphs are closed under the concrete n-ary composition
construction.  The semantic identification with the ordinary composite is
proved separately, so this theorem contains only the closure argument. -/
theorem higmanGenerated_natCompGraph {m n : ℕ}
    {F : List.Vector ℕ n → ℕ} {G : Fin n → List.Vector ℕ m → ℕ}
    (hF : HigmanGenerated (natGraph F))
    (hG : ∀ i, HigmanGenerated (natGraph (G i))) :
    HigmanGenerated (natCompGraph F G) := by
  classical
  unfold natCompGraph natCompAssembly
  refine HigmanGenerated.inter
    (HigmanGenerated.inter (higmanGenerated_freeAux n (m + 1) ?_)
      (higmanGenerated_windowSupport (m + 1)))
    (higmanGenerated_natInputs m)
  exact HigmanGenerated.inter
      (higmanGenerated_biInter Finset.univ
        (fun i : Fin n =>
          placeAt (m + 1) (natCompInnerCoord m i.val) (natGraph (G i)))
        (fun i _ => higmanGenerated_placeAt (m + 1)
          (natCompInnerCoord m i.val) (natGraph (G i)) (hG i)))
      (higmanGenerated_placeAt (n + 1) (natCompOuterCoord m n) (natGraph F) hF)

/-- Write a vector of intermediate natural values into the fresh interval of
the composition construction. -/
private noncomputable def natCompWide {m n : ℕ} (f : E) (y : Fin n → ℕ) : E :=
  f + ∑ i : Fin n, Finsupp.single ((m + 1 + i.val : ℕ) : ℤ) (y i : ℤ)

private theorem finsupp_fintypeSum_apply {alpha : Type*} [Fintype alpha]
    (u : alpha → E) (j : ℤ) : (∑ i, u i) j = ∑ i, u i j := by
  classical
  change (Finset.univ.sum u) j = Finset.univ.sum fun i => u i j
  induction (Finset.univ : Finset alpha) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Finsupp.add_apply]

private theorem natCompWide_old {m n : ℕ} (f : E) (y : Fin n → ℕ) (j : ℕ)
    (hj : j < m + 1) : natCompWide (m := m) f y (j : ℤ) = f (j : ℤ) := by
  classical
  unfold natCompWide
  rw [Finsupp.add_apply]
  have hz : (∑ i : Fin n,
      Finsupp.single ((m + 1 + i.val : ℕ) : ℤ) (y i : ℤ)) (j : ℤ) = 0 := by
    rw [finsupp_fintypeSum_apply]
    simp only [Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    omega
  rw [hz, add_zero]

private theorem natCompWide_aux {m n : ℕ} (f : E) (y : Fin n → ℕ)
    (hf : f ∈ windowSupport (m + 1)) (i : Fin n) :
    natCompWide (m := m) f y ((m + 1 + i.val : ℕ) : ℤ) = (y i : ℤ) := by
  classical
  unfold natCompWide
  rw [Finsupp.add_apply]
  have hf0 : f ((m + 1 + i.val : ℕ) : ℤ) = 0 :=
    ((mem_windowSupport_iff (m + 1) f).mp hf).2 _ (by push_cast; omega)
  rw [hf0, zero_add]
  rw [finsupp_fintypeSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [if_neg]
    intro heq
    have hnat : m + 1 + j.val = m + 1 + i.val := by exact_mod_cast heq
    exact hji (Fin.ext (by omega))
  · simp

private theorem natCompWide_off {m n : ℕ} (f : E) (y : Fin n → ℕ) (j : ℤ)
    (hj : ∀ i : Fin n, j ≠ ((m + 1 + i.val : ℕ) : ℤ)) :
    natCompWide (m := m) f y j = f j := by
  classical
  unfold natCompWide
  rw [Finsupp.add_apply]
  have hz : (∑ i : Fin n,
      Finsupp.single ((m + 1 + i.val : ℕ) : ℤ) (y i : ℤ)) j = 0 := by
    rw [finsupp_fintypeSum_apply]
    simp only [Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (hj i).symm]
  rw [hz, add_zero]

/-- The composition construction is exactly the ordinary n-ary composite. -/
theorem natCompGraph_eq {m n : ℕ}
    (F : List.Vector ℕ n → ℕ) (G : Fin n → List.Vector ℕ m → ℕ) :
    natCompGraph F G =
      natGraph (fun x => F (List.Vector.ofFn fun i : Fin n => G i x)) := by
  classical
  ext f
  constructor
  · rintro ⟨⟨⟨g, ⟨hinners, houter⟩, hfg⟩, hfw⟩, hnat⟩
    refine ⟨hfw, (mem_natInputs_iff m f).mp hnat, ?_⟩
    let x : List.Vector ℕ m :=
      List.Vector.ofFn fun j : Fin m => (f (j.val : ℤ)).toNat
    have hold (j : ℕ) (hj : j < m + 1) : g (j : ℤ) = f (j : ℤ) := by
      symm
      exact hfg (j : ℤ) (by intro a ha; omega)
    have hinner (i : Fin n) :
        g ((m + 1 + i.val : ℕ) : ℤ) = (G i x : ℤ) := by
      obtain ⟨w, hw, hplace⟩ :=
        Set.mem_iInter₂.mp hinners i (Finset.mem_univ i)
      have hout := hplace m (by omega)
      simp [natCompInnerCoord] at hout
      rw [hw.2.2] at hout
      have hargs : (List.Vector.ofFn fun j : Fin m => (w (j.val : ℤ)).toNat) = x := by
        congr 1
        funext j
        have hin := hplace j.val (by omega)
        rw [natCompInnerCoord_input _ _ _ j.isLt, hold j.val (by omega)] at hin
        simpa [x] using congrArg Int.toNat hin.symm
      rw [hargs] at hout
      simpa only [Nat.cast_add, Nat.cast_one] using hout
    obtain ⟨w, hw, hplace⟩ := houter
    have hout := hplace n (by omega)
    rw [natCompOuterCoord_output, hw.2.2] at hout
    have hargs : (List.Vector.ofFn fun i : Fin n => (w (i.val : ℤ)).toNat) =
        List.Vector.ofFn fun i : Fin n => G i x := by
      congr 1
      funext i
      have hin := hplace i.val (by omega)
      rw [natCompOuterCoord_input _ _ _ i.isLt] at hin
      simpa using congrArg Int.toNat (hin.symm.trans (hinner i))
    rw [hargs] at hout
    simpa [x] using (hold m (by omega)).symm.trans hout
  · rintro hf
    let x : List.Vector ℕ m :=
      List.Vector.ofFn fun j : Fin m => (f (j.val : ℤ)).toNat
    let y : Fin n → ℕ := fun i => G i x
    let g : E := natCompWide (m := m) f y
    refine ⟨⟨⟨g, ?_, ?_⟩, hf.1⟩, (mem_natInputs_iff m f).mpr hf.2.1⟩
    · constructor
      · refine Set.mem_iInter₂.mpr fun i _ => ?_
        refine ⟨natGraphSeq (G i) x, natGraphSeq_mem (G i) x, fun j hj => ?_⟩
        by_cases hjm : j < m
        · rw [natCompInnerCoord_input _ _ _ hjm,
            natCompWide_old f y j (by omega)]
          rw [natGraphSeq_input (G i) x ⟨j, hjm⟩]
          simp only [x, List.Vector.get_ofFn,
            Int.toNat_of_nonneg (hf.2.1 ⟨j, hjm⟩)]
        · have hjm' : j = m := by omega
          subst j
          rw [natCompInnerCoord_output, natCompWide_aux f y hf.1 i,
            natGraphSeq_output]
      · refine ⟨natGraphSeq F (List.Vector.ofFn y),
          natGraphSeq_mem F (List.Vector.ofFn y), fun j hj => ?_⟩
        by_cases hjn : j < n
        · rw [natCompOuterCoord_input _ _ _ hjn,
            natCompWide_aux f y hf.1 ⟨j, hjn⟩,
            natGraphSeq_input F (List.Vector.ofFn y) ⟨j, hjn⟩]
          simp only [List.Vector.get_ofFn]
        · have hjn' : j = n := by omega
          subst j
          rw [natCompOuterCoord_output, natCompWide_old f y m (by omega),
            natGraphSeq_output]
          exact hf.2.2
    · intro j hj
      apply (natCompWide_off f y j ?_).symm
      intro i
      exact hj i.val i.isLt

/-! ## Primitive recursion: the generated construction

`recGraph` expects the step variables in the order
`parameters, counter, old value, new value`.  `Nat.Primrec'.prec` supplies its
step graph in the order `counter, old value, parameters, new value`, so one
finite placement is the whole adapter between the two conventions.
-/

def natRecStepCoord (n : ℕ) (j : ℕ) : ℤ :=
  if j = 0 then (n : ℤ)
  else if j = 1 then ((n + 1 : ℕ) : ℤ)
  else if j < n + 2 then ((j - 2 : ℕ) : ℤ)
  else ((n + 2 : ℕ) : ℤ)

noncomputable def natRecStep {n : ℕ}
    (H : List.Vector ℕ (n + 2) → ℕ) : Set E :=
  placeAt (n + 3) (natRecStepCoord n) (natGraph H) ∩ windowSupport (n + 3)

noncomputable def natRecGraph {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ) : Set E :=
  recGraph n (natGraph F) (natRecStep H)

/-- A canonical step point, written in the coordinate order consumed by
`recGraph`: parameters, counter, old value, new value. -/
def natRecNativeCoords {n : ℕ} (H : List.Vector ℕ (n + 2) → ℕ)
    (a : List.Vector ℕ (n + 2)) (i : Fin (n + 3)) : ℤ :=
  if hi : i.val < n then (a.get ⟨i.val + 2, by omega⟩ : ℤ)
  else if hcount : i.val = n then (a.get ⟨0, by omega⟩ : ℤ)
  else if hold : i.val = n + 1 then (a.get ⟨1, by omega⟩ : ℤ)
  else (H a : ℤ)

noncomputable def natRecNativeSeq {n : ℕ} (H : List.Vector ℕ (n + 2) → ℕ)
    (a : List.Vector ℕ (n + 2)) : E :=
  coordSeq (n + 3) (natRecNativeCoords H a)

@[simp] theorem natRecNativeSeq_param {n : ℕ}
    (H : List.Vector ℕ (n + 2) → ℕ) (a : List.Vector ℕ (n + 2))
    (j : ℕ) (hj : j < n) :
    natRecNativeSeq H a (j : ℤ) = (a.get ⟨j + 2, by omega⟩ : ℤ) := by
  rw [natRecNativeSeq, coordSeq_apply_natCast (n + 3) _ j (by omega)]
  simp [natRecNativeCoords, hj]

@[simp] theorem natRecNativeSeq_count {n : ℕ}
    (H : List.Vector ℕ (n + 2) → ℕ) (a : List.Vector ℕ (n + 2)) :
    natRecNativeSeq H a (n : ℤ) = (a.get ⟨0, by omega⟩ : ℤ) := by
  rw [natRecNativeSeq, coordSeq_apply_natCast (n + 3) _ n (by omega)]
  simp [natRecNativeCoords]

@[simp] theorem natRecNativeSeq_old {n : ℕ}
    (H : List.Vector ℕ (n + 2) → ℕ) (a : List.Vector ℕ (n + 2)) :
    natRecNativeSeq H a ((n + 1 : ℕ) : ℤ) = (a.get ⟨1, by omega⟩ : ℤ) := by
  rw [natRecNativeSeq, coordSeq_apply_natCast (n + 3) _ (n + 1) (by omega)]
  simp [natRecNativeCoords]

@[simp] theorem natRecNativeSeq_output {n : ℕ}
    (H : List.Vector ℕ (n + 2) → ℕ) (a : List.Vector ℕ (n + 2)) :
    natRecNativeSeq H a ((n + 2 : ℕ) : ℤ) = (H a : ℤ) := by
  rw [natRecNativeSeq, coordSeq_apply_natCast (n + 3) _ (n + 2) (by omega)]
  simp [natRecNativeCoords]

@[simp] theorem natRecStepCoord_count (n : ℕ) : natRecStepCoord n 0 = (n : ℤ) := by
  simp [natRecStepCoord]

@[simp] theorem natRecStepCoord_old (n : ℕ) :
    natRecStepCoord n 1 = ((n + 1 : ℕ) : ℤ) := by
  simp [natRecStepCoord]

@[simp] theorem natRecStepCoord_param (n j : ℕ) (hj : j < n) :
    natRecStepCoord n (j + 2) = (j : ℤ) := by
  simp [natRecStepCoord, hj]

@[simp] theorem natRecStepCoord_output (n : ℕ) :
    natRecStepCoord n (n + 2) = ((n + 2 : ℕ) : ℤ) := by
  simp [natRecStepCoord]

theorem natRecNativeSeq_mem {n : ℕ} (H : List.Vector ℕ (n + 2) → ℕ)
    (a : List.Vector ℕ (n + 2)) : natRecNativeSeq H a ∈ natRecStep H := by
  refine ⟨⟨natGraphSeq H a, natGraphSeq_mem H a, fun j hj => ?_⟩,
    coordSeq_mem_windowSupport (n + 3) (natRecNativeCoords H a)⟩
  by_cases h0 : j = 0
  · subst j
    rw [natRecStepCoord_count, natRecNativeSeq_count,
      natGraphSeq_input H a ⟨0, by omega⟩]
  by_cases h1 : j = 1
  · subst j
    rw [natRecStepCoord_old, natRecNativeSeq_old,
      natGraphSeq_input H a ⟨1, by omega⟩]
  by_cases hout : j = n + 2
  · subst j
    rw [natRecStepCoord_output, natRecNativeSeq_output, natGraphSeq_output]
  · let k := j - 2
    have hk : k < n := by omega
    have hjk : j = k + 2 := by omega
    rw [hjk, natRecStepCoord_param n k hk, natRecNativeSeq_param H a k hk,
      natGraphSeq_input H a ⟨k + 2, by omega⟩]

theorem recBaseAt_natGraph_iff {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (x : ℕ → ℤ) (u : ℤ) :
    recBaseAt n (natGraph F) x u ↔
      (∀ j : ℕ, j < n → 0 ≤ x j) ∧
        u = (F (List.Vector.ofFn fun i : Fin n => (x i.val).toNat) : ℤ) := by
  constructor
  · rintro ⟨w, hw, hparam, hout⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← hparam j hj]
      exact hw.2.1 ⟨j, hj⟩
    · have hargs : (List.Vector.ofFn fun i : Fin n => (w (i.val : ℤ)).toNat) =
          List.Vector.ofFn fun i : Fin n => (x i.val).toNat := by
        congr 1
        funext i
        exact congrArg Int.toNat (hparam i.val i.isLt)
      rw [← hout, hw.2.2, hargs]
  · rintro ⟨hnonneg, hu⟩
    let a : List.Vector ℕ n :=
      List.Vector.ofFn fun i : Fin n => (x i.val).toNat
    refine ⟨natGraphSeq F a, natGraphSeq_mem F a, fun j hj => ?_, ?_⟩
    · rw [natGraphSeq_input F a ⟨j, hj⟩]
      simp only [a, List.Vector.get_ofFn, Int.toNat_of_nonneg (hnonneg j hj)]
    · rw [natGraphSeq_output]
      exact hu.symm

def natRecArgs {n : ℕ} (x : ℕ → ℤ) (r u : ℤ) : List.Vector ℕ (n + 2) :=
  r.toNat ::ᵥ u.toNat ::ᵥ
    List.Vector.ofFn fun i : Fin n => (x i.val).toNat

@[simp] theorem natRecArgs_count {n : ℕ} (x : ℕ → ℤ) (r u : ℤ) :
    (natRecArgs (n := n) x r u).get ⟨0, by omega⟩ = r.toNat := by
  simp [natRecArgs]

@[simp] theorem natRecArgs_old {n : ℕ} (x : ℕ → ℤ) (r u : ℤ) :
    (natRecArgs (n := n) x r u).get ⟨1, by omega⟩ = u.toNat := by
  have hi : (⟨1, by omega⟩ : Fin (n + 2)) = (⟨0, by omega⟩ : Fin (n + 1)).succ :=
    Fin.ext rfl
  unfold natRecArgs
  rw [hi, List.Vector.get_cons_succ]
  exact List.Vector.get_cons_zero _ _

@[simp] theorem natRecArgs_param {n : ℕ} (x : ℕ → ℤ) (r u : ℤ)
    (j : ℕ) (hj : j < n) :
    (natRecArgs (n := n) x r u).get ⟨j + 2, by omega⟩ = (x j).toNat := by
  have hi : (⟨j + 2, by omega⟩ : Fin (n + 2)) = (⟨j, hj⟩ : Fin n).succ.succ :=
    Fin.ext (by simp)
  unfold natRecArgs
  rw [hi, List.Vector.get_cons_succ, List.Vector.get_cons_succ]
  exact List.Vector.get_ofFn _ _

theorem recStepAt_natRecStep_iff {n : ℕ} (H : List.Vector ℕ (n + 2) → ℕ)
    (x : ℕ → ℤ) (r u v : ℤ) :
    recStepAt n (natRecStep H) x r u v ↔
      (∀ j : ℕ, j < n → 0 ≤ x j) ∧ 0 ≤ r ∧ 0 ≤ u ∧
        v = (H (natRecArgs (n := n) x r u) : ℤ) := by
  constructor
  · rintro ⟨w, ⟨⟨q, hq, hplace⟩, _⟩, hparam, hcount, hold, hout⟩
    have hr : 0 ≤ r := by
      have h := hq.2.1 (⟨0, by omega⟩ : Fin (n + 2))
      rw [← hplace 0 (by omega), natRecStepCoord_count, hcount] at h
      exact h
    have hu : 0 ≤ u := by
      have h := hq.2.1 (⟨1, by omega⟩ : Fin (n + 2))
      rw [← hplace 1 (by omega), natRecStepCoord_old] at h
      have hold' : w (((n + 1 : ℕ) : ℤ)) = u := by
        simpa only [Nat.cast_add, Nat.cast_one] using hold
      rw [hold'] at h
      exact h
    have hx : ∀ j : ℕ, j < n → 0 ≤ x j := by
      intro j hj
      have h := hq.2.1 (⟨j + 2, by omega⟩ : Fin (n + 2))
      rw [← hplace (j + 2) (by omega), natRecStepCoord_param n j hj,
        hparam j hj] at h
      exact h
    have hargs : (List.Vector.ofFn fun i : Fin (n + 2) => (q (i.val : ℤ)).toNat) =
        natRecArgs (n := n) x r u := by
      rw [← List.Vector.ofFn_get (natRecArgs (n := n) x r u)]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i
      · have h := hplace 0 (by omega)
        rw [natRecStepCoord_count] at h
        calc
          (q (0 : ℤ)).toNat = (w (n : ℤ)).toNat :=
            congrArg Int.toNat h.symm
          _ = r.toNat := congrArg Int.toNat hcount
          _ = (natRecArgs (n := n) x r u).get ⟨0, by omega⟩ :=
            (natRecArgs_count x r u).symm
      · have h := hplace 1 (by omega)
        rw [natRecStepCoord_old] at h
        have hold' : w (((n + 1 : ℕ) : ℤ)) = u := by
          simpa only [Nat.cast_add, Nat.cast_one] using hold
        calc
          (q (1 : ℤ)).toNat = (w (((n + 1 : ℕ) : ℤ))).toNat :=
            congrArg Int.toNat h.symm
          _ = u.toNat := congrArg Int.toNat hold'
          _ = (natRecArgs (n := n) x r u).get ⟨1, by omega⟩ :=
            (natRecArgs_old x r u).symm
      · have h := hplace (j.val + 2) (by omega)
        rw [natRecStepCoord_param n j.val j.isLt] at h
        calc
          (q ((j.val + 2 : ℕ) : ℤ)).toNat =
              (w (j.val : ℤ)).toNat := congrArg Int.toNat h.symm
          _ = (x j.val).toNat := congrArg Int.toNat (hparam j.val j.isLt)
          _ = (natRecArgs (n := n) x r u).get
              ⟨j.val + 2, by omega⟩ :=
            (natRecArgs_param x r u j.val j.isLt).symm
    refine ⟨hx, hr, hu, ?_⟩
    calc
      v = w ((n : ℤ) + 2) := hout.symm
      _ = q ((n + 2 : ℕ) : ℤ) := by
        simpa only [natRecStepCoord_output, Nat.cast_add, Nat.cast_ofNat] using
          hplace (n + 2) (by omega)
      _ = (H (List.Vector.ofFn fun i : Fin (n + 2) => (q (i.val : ℤ)).toNat) : ℤ) := hq.2.2
      _ = (H (natRecArgs (n := n) x r u) : ℤ) := by rw [hargs]
  · rintro ⟨hx, hr, hu, hv⟩
    let a := natRecArgs (n := n) x r u
    refine ⟨natRecNativeSeq H a, natRecNativeSeq_mem H a, fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [natRecNativeSeq_param H a j hj]
      dsimp only [a]
      rw [natRecArgs_param x r u j hj, Int.toNat_of_nonneg (hx j hj)]
    · rw [natRecNativeSeq_count]
      change ((natRecArgs (n := n) x r u).get ⟨0, by omega⟩ : ℤ) = r
      rw [natRecArgs_count, Int.toNat_of_nonneg hr]
    · have h := natRecNativeSeq_old H a
      dsimp only [a] at h
      rw [natRecArgs_old, Int.toNat_of_nonneg hu] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h
    · have h := natRecNativeSeq_output H a
      dsimp only [a] at h
      exact (by simpa only [Nat.cast_add, Nat.cast_ofNat] using h.trans hv.symm)

theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ n := Nat.one_le_pow' n 1
      omega

/-- Primitive recursion preserves generation at the construction level. -/
theorem higmanGenerated_natRecGraph {n : ℕ}
    {F : List.Vector ℕ n → ℕ} {H : List.Vector ℕ (n + 2) → ℕ}
    (hF : HigmanGenerated (natGraph F)) (hH : HigmanGenerated (natGraph H)) :
    HigmanGenerated (natRecGraph F H) := by
  have hstep : HigmanGenerated (natRecStep H) := by
    unfold natRecStep
    exact HigmanGenerated.inter
      (higmanGenerated_placeAt (n + 3) (natRecStepCoord n) (natGraph H) hH)
      (higmanGenerated_windowSupport (n + 3))
  unfold natRecGraph
  refine higmanGenerated_recGraph_of_generated n (2 ^ (n + 5)) (n + 5)
    (nat_le_two_pow (n + 5)) ?_ (natGraph F) (natRecStep H) hF hstep
  norm_num

end Seq
end Higman
end GroupApproximation
