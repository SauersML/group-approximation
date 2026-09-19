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

end Seq
end Higman
end GroupApproximation
