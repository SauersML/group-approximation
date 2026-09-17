import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Section corners: lobes of the outer face

Let `B` be the boundary traversal of a face `F` with `n` darts, and write `ℓ i` for the `i`-th dart
of the reversed traversal, read cyclically (`ell`).  The face permutation steps backwards along
`ℓ`: `φ (ℓ (i + 1)) = ℓ i`.  For `F` the outer face, `α (ℓ i)` is the `i`-th dart of the oriented
outer boundary `outerDarts`.

## The lobe of a corner

Take positions `p ≠ q < n` with `φ (α (ℓ p)) = α (ℓ q)`, the darts `α (ℓ p)`, `α (ℓ q)` based off
`F`: an interior face walk turns at the vertex from the outer dart at `p` to the outer dart at `q`.
The *lobe* is the list `ℓ (q - 1), ℓ (q - 2), …, ℓ (p + 1)` (indices mod `n`), the darts of `F`
at the open cyclic interval `(p, q)` (`InOpen`).

* Chain.  `σ (α (ℓ (i + 1))) = ℓ i`, so consecutive lobe darts are joined at a vertex.
* Turning.  For a lobe dart other than the last one, `σ (α d)` is the next lobe dart.  For the last
  dart `ℓ (p + 1)`: `σ (α (ℓ (p + 1))) = ℓ p`, which is off the walk (its reversal is based off
  `F`, and `p ∉ (p, q)`); `σ (ℓ p) = φ (α (ℓ p)) = α (ℓ q)`, off the walk for the same reason;
  `σ (α (ℓ q)) = ℓ (q - 1)`, the first lobe dart.  So the first kept rotation is a lobe dart.
* Hence the enclosure API (`FirstTurnEnclosure.mem_iff_enclosedFaces`) applies on the planar map.

## Separation (`lobe_separation`)

Let `p' ∈ (p, q)` with `α (ℓ p')` based off `F`.  Let `x`, `x'` be darts with
`face x = face (α (ℓ p))`, `face x' = face (α (ℓ p'))`, both reversals based off `F`, and
`face (α x) = face (α x')`.  This is impossible:

1. `F` holds lobe darts, so `F` is not enclosed.
2. A dart based off `F` whose reversal is also based off `F` is not kept by the lobe.
3. `ℓ p'` is a lobe dart whose reversal is not a lobe dart, so `face (α (ℓ p'))` is enclosed, that
   is `face x'` is enclosed.  Crossing the edge of `x'`, `face (α x') = face (α x)` is enclosed;
   crossing the edge of `α x`, `face x = face (α (ℓ p))` is enclosed.
4. `α (ℓ p)` is not kept (`ℓ p` is not a lobe dart), so crossing it `face (ℓ p) = F` is enclosed,
   contradicting 1.

In the corner count, `x` and `x'` are darts of two polygon walks with their reversals on the same
relator cell: two corners at nested positions cannot charge the same cell.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

open Equiv

universe v

variable {M : CombMap.{v}} {F : M.Face} (B : FaceBoundary M F)

theorem getElem_idx_eq {α : Type*} (l : List α) {a b : ℕ} {ha : a < l.length}
    {hb : b < l.length} (h : a = b) : l[a] = l[b] := by
  subst h
  rfl

theorem length_pos : 0 < B.darts.length := List.length_pos_iff.mpr B.nonempty

/-- The `i`-th dart of the reversed boundary traversal, read cyclically. -/
def ell (i : ℕ) : M.Dart :=
  B.darts.reverse[i % B.darts.length]'(by
    rw [List.length_reverse]
    exact Nat.mod_lt _ (length_pos B))

theorem ell_eq_of_mod_eq {i i' : ℕ} (h : i % B.darts.length = i' % B.darts.length) :
    ell B i = ell B i' :=
  getElem_idx_eq _ h

theorem ell_add_length (i : ℕ) : ell B (i + B.darts.length) = ell B i :=
  ell_eq_of_mod_eq B (Nat.add_mod_right i _)

theorem ell_of_lt {i : ℕ} (hi : i < B.darts.length) :
    ell B i = B.darts.reverse[i]'(by rw [List.length_reverse]; exact hi) :=
  getElem_idx_eq _ (Nat.mod_eq_of_lt hi)

theorem faceOf_ell (i : ℕ) : M.faceOf (ell B i) = F := by
  refine (B.mem_iff _).mp (List.mem_reverse.mp ?_)
  unfold ell
  exact List.getElem_mem _

theorem ell_inj {i i' : ℕ} (hi : i < B.darts.length) (hi' : i' < B.darts.length)
    (h : ell B i = ell B i') : i = i' := by
  rw [ell_of_lt B hi, ell_of_lt B hi'] at h
  exact (List.nodup_reverse.mpr B.nodup).getElem_inj_iff.mp h

theorem facePerm_ell_succ_of_lt {r : ℕ} (hr : r < B.darts.length) :
    M.facePerm (ell B (r + 1)) = ell B r := by
  rcases Nat.lt_or_ge (r + 1) B.darts.length with h | h
  · rw [ell_of_lt B h, ell_of_lt B hr, List.getElem_reverse, List.getElem_reverse]
    have hc := List.isChain_iff_getElem.mp B.chain (B.darts.length - 1 - (r + 1)) (by omega)
    exact Eq.trans hc (getElem_idx_eq _ (by omega))
  · have h0 : r + 1 = B.darts.length := by omega
    rw [ell_eq_of_mod_eq B (i := r + 1) (i' := 0) (by rw [h0, Nat.mod_self, Nat.zero_mod]),
      ell_of_lt B (length_pos B), ell_of_lt B hr, List.getElem_reverse, List.getElem_reverse]
    have hcl := B.closes
    rw [List.getLast_eq_getElem, List.head_eq_getElem] at hcl
    exact (congrArg M.facePerm (getElem_idx_eq _ (by omega))).trans
      (hcl.trans (getElem_idx_eq _ (by omega)))

/-- **The face permutation steps backwards along `ℓ`.** -/
theorem facePerm_ell_succ (i : ℕ) : M.facePerm (ell B (i + 1)) = ell B i := by
  have h := facePerm_ell_succ_of_lt B (Nat.mod_lt i (length_pos B))
  rwa [ell_eq_of_mod_eq B (i := i % B.darts.length + 1) (i' := i + 1) (Nat.mod_add_mod _ _ _),
    ell_eq_of_mod_eq B (i := i % B.darts.length) (i' := i) (Nat.mod_mod _ _)] at h

theorem sigma_alpha_ell (i : ℕ) : M.sigma (M.alpha (ell B (i + 1))) = ell B i := by
  have h := facePerm_ell_succ B i
  rwa [CombMap.facePerm, Equiv.Perm.mul_apply] at h

/-- The open cyclic interval `(p, q)` of positions. -/
def InOpen (p q i : ℕ) : Prop :=
  (p < q ∧ p < i ∧ i < q) ∨ (q < p ∧ (p < i ∨ i < q))

/-- The half-open cyclic interval `(p, q]` of positions. -/
def InHalfOpen (p q t : ℕ) : Prop :=
  (p < q ∧ p < t ∧ t ≤ q) ∨ (q < p ∧ (p < t ∨ t ≤ q))

/-- The number of positions strictly between `p` and `q`, cyclically mod `n`. -/
def lobeLen (n p q : ℕ) : ℕ :=
  if p < q then q - p - 1 else q + n - p - 1

/-- **The lobe of `(p, q)`**: the darts `ℓ (q - 1), …, ℓ (p + 1)`. -/
def lobe (p q : ℕ) : List M.Dart :=
  (List.range (lobeLen B.darts.length p q)).map fun j => ell B (q + B.darts.length - 1 - j)

theorem lobe_length (p q : ℕ) : (lobe B p q).length = lobeLen B.darts.length p q := by
  rw [lobe, List.length_map, List.length_range]

theorem lobe_getElem (p q j : ℕ) (hj : j < (lobe B p q).length) :
    (lobe B p q)[j] = ell B (q + B.darts.length - 1 - j) := by
  simp only [lobe, List.getElem_map, List.getElem_range]

theorem mem_lobe {p q : ℕ} {d : M.Dart} :
    d ∈ lobe B p q ↔
      ∃ j, j < lobeLen B.darts.length p q ∧ ell B (q + B.darts.length - 1 - j) = d := by
  simp only [lobe, List.mem_map, List.mem_range]

theorem faceOf_of_mem_lobe {p q : ℕ} {d : M.Dart} (hd : d ∈ lobe B p q) : M.faceOf d = F := by
  obtain ⟨j, -, rfl⟩ := (mem_lobe B).mp hd
  exact faceOf_ell B _

theorem lobeLen_le (p q : ℕ) : lobeLen B.darts.length p q ≤ q + B.darts.length - 1 := by
  unfold lobeLen
  split_ifs <;> omega

theorem ell_mem_lobe {p q i : ℕ} (hp : p < B.darts.length) (hi : i < B.darts.length)
    (h : InOpen p q i) : ell B i ∈ lobe B p q := by
  refine (mem_lobe B).mpr ?_
  unfold InOpen at h
  by_cases hiq : i < q
  · refine ⟨q - 1 - i, ?_, ?_⟩
    · unfold lobeLen
      split_ifs <;> omega
    · refine ell_eq_of_mod_eq B ?_
      rw [show q + B.darts.length - 1 - (q - 1 - i) = i + B.darts.length by omega,
        Nat.add_mod_right]
  · refine ⟨q + B.darts.length - 1 - i, ?_, congrArg (ell B) (by omega)⟩
    unfold lobeLen
    split_ifs <;> omega

theorem inOpen_of_ell_mem {p q i : ℕ} (hq : q < B.darts.length) (hi : i < B.darts.length)
    (hpq : p ≠ q) (h : ell B i ∈ lobe B p q) : InOpen p q i := by
  obtain ⟨j, hj, hji⟩ := (mem_lobe B).mp h
  unfold lobeLen at hj
  unfold InOpen
  by_cases ha : q + B.darts.length - 1 - j < B.darts.length
  · have := ell_inj B ha hi hji
    split_ifs at hj <;> omega
  · rw [show q + B.darts.length - 1 - j = (q - 1 - j) + B.darts.length by omega,
      ell_add_length] at hji
    have := ell_inj B (by omega) hi hji
    split_ifs at hj <;> omega

theorem lobe_isChain (p q : ℕ) :
    (lobe B p q).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
  refine List.isChain_iff_getElem.mpr fun j hj => ?_
  have hlen := lobe_length B p q
  have hle := lobeLen_le B p q
  rw [lobe_getElem, lobe_getElem]
  have h := sigma_alpha_ell B (q + B.darts.length - 1 - (j + 1))
  rw [show q + B.darts.length - 1 - (j + 1) + 1 = q + B.darts.length - 1 - j by omega] at h
  rw [← h]
  exact (M.vertexOf_sigma _).symm

theorem sigma_pow_one (x : M.Dart) : (M.sigma ^ 1) x = M.sigma x := by
  rw [pow_one]

theorem sigma_pow_two (x : M.Dart) : (M.sigma ^ 2) x = M.sigma (M.sigma x) := by
  rw [pow_two, Equiv.Perm.mul_apply]

theorem sigma_pow_three (x : M.Dart) : (M.sigma ^ 3) x = M.sigma (M.sigma (M.sigma x)) := by
  rw [pow_succ, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

/-- A middle lobe dart turns to the next lobe dart. -/
theorem lobe_turn_middle {p q j : ℕ} (hj1 : j + 1 < (lobe B p q).length) :
    M.sigma (M.alpha (ell B (q + B.darts.length - 1 - j))) = (lobe B p q)[j + 1] := by
  have hlen := lobe_length B p q
  have hle := lobeLen_le B p q
  rw [lobe_getElem, show q + B.darts.length - 1 - j = (q + B.darts.length - 1 - (j + 1)) + 1 by
    omega]
  exact sigma_alpha_ell B _

/-- The rotations at the last lobe dart. -/
theorem lobe_last_rotations {p q : ℕ} (hq : q < B.darts.length)
    (hface : M.facePerm (M.alpha (ell B p)) = M.alpha (ell B q)) :
    M.sigma (M.alpha (ell B (p + 1))) = ell B p ∧ M.sigma (ell B p) = M.alpha (ell B q) ∧
      M.sigma (M.alpha (ell B q)) = ell B (q + B.darts.length - 1) := by
  refine ⟨sigma_alpha_ell B p, ?_, ?_⟩
  · have h := hface
    rwa [CombMap.facePerm, Equiv.Perm.mul_apply, M.alpha_involutive (ell B p)] at h
  · have h := sigma_alpha_ell B (q + B.darts.length - 1)
    rwa [show q + B.darts.length - 1 + 1 = q + B.darts.length by omega, ell_add_length] at h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.getElem_idx_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.length_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell_eq_of_mod_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell_add_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.faceOf_ell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell_inj
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.facePerm_ell_succ_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.facePerm_ell_succ
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.sigma_alpha_ell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.InOpen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.InHalfOpen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobeLen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.mem_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.faceOf_of_mem_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobeLen_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.ell_mem_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.inOpen_of_ell_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.sigma_pow_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.sigma_pow_two
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.sigma_pow_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe_turn_middle
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.lobe_last_rotations
