import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: value one on same-cell junction gaps

Target: `OsinLemma94CellJunctionValueInput`.

## Notation

`X = S.diagram`, `M` its combinatorial map, `f = P.face k` the polygon face.  Side `s` has kind
`cell j` and joins the next side at kind level, so the next side also has kind `cell j`.  Write
`C = (cell X j).face`, `e` for the last dart of side `s`, `e'` for the first dart of the next side,
`a = α e'`, `b = α e`.  Then `σ b = α a`, both `a` and `b` are darts of the cell `C`, and with
`m` least such that `facePerm^(m+1) a = b` the gap is `α (facePerm^m a), …, α (facePerm a)`.
Put `p = facePerm^m a` and `J = joined M p a`, the map with the corner split.  The two sides of
the corner are apart (`JunctionPocket.junction_not_reach`): `b` does not reach `facePerm a` in `J`.

`seg x n` is the face walk `x, facePerm x, …, facePerm^(n-1) x`.

## The proof

If `m = 0` the gap is empty and reads `1`.  Otherwise fix an outer dart `o₀`.  By
`JunctionPocket.reach_or_reach`, in `J` the dart `o₀` is reached from `b` or from `facePerm a`.

**Case A (exterior on the face side): `J b o₀`.**  The gap walk `c = seg (facePerm a) m` is a
face walk of `C`: it is nodup, each dart turns into the next one by `facePerm`, and it closes by a
first turn from `p` past `b` and `α a` to `facePerm a` (`firstTurn_three`; `b` and `α a` are off
the edges of `c`, by minimality of `m` and since `α b`, `α a` lie on `f ≠ C`).  Let `E` be the
enclosed faces of `c`.  The darts `p` and `a` lie on `C ∉ E`.  A face class path from a seed
`α y`, `y ∈ c`, runs by face steps off `p, a` and by reversals, which are steps of `J`
(`reach_of_enclosed`); every seed is reached from `facePerm a` (`JunctionPocket.reach_gap`).  So
every dart on a face of `E` is reached from `facePerm a` in `J`, and the outer face is not in `E`
since `o₀` is reached from `b`.  Hence `E` is an enclosed face set over `c`
(`enclosedFaceSetSucc_of_chain`).  The walk `c` is an arc of the cell `C`
(`CyclicArc.exists_darts_eq_map_pow`), and `C ∉ E`.  A relator cell in `E` gives a loop cut, which
the clause below the number of relator cells refutes (the hypothesis `NoCellInside`, discharged in
`Proof.lean` through `enclosedSubdiagramLoopCutSuccLong` with empty connector).  So `E` holds no
relator cell and the enclosed subdiagram has no relator cell: the reversed walk, which is the gap,
reads `1` (`SameCellSpurEnclosure.listVal_eq_one_of_enclosedSucc`).

**Case B (exterior on the gap side): `J (facePerm a) o₀`.**  We show that the polygon has at most
one class non-join, against the hypothesis.

*The hole.*  Let `n ≥ 1` be least with `facePerm^n p = a`, and `c_h = seg b n`, the darts
`b, …, a` of `C` after the gap.  It is nodup by minimality, a face walk, and closes by a first turn
from `a` to `b`: with `K` least such that `σ^(K+1) (α a) = b`, every intermediate dart
`σ^t (α a)`, `1 ≤ t ≤ K`, is reached from `facePerm a` in `J` (by induction, since it is neither
`α a` — else `J.σ (α a) = facePerm p = b` is reached — nor `α p`, by minimality), while every dart
of `c_h` is reached from `b` (face steps off `p`, `a`); a kept intermediate would join the two sides.
Let `E_h` be its enclosed faces.  Then `f ∈ E_h` (the seed `α b = e`), `C ∉ E_h`, and the outer face
is not in `E_h` (every dart on a face of `E_h` is reached from `b`, and `o₀` from `facePerm a`).

*Every dart of `f` sits in the hole.*  For a dart `y` of `f` whose reverse is not on `C`, `y` is off
the edges of `c_h`, so `faceOf (α y) ∈ E_h`.  Going through the kinds of the sides of `k`:
* a boundary side gives the outer face in `E_h`: impossible;
* a cell side of kind `cell i` gives the face of cell `i` in `E_h`, so `i = j` (`NoCellInside` for
  the arc `c_h`, and injectivity of cell faces);
* a short side gives a region face `g ∈ E_h`.  Along the boundary cycle of the region, `E_h`
  membership propagates (face steps and internal moves are off the edges of `c_h`).  The source arc
  is nonempty, so the source cell face is in `E_h` unless the source is `j`; the target arc is
  nonempty, so the target is not `none` (outer face) and is `some j`.  But the target is not the
  source (`respects`): impossible;
* a cutting side has `f` on both sides.  Then every dart of `f` whose reverse is not on `f` has
  reverse on `C`.  For a dart `d` with `f` on both sides take `L` least with
  `facePerm^(L+1) d = α d` and the walk `A_d = seg (facePerm d) L`; it closes past `α d`.  `L = 0`
  is a leaf, against `DartMinimal`.  By strong induction on `L`, `A_d` holds a dart whose reverse is
  on `C`: if `facePerm d` has `f` on both sides, planarity puts `α (facePerm d)` inside `A_d`, so the
  walk of `facePerm d` is shorter and inside `A_d`.  Hence `C` is enclosed by `A_d`; the same for
  `α d`, with a dart `y₂ ∈ A_{α d}` whose reverse is on `C`.  If `y₂ ∉ A_d`, the reversal from the
  enclosed face `C` puts `f` in the enclosed faces of `A_d`, against `faceOf_not_mem_enclosedFaces`;
  and `A_d`, `A_{α d}` are disjoint by the minimality of both lengths.  Impossible.

So every side has kind `cell j` and every side joins the next at kind level.

*Values at the other junctions.*  For a side `t ≠ s` with `m_t ≠ 0`, the corners of `s` and `t`
have different `b` (the sides are disjoint), so by `JunctionPocket.reach_face_or_reach_face` the
outer dart is on the face side of `s` or of `t`.  The face side of `s` joins `b` to `facePerm a`;
so it is on the face side of `t`, and Case A at `t` gives value one.  The cell face clause of
`ClassJoins` is `junctionGap_faceOf_ne_face`, and the boundary clause is vacuous.  So every `t ≠ s`
is a class join, and the class non-joins number at most one.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

/-! ## Powers of a permutation -/

theorem pow_sub_apply_eq {α : Type*} {p : Perm α} {x : α} {i j : ℕ} (hij : i ≤ j)
    (h : (p ^ i) x = (p ^ j) x) : (p ^ (j - i)) x = x := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  rw [Nat.add_sub_cancel_left]
  apply (p ^ i).injective
  rw [h, pow_add, Perm.mul_apply]

theorem pow_succ_apply' {α : Type*} (p : Perm α) (x : α) (r : ℕ) :
    (p ^ (r + 1)) x = (p ^ r) (p x) := by
  rw [pow_succ, Perm.mul_apply]

theorem pow_succ_apply {α : Type*} (p : Perm α) (x : α) (r : ℕ) :
    (p ^ (r + 1)) x = p ((p ^ r) x) := by
  rw [pow_succ', Perm.mul_apply]

/-- A permutation of a finite type returns every point after `orderOf p` steps. -/
theorem pow_orderOf_apply {α : Type*} [Fintype α] [DecidableEq α] (p : Perm α) (x : α) (k : ℕ) :
    (p ^ (orderOf p * k)) x = x := by
  rw [pow_mul, pow_orderOf_eq_one, one_pow, Perm.one_apply]

/-! ## Face walks -/

section Seg

variable {M : CombMap.{v}}

/-- The face walk of length `n` from `x`. -/
noncomputable def seg (M : CombMap.{v}) (x : M.Dart) (n : ℕ) : List M.Dart :=
  (List.range n).map fun r => (M.facePerm ^ r) x

theorem mem_seg {x y : M.Dart} {n : ℕ} : y ∈ seg M x n ↔ ∃ r < n, (M.facePerm ^ r) x = y := by
  unfold seg
  simp only [List.mem_map, List.mem_range]

theorem length_seg (x : M.Dart) (n : ℕ) : (seg M x n).length = n := by
  unfold seg
  rw [List.length_map, List.length_range]

theorem seg_ne_nil {x : M.Dart} {n : ℕ} (hn : n ≠ 0) : seg M x n ≠ [] := by
  intro h
  have h' := congrArg List.length h
  rw [length_seg, List.length_nil] at h'
  exact hn h'

theorem seg_isChain (x : M.Dart) (n : ℕ) :
    (seg M x n).IsChain fun d e => M.facePerm d = e := by
  refine List.isChain_iff_getElem.mpr fun i hi => ?_
  simp only [seg, List.getElem_map, List.getElem_range]
  rw [pow_succ_apply]

theorem seg_head {x : M.Dart} {n : ℕ} (hn : n ≠ 0) : (seg M x n).head (seg_ne_nil hn) = x := by
  rw [List.head_eq_getElem]
  simp only [seg, List.getElem_map, List.getElem_range, pow_zero, Perm.one_apply]

theorem seg_getLast {x : M.Dart} {n : ℕ} (hn : n ≠ 0) :
    (seg M x n).getLast (seg_ne_nil hn) = (M.facePerm ^ (n - 1)) x := by
  rw [List.getLast_eq_getElem]
  simp only [seg, List.getElem_map, List.getElem_range, List.length_map, List.length_range]

theorem faceOf_of_mem_seg {x y : M.Dart} {n : ℕ} (hy : y ∈ seg M x n) :
    M.faceOf y = M.faceOf x := by
  obtain ⟨r, -, rfl⟩ := mem_seg.mp hy
  exact JunctionPocket.faceOf_pow_apply x r

theorem seg_nodup {x : M.Dart} {n : ℕ} (hper : ∀ r, 0 < r → r < n → (M.facePerm ^ r) x ≠ x) :
    (seg M x n).Nodup := by
  unfold seg
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  rw [List.mem_range] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hper (j - i) (by omega) (by omega) (pow_sub_apply_eq h.le hij)
  · exact hper (i - j) (by omega) (by omega) (pow_sub_apply_eq h.le hij.symm)

theorem seg_subset {x : M.Dart} {n n' : ℕ} (hn : n ≤ n') : seg M x n ⊆ seg M x n' := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := mem_seg.mp hy
  exact mem_seg.mpr ⟨r, by omega, rfl⟩

/-- A face walk from `facePerm x` of a shorter length sits inside the longer walk. -/
theorem seg_facePerm_subset {x : M.Dart} {n n' : ℕ} (hn : n + 1 ≤ n') :
    seg M (M.facePerm x) n ⊆ seg M x n' := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := mem_seg.mp hy
  exact mem_seg.mpr ⟨r + 1, by omega, pow_succ_apply' _ _ _⟩

end Seg

/-! ## First turns -/

/-- Three rotation steps from the reversal, past two darts off the edges of `c`, are a first
turn. -/
theorem firstTurn_three {M : CombMap.{v}} {c : List M.Dart} {x y z₁ z₂ : M.Dart}
    (h₁ : M.sigma (M.alpha x) = z₁) (h₂ : M.sigma z₁ = z₂) (h₃ : M.sigma z₂ = y)
    (hz₁ : ¬ walkKeep M c z₁) (hz₂ : ¬ walkKeep M c z₂) : FirstTurn M c x y := by
  refine ⟨2 + 1, by omega, ?_, fun t ht htk => ?_⟩
  · rw [pow_succ, Perm.mul_apply, pow_two, Perm.mul_apply, h₁, h₂, h₃]
  · obtain rfl | rfl : t = 1 ∨ t = 2 := by omega
    · rw [pow_one, h₁]
      exact hz₁
    · rw [pow_two, Perm.mul_apply, h₁, h₂]
      exact hz₂

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **An enclosed face set over a closed face walk.**  A nodup walk whose darts follow the face
permutation and that closes by a first turn, with the outer face not enclosed. -/
theorem enclosedFaceSetSucc_of_chain (X : DiscDiagram.{u, w, v} W) {c : List X.toCombMap.Dart}
    (hc : c ≠ []) (hnodup : c.Nodup)
    (hfp : c.IsChain fun d e => X.toCombMap.facePerm d = e)
    (hclose : FirstTurn X.toCombMap c (c.getLast hc) (c.head hc))
    (hout : X.outerFace ∉ enclosedFaces X.toCombMap c) :
    EnclosedFaceSetSucc X (enclosedFaces X.toCombMap c) c := by
  have hfchain : c.IsChain (FirstTurn X.toCombMap c) :=
    hfp.imp fun _ _ h => FirstTurn.of_facePerm h
  have hchain : c.IsChain fun d d' =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf d' :=
    hfchain.imp fun _ _ h => h.vertexOf_eq
  have hturn : TurnMem X.toCombMap c := turnMem_of_firstTurn hc hfchain hclose
  exact
    { outerFace_not_mem := hout
      ne_nil := hc
      nodup := hnodup
      chain := hchain
      closes := hclose.vertexOf_eq
      mem_iff := mem_iff_enclosedFaces X.planar hc hchain hturn
      turn_mem := hturn
      turn_next := fun _ hi _ hm hkeep hfirst =>
        eq_of_firstTurn (firstTurn_getElem_succ hc hfchain hclose hi (Nat.mod_lt _ (by omega)))
          (List.getElem_mem _) hm hkeep hfirst }

/-- The planar facts of a closed face walk: its vertex chain and turn clause. -/
theorem turnMem_of_chain {M : CombMap.{v}} {c : List M.Dart} (hc : c ≠ [])
    (hfp : c.IsChain fun d e => M.facePerm d = e)
    (hclose : FirstTurn M c (c.getLast hc) (c.head hc)) :
    (c.IsChain fun d d' => M.vertexOf (M.alpha d) = M.vertexOf d') ∧ TurnMem M c := by
  have hfchain : c.IsChain (FirstTurn M c) := hfp.imp fun _ _ h => FirstTurn.of_facePerm h
  exact ⟨hfchain.imp fun _ _ h => h.vertexOf_eq, turnMem_of_firstTurn hc hfchain hclose⟩

/-- A dart of a closed face walk is on a face that is not enclosed. -/
theorem faceOf_not_mem_of_chain {M : CombMap.{v}} (hM : M.IsPlanar) {c : List M.Dart}
    (hc : c ≠ []) (hfp : c.IsChain fun d e => M.facePerm d = e)
    (hclose : FirstTurn M c (c.getLast hc) (c.head hc)) {d : M.Dart} (hd : d ∈ c) :
    M.faceOf d ∉ enclosedFaces M c :=
  faceOf_not_mem_enclosedFaces hM hc (turnMem_of_chain hc hfp hclose).1
    (turnMem_of_chain hc hfp hclose).2 hd

/-- The membership criterion of a closed face walk. -/
theorem mem_iff_of_chain {M : CombMap.{v}} (hM : M.IsPlanar) {c : List M.Dart}
    (hc : c ≠ []) (hfp : c.IsChain fun d e => M.facePerm d = e)
    (hclose : FirstTurn M c (c.getLast hc) (c.head hc)) (d : M.Dart) :
    d ∈ c ↔ M.faceOf d ∉ enclosedFaces M c ∧
      (M.faceOf (M.alpha d) ∈ enclosedFaces M c ∨ M.alpha d ∈ c) :=
  mem_iff_enclosedFaces hM hc (turnMem_of_chain hc hfp hclose).1
    (turnMem_of_chain hc hfp hclose).2 d

/-! ## Enclosed faces are reached in a joined map -/

section Reach

variable {M : CombMap.{v}}

/-- A seed of a closed walk is on an enclosed face. -/
theorem faceOf_alpha_mem_of_seed {c : List M.Dart} {y : M.Dart} (hy : y ∈ c)
    (hya : M.alpha y ∉ c) : M.faceOf (M.alpha y) ∈ enclosedFaces M c :=
  (mem_enclosedFaces_iff M c _).mpr ⟨y, hy, hya, .refl _⟩

/-- A dart off the edges of `c` on an enclosed face has its reverse on an enclosed face, and
conversely. -/
theorem faceOf_alpha_mem_iff {c : List M.Dart} {x : M.Dart} (hk : ¬ walkKeep M c x) :
    M.faceOf (M.alpha x) ∈ enclosedFaces M c ↔ M.faceOf x ∈ enclosedFaces M c := by
  have hk' : ¬ walkKeep M c (M.alpha x) := by
    rwa [walkKeep_alpha]
  refine ⟨fun hx => ?_, fun hx => faceOf_alpha_mem_enclosedFaces hk hx⟩
  have h' := faceOf_alpha_mem_enclosedFaces hk' hx
  rwa [M.alpha_involutive x] at h'

/-- **Transport of face classes into a joined map.**  Along a face class path of `c`, enclosed
membership is preserved, and on enclosed faces the steps are steps of the joined map, as long as
the joined darts are on faces that are not enclosed. -/
theorem eqvGen_joined_transport {c : List M.Dart} {p a r : M.Dart}
    (hp : M.faceOf p ∉ enclosedFaces M c) (ha : M.faceOf a ∉ enclosedFaces M c)
    {z z' : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) z z') :
    (M.faceOf z ∈ enclosedFaces M c ↔ M.faceOf z' ∈ enclosedFaces M c) ∧
      (M.faceOf z ∈ enclosedFaces M c →
        (Relation.EqvGen (FoldMap.joined M p a).Adjacent r z ↔
          Relation.EqvGen (FoldMap.joined M p a).Adjacent r z')) := by
  induction h with
  | rel x y hxy =>
      rcases hxy with rfl | ⟨hk, rfl⟩
      · rw [M.faceOf_facePerm]
        refine ⟨Iff.rfl, fun hx => ?_⟩
        have hstep := JunctionPocket.joined_reach_facePerm (M := M) (p := p) (e := a) (x := x)
          (fun h0 => hp (h0 ▸ hx)) (fun h0 => ha (h0 ▸ hx))
        exact ⟨fun h1 => .trans _ _ _ h1 hstep, fun h1 => .trans _ _ _ h1 (.symm _ _ hstep)⟩
      · exact ⟨(faceOf_alpha_mem_iff hk).symm,
          fun _ => JunctionPocket.eqvGen_iff_of_adjacent (Or.inl rfl)⟩
  | refl x => exact ⟨Iff.rfl, fun _ => Iff.rfl⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy => (ih.2 (ih.1.mpr hy)).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, fun hx => (ih₁.2 hx).trans (ih₂.2 (ih₁.1.mp hx))⟩

/-- **Enclosed faces are reached.**  If every seed of `c` is reached from `r` in the joined map
and the joined darts are on faces that are not enclosed, every dart on an enclosed face is reached
from `r`. -/
theorem reach_of_enclosed {c : List M.Dart} {p a r : M.Dart}
    (hp : M.faceOf p ∉ enclosedFaces M c) (ha : M.faceOf a ∉ enclosedFaces M c)
    (hseed : ∀ y ∈ c, M.alpha y ∉ c →
      Relation.EqvGen (FoldMap.joined M p a).Adjacent r (M.alpha y))
    {x : M.Dart} (hx : M.faceOf x ∈ enclosedFaces M c) :
    Relation.EqvGen (FoldMap.joined M p a).Adjacent r x := by
  obtain ⟨y, hy, hya, hcls⟩ := (mem_enclosedFaces_iff M c x).mp hx
  exact ((eqvGen_joined_transport (r := r) hp ha hcls).2 (faceOf_alpha_mem_of_seed hy hya)).mp
    (hseed y hy hya)

/-- Seeds reached through the walk: if every dart of `c` is reached from `r`, so is every seed. -/
theorem seed_of_reach {c : List M.Dart} {p a r : M.Dart}
    (hall : ∀ y ∈ c, Relation.EqvGen (FoldMap.joined M p a).Adjacent r y) :
    ∀ y ∈ c, M.alpha y ∉ c →
      Relation.EqvGen (FoldMap.joined M p a).Adjacent r (M.alpha y) :=
  fun y hy _ => (JunctionPocket.eqvGen_iff_of_adjacent (Or.inl rfl)).mp (hall y hy)

end Reach

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue
