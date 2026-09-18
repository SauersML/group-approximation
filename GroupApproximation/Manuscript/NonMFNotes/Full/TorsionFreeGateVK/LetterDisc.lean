import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGateVK.FaceWords

/-!
# Letter-labelled planar discs as labelled maps

A `LetterDisc R u` is a planar combinatorial map (`GGT.VanKampen.CombMap`) whose darts carry
letters of the free group, reversed darts carrying inverse letters, with a distinguished
outer face reading `u` and every other face reading a word of the symmetrization of `R`:
the letter form of a van Kampen diagram (Lyndon–Schupp, Ch. V §1, Thm. 1.1).

`LetterDisc.toLabelledMap` presents it as a `LabelledMap`, with face rotation
`next = sigma * alpha` and `opp = alpha`, and transports the invariants:

* `orbitDegree_mk`, `sum_one_div_minimalPeriod`: orbit sizes of a permutation are its
  minimal periods, so summing their reciprocals counts orbits;
* `LetterDisc.wordFrom_head`: the face word from the head of a face cycle is the labelling
  of the cycle;
* `LetterDisc.onFace_iff`: `OnFace` is equality of faces;
* `LetterDisc.isConnected`, `LetterDisc.isSpherical`: connectedness and Euler's formula;
* `LetterDisc.wordFrom_outer`, `LetterDisc.wordFrom_mem_symmetrization`.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07a-A.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter GroupApproximation.GGT.VanKampen

universe u v

/-! ## Orbit sizes of a permutation -/

/-- The orbit fibre of `x` has `minimalPeriod p x` elements. -/
theorem orbitDegree_mk {D : Type v} [Fintype D] (p : Equiv.Perm D) (x : D) :
    CombMap.orbitDegree p (Quotient.mk'' x) = Function.minimalPeriod p x := by
  classical
  have hpos : 0 < Function.minimalPeriod p x :=
    Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)
  let f : Fin (Function.minimalPeriod p x) →
      {d : D // (Quotient.mk'' d : CombMap.Orbit p) = Quotient.mk'' x} :=
    fun i => ⟨(p ^ (i : ℕ)) x, Quotient.eq''.mpr
      (Equiv.Perm.sameCycle_pow_left.mpr Equiv.Perm.SameCycle.rfl)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hv : (p ^ (i : ℕ)) x = (p ^ (j : ℕ)) x := congrArg Subtype.val hij
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod (f := p) (x := x)
      (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) hv)
  have hsurj : Function.Surjective f := by
    rintro ⟨d, hd⟩
    have hdx : p.SameCycle d x := Quotient.eq''.mp hd
    obtain ⟨n, hn⟩ := hdx.symm.exists_nat_pow_eq
    refine ⟨⟨n % Function.minimalPeriod p x, Nat.mod_lt _ hpos⟩, Subtype.ext ?_⟩
    exact (Function.iterate_mod_minimalPeriod_eq (f := p) (x := x) (n := n)).trans hn
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm.trans (Nat.card_fin _)

/-- Summing the reciprocal minimal periods over all points counts the orbits. -/
theorem sum_one_div_minimalPeriod {D : Type v} [Fintype D] (p : Equiv.Perm D) :
    (∑ d : D, (1 : ℚ) / (Function.minimalPeriod p d : ℚ)) =
      (Nat.card (CombMap.Orbit p) : ℚ) := by
  classical
  calc (∑ d : D, (1 : ℚ) / (Function.minimalPeriod p d : ℚ))
      = ∑ d : D, (fun o : CombMap.Orbit p => (1 : ℚ) / (CombMap.orbitDegree p o : ℚ))
          (Quotient.mk'' d) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        show (1 : ℚ) / (Function.minimalPeriod p d : ℚ) =
          (1 : ℚ) / (CombMap.orbitDegree p (Quotient.mk'' d) : ℚ)
        rw [orbitDegree_mk]
    _ = ∑ o : CombMap.Orbit p, ∑ _i : {i : D // (Quotient.mk'' i : CombMap.Orbit p) = o},
          (1 : ℚ) / (CombMap.orbitDegree p o : ℚ) :=
        (Fintype.sum_fiberwise' (fun d : D => (Quotient.mk'' d : CombMap.Orbit p)) _).symm
    _ = ∑ _o : CombMap.Orbit p, (1 : ℚ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        have hne : (CombMap.orbitDegree p o : ℚ) ≠ 0 := by
          refine Quotient.inductionOn' o ?_
          intro x
          rw [orbitDegree_mk]
          exact Nat.cast_ne_zero.mpr
            (Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)).ne'
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        exact mul_one_div_cancel hne
    _ = (Nat.card (CombMap.Orbit p) : ℚ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]

/-! ## Paths in a labelled map -/

variable {α : Type u}

theorem path_opp (M : LabelledMap α) (d : M.Dart) :
    Relation.ReflTransGen (fun x y => y = M.next x ∨ y = M.opp x) d (M.opp d) :=
  Relation.ReflTransGen.single (Or.inr rfl)

theorem path_next (M : LabelledMap α) (d : M.Dart) :
    Relation.ReflTransGen (fun x y => y = M.next x ∨ y = M.opp x) d (M.next d) :=
  Relation.ReflTransGen.single (Or.inl rfl)

theorem path_iterate (M : LabelledMap α) (d : M.Dart) :
    ∀ n : ℕ, Relation.ReflTransGen (fun x y => y = M.next x ∨ y = M.opp x) d (M.next^[n] d)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (path_iterate M d n).trans (path_next M _)

/-! ## Letter discs -/

/-- **A letter disc** with boundary `u` over relators `R`: a planar map with letters on its
darts, inverse letters on reversed darts, an outer face cycle reading `u`, and every other
face reading a word of the symmetrization of `R`. -/
structure LetterDisc (R : Set (List (α × Bool))) (u : List (α × Bool)) where
  /-- The underlying planar map. -/
  map : CombMap.{0}
  planar : map.IsPlanar
  /-- The letter on each dart. -/
  label : map.Dart → α × Bool
  label_alpha : ∀ d, label (map.alpha d) = invLetter (label d)
  /-- A face cycle of the outer face. -/
  outer : List map.Dart
  outer_cycle : map.IsFaceCycle outer
  outer_word : outer.map label = u
  face_word : ∀ (l : List map.Dart) (hl : map.IsFaceCycle l),
    map.faceOf (l.head hl.ne_nil) ≠ map.faceOf (outer.head outer_cycle.ne_nil) →
      l.map label ∈ symmetrization R

namespace LetterDisc

variable {R : Set (List (α × Bool))} {u : List (α × Bool)} (D : LetterDisc R u)

/-- The letter disc as a labelled map: `next` is the face rotation, `opp` the reversal. -/
def toLabelledMap : LabelledMap α where
  Dart := D.map.Dart
  instFintype := D.map.dartFintype
  label := D.label
  opp := D.map.alpha
  next := D.map.facePerm
  prev := D.map.facePerm.symm
  opp_opp := D.map.alpha_involutive
  opp_ne := D.map.alpha_fixedPointFree
  next_prev := D.map.facePerm.apply_symm_apply
  prev_next := D.map.facePerm.symm_apply_apply
  label_opp := D.label_alpha

/-- The base dart of the outer face. -/
def base : D.map.Dart := D.outer.head D.outer_cycle.ne_nil

theorem run_eq (d : D.map.Dart) :
    ∀ k : ℕ, D.toLabelledMap.run d k = (orbitWalk D.map.facePerm d k).map D.label
  | 0 => rfl
  | k + 1 => congrArg (List.cons (D.label d)) (run_eq (D.map.facePerm d) k)

/-- The face length of a dart is the degree of its face. -/
theorem flen_eq (d : D.map.Dart) :
    D.toLabelledMap.flen d = D.map.faceDegree (D.map.faceOf d) :=
  (orbitDegree_mk D.map.facePerm d).symm

/-- The face word from the head of a face cycle is the labelling of the cycle. -/
theorem wordFrom_head {l : List D.map.Dart} (hl : D.map.IsFaceCycle l) :
    D.toLabelledMap.wordFrom (l.head hl.ne_nil) = l.map D.label := by
  have hlen : D.toLabelledMap.flen (l.head hl.ne_nil) = l.length := by
    rw [hl.length_eq]
    exact D.flen_eq _
  have hwalk := eq_orbitWalk_of_isChain D.map.facePerm l (l.head hl.ne_nil) hl.chain
    (List.head?_eq_some_head hl.ne_nil)
  show D.toLabelledMap.run (l.head hl.ne_nil) (D.toLabelledMap.flen (l.head hl.ne_nil)) =
    l.map D.label
  rw [hlen, run_eq]
  exact congrArg (List.map D.label) hwalk.symm

/-- The outer face word is `u`. -/
theorem wordFrom_outer : D.toLabelledMap.wordFrom D.base = u :=
  (D.wordFrom_head D.outer_cycle).trans D.outer_word

/-- `OnFace` is equality of faces. -/
theorem onFace_iff (x d : D.map.Dart) :
    D.toLabelledMap.OnFace x d ↔ D.map.faceOf x = D.map.faceOf d := by
  rw [D.map.faceOf_eq_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have h : D.map.facePerm.SameCycle x ((D.map.facePerm ^ n) x) :=
      Equiv.Perm.sameCycle_pow_right.mpr Equiv.Perm.SameCycle.rfl
    exact h
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, hn⟩

/-- Every face other than the outer one reads a word of the symmetrization. -/
theorem wordFrom_mem_symmetrization (d : D.map.Dart)
    (hd : ¬ D.toLabelledMap.OnFace D.base d) :
    D.toLabelledMap.wordFrom d ∈ symmetrization R := by
  obtain ⟨l, hl, hhead⟩ := D.map.exists_isFaceCycle_head d
  have hne : D.map.faceOf (l.head hl.ne_nil) ≠ D.map.faceOf (D.outer.head D.outer_cycle.ne_nil) := by
    rw [hhead]
    intro h
    exact hd ((D.onFace_iff _ _).mpr h.symm)
  have hw := D.face_word l hl hne
  rw [← hhead, D.wordFrom_head hl]
  exact hw

/-- **Connectedness.** -/
theorem isConnected : D.toLabelledMap.IsConnected := by
  have hadj : ∀ x y : D.map.Dart, D.map.Adjacent x y →
      Relation.ReflTransGen (fun a b => b = D.toLabelledMap.next a ∨ b = D.toLabelledMap.opp a)
          x y ∧
        Relation.ReflTransGen
          (fun a b => b = D.toLabelledMap.next a ∨ b = D.toLabelledMap.opp a) y x := by
    intro x y h
    rcases h with h | h
    · refine ⟨?_, ?_⟩
      · rw [← h]
        exact path_opp D.toLabelledMap x
      · have e : x = D.map.alpha y := by
          rw [← h, D.map.alpha_involutive x]
        rw [e]
        exact path_opp D.toLabelledMap y
    · have hxy : D.map.facePerm (D.map.alpha x) = y := by
        show D.map.sigma (D.map.alpha (D.map.alpha x)) = y
        rw [D.map.alpha_involutive x, h]
      refine ⟨?_, ?_⟩
      · rw [← hxy]
        exact (path_opp D.toLabelledMap x).trans (path_next D.toLabelledMap _)
      · have h0 : D.map.facePerm.SameCycle (D.map.facePerm (D.map.alpha x)) (D.map.alpha x) :=
          Equiv.Perm.sameCycle_apply_left.mpr Equiv.Perm.SameCycle.rfl
        rw [hxy] at h0
        obtain ⟨n, hn⟩ := h0.exists_nat_pow_eq
        have e : x = D.toLabelledMap.opp (D.toLabelledMap.next^[n] y) := by
          show x = D.map.alpha ((D.map.facePerm ^ n) y)
          rw [hn, D.map.alpha_involutive x]
        rw [e]
        exact (path_iterate D.toLabelledMap y n).trans (path_opp D.toLabelledMap _)
  have key : ∀ x y : D.map.Dart, Relation.EqvGen D.map.Adjacent x y →
      Relation.ReflTransGen (fun a b => b = D.toLabelledMap.next a ∨ b = D.toLabelledMap.opp a)
          x y ∧
        Relation.ReflTransGen
          (fun a b => b = D.toLabelledMap.next a ∨ b = D.toLabelledMap.opp a) y x := by
    intro x y h
    induction h with
    | rel a b hab => exact hadj a b hab
    | refl a => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | symm a b _ ih => exact ⟨ih.2, ih.1⟩
    | trans a b c _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₂.2.trans ih₁.2⟩
  intro d d'
  exact (key d d' (D.map.connected_of_planar D.planar d d')).1

theorem rot_eq : D.toLabelledMap.rot = D.map.sigma := by
  funext d
  show D.map.sigma (D.map.alpha (D.map.alpha d)) = D.map.sigma d
  rw [D.map.alpha_involutive d]

/-- **Euler's formula**, counted over darts. -/
theorem isSpherical : D.toLabelledMap.IsSpherical := by
  have hv : ∀ d : D.toLabelledMap.Dart,
      D.toLabelledMap.vdeg d = Function.minimalPeriod D.map.sigma d := by
    intro d
    show Function.minimalPeriod D.toLabelledMap.rot d = _
    rw [D.rot_eq]
  have e1 : (∑ d : D.toLabelledMap.Dart, (1 : ℚ) / (D.toLabelledMap.flen d : ℚ)) =
      (D.map.faceCount : ℚ) :=
    sum_one_div_minimalPeriod D.map.facePerm
  have e2 : (∑ d : D.toLabelledMap.Dart, (1 : ℚ) / (D.toLabelledMap.vdeg d : ℚ)) =
      (D.map.vertexCount : ℚ) := by
    simp only [hv]
    exact sum_one_div_minimalPeriod D.map.sigma
  have hcard' : Fintype.card D.toLabelledMap.Dart = 2 * D.map.edgeCount := by
    rw [← Nat.card_eq_fintype_card]
    exact D.map.dartCount_eq_two_mul_edgeCount
  have hcard : (Fintype.card D.toLabelledMap.Dart : ℚ) = 2 * (D.map.edgeCount : ℚ) := by
    exact_mod_cast hcard'
  have hχ := congrArg (Int.cast : ℤ → ℚ) (D.map.euler_eq_two D.planar)
  push_cast at hχ
  unfold LabelledMap.IsSpherical
  rw [Finset.sum_add_distrib, e1, e2, hcard]
  linarith

end LetterDisc

end GroupApproximation.Full.NN07a.VK
