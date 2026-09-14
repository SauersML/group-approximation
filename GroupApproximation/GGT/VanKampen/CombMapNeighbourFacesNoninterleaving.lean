import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSides
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitMap
import GroupApproximation.Meta.AxiomGuard

/-!
# The neighbour faces of one face of a planar map do not interleave

Let `f` be a face of a planar map, read from `x₀` as `x₀, φ x₀, …, φ^{n-1} x₀` for the face
permutation `φ`.  If the faces across positions `0` and `q` are one face `a`, and the faces across
positions `r` and `s` are one face `b`, with `0 < r < q < s < n` and `a`, `b`, `f` pairwise
distinct, the map is not planar.  On the sphere the two closed curves through `f` and `a` and
through `f` and `b` would meet exactly once.

The proof merges `a` into `f` by splitting the vertex at `x₀` (`PinchSplit`), which keeps the map
planar and every dart.  After the split the edge of `φ^q x₀` has the merged face on both sides, so
it is a bridge (`AvoidEdgeStep.not_eqvGen_alpha_of_sameFace`).  Moves avoiding it still join its
two darts:
* `φ^r x₀` reaches `φ^q x₀` along `f`;
* `φ^s x₀` reaches the dart of `f` before `x₀`, then enters `a` through the split, and reaches
  `α φ^q x₀` along `a`;
* `φ^r x₀` crosses into `b`, walks along `b`, which the split does not touch, and crosses back to
  `φ^s x₀`.

* `NeighbourFaces.eqvGen_facePerm_run`: a run of face steps avoiding an edge.
* `NeighbourFaces.false_of_interleave`: the statement, with position `0` the first `a` side.
* `NeighbourFacesNoninterleavingStatement`, `neighbourFacesNoninterleaving`: the closed endpoint.

Model test (hand).  On the torus with one vertex, two edges `u`, `v` and one face, the face walk
reads `u, v, α u, α v`, and the faces across are `f, f, f, f`, so `a = b = f` and the hypotheses
fail.  The distinctness of `a`, `b` and `f` is needed: with `a = f` the pattern occurs on planar
maps, a face with an internal chord and another neighbour on both sides.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4, arXiv:math/0411039v3,
§9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace NeighbourFaces

/-- One face step that avoids the edge of `d`: reversal at another edge, then vertex rotation. -/
theorem eqvGen_facePerm_step (N : CombMap.{u}) (d u : N.Dart) (h1 : u ≠ d) (h2 : u ≠ N.alpha d) :
    Relation.EqvGen (AvoidEdgeStep N d) u (N.facePerm u) :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨h1, h2, rfl⟩))
    (Relation.EqvGen.rel _ _ (Or.inl rfl))

/-- **A run of face steps avoiding an edge.** -/
theorem eqvGen_facePerm_run (N : CombMap.{u}) (d : N.Dart) (g : ℕ → N.Dart) (m : ℕ)
    (hstep : ∀ t < m, N.facePerm (g t) = g (t + 1))
    (havoid : ∀ t < m, g t ≠ d ∧ g t ≠ N.alpha d) :
    Relation.EqvGen (AvoidEdgeStep N d) (g 0) (g m) := by
  induction m with
  | zero => exact Relation.EqvGen.refl _
  | succ m ih =>
    refine Relation.EqvGen.trans _ _ _
      (ih (fun t ht => hstep t (by omega)) (fun t ht => havoid t (by omega))) ?_
    obtain ⟨h1, h2⟩ := havoid m (by omega)
    rw [← hstep m (by omega)]
    exact eqvGen_facePerm_step N d (g m) h1 h2

theorem faceOf_pow (M : CombMap.{u}) (x : M.Dart) (j : ℕ) :
    M.faceOf ((M.facePerm ^ j) x) = M.faceOf x :=
  faceOf_facePerm_pow M x j

theorem facePerm_pow_succ_apply (M : CombMap.{u}) (x : M.Dart) (i : ℕ) :
    M.facePerm ((M.facePerm ^ i) x) = (M.facePerm ^ (i + 1)) x := by
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem ne_of_faceOf_ne {M : CombMap.{u}} {a b : M.Dart} (h : M.faceOf a ≠ M.faceOf b) : a ≠ b :=
  fun hab => h (by rw [hab])

/-- **Interleaving neighbour faces contradict planarity**, with position `0` the first side along
`a`. -/
theorem false_of_interleave (M : CombMap.{u}) (hM : M.IsPlanar) (x₀ : M.Dart) (n : ℕ)
    (hcyc : (M.facePerm ^ n) x₀ = x₀)
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) x₀ = (M.facePerm ^ b) x₀ → a = b)
    {r q s : ℕ} (hr : 0 < r) (hrq : r < q) (hqs : q < s) (hsn : s < n)
    (hA : M.faceOf (M.alpha x₀) = M.faceOf (M.alpha ((M.facePerm ^ q) x₀)))
    (hB : M.faceOf (M.alpha ((M.facePerm ^ r) x₀)) = M.faceOf (M.alpha ((M.facePerm ^ s) x₀)))
    (hAB : M.faceOf (M.alpha x₀) ≠ M.faceOf (M.alpha ((M.facePerm ^ r) x₀)))
    (hAf : M.faceOf (M.alpha x₀) ≠ M.faceOf x₀)
    (hBf : M.faceOf (M.alpha ((M.facePerm ^ r) x₀)) ≠ M.faceOf x₀) : False := by
  classical
  -- positions along `f`
  set X : ℕ → M.Dart := fun i => (M.facePerm ^ i) x₀ with hX
  have hXf : ∀ i, M.faceOf (X i) = M.faceOf x₀ := fun i => faceOf_pow M x₀ i
  have hXstep : ∀ i, M.facePerm (X i) = X (i + 1) := fun i => facePerm_pow_succ_apply M x₀ i
  have hXne : ∀ i j, i < n → j < n → i ≠ j → X i ≠ X j :=
    fun i j hi hj hij h => hij (hinj i j hi hj h)
  have hX0 : X 0 = x₀ := by simp [hX]
  -- the dart `z` of `f` before `x₀`, and the split darts
  set z := X (n - 1) with hzdef
  have hz : M.facePerm z = x₀ := by
    rw [hzdef, hXstep, show n - 1 + 1 = n by omega]
    exact hcyc
  set x := M.alpha z with hxdef
  have hax : M.alpha x = z := M.alpha_involutive z
  have hsig : M.sigma x = x₀ := by
    have h : M.facePerm (M.alpha x) = M.sigma x := by
      show M.sigma (M.alpha (M.alpha x)) = M.sigma x
      rw [M.alpha_involutive]
    rw [← h, hax, hz]
  have hxy : M.sigma.SameCycle x x₀ := ⟨1, by rw [zpow_one]; exact hsig⟩
  have hface_ne : M.faceOf (M.alpha x) ≠ M.faceOf (M.alpha x₀) := by
    rw [hax, hzdef, hXf]
    exact fun h => hAf h.symm
  let C : PinchSplit.Cycles M x x₀ := (PinchSplit.exists_cycles hface_ne).some
  let M1 := PinchSplit.toCombMap M x x₀
  have hM1 : M1.IsPlanar := C.planar hM hxy
  -- face permutation of the split away from the pinch
  have hfp : ∀ d, d ≠ z → d ≠ M.alpha x₀ → M1.facePerm d = M.facePerm d := fun d h1 h2 =>
    PinchSplit.facePerm_apply_of_ne M x x₀ (by rw [hax]; exact h1) h2
  set dq := X q with hdq
  -- faces of `f` and `a` merge
  have hmerged_f : ∀ e, M.faceOf e = M.faceOf x₀ → M1.faceOf e = M1.faceOf (M.alpha x) := by
    intro e he
    exact (C.faceOf_merged_iff e).mpr (Or.inl (by rw [he, hax, hzdef, hXf]))
  have hmerged_a : ∀ e, M.faceOf e = M.faceOf (M.alpha x₀) →
      M1.faceOf e = M1.faceOf (M.alpha x) :=
    fun e he => (C.faceOf_merged_iff e).mpr (Or.inr he)
  have hface1 : M1.faceOf dq = M1.faceOf (M1.alpha dq) :=
    (hmerged_f dq (hXf q)).trans (hmerged_a (M.alpha dq) hA.symm).symm
  have hbridge := AvoidEdgeStep.not_eqvGen_alpha_of_sameFace M1 hM1 dq hface1
  -- inequalities by faces
  have hfa : ∀ i, X i ≠ M.alpha dq := fun i =>
    ne_of_faceOf_ne (by rw [hXf, ← hA]; exact fun h => hAf h.symm)
  have hfa0 : ∀ i, X i ≠ M.alpha x₀ := fun i =>
    ne_of_faceOf_ne (by rw [hXf]; exact fun h => hAf h.symm)
  -- (a) `X r` reaches `X q` along `f`
  have ha : Relation.EqvGen (AvoidEdgeStep M1 dq) (X r) dq := by
    have h := eqvGen_facePerm_run M1 dq (fun t => X (r + t)) (q - r)
      (fun t ht => by
        show M1.facePerm (X (r + t)) = X (r + (t + 1))
        rw [hfp _ (hXne _ _ (by omega) (by omega) (by omega)) (hfa0 _), hXstep, Nat.add_assoc])
      (fun t ht => ⟨hXne _ _ (by omega) (by omega) (by omega), hfa _⟩)
    simpa [show r + (q - r) = q by omega] using h
  -- the walk of `a` from `α x₀`, up to `α (X q)`
  set W : ℕ → M.Dart := fun j => (M.facePerm ^ j) (M.alpha x₀) with hW
  have hWf : ∀ j, M.faceOf (W j) = M.faceOf (M.alpha x₀) := fun j => faceOf_pow M _ j
  have hWstep : ∀ j, M.facePerm (W j) = W (j + 1) := fun j => facePerm_pow_succ_apply M _ j
  have hex : ∃ j : ℕ, W j = M.alpha dq := ((M.faceOf_eq_iff _ _).mp hA).exists_nat_pow_eq
  set jq := Nat.find hex with hjqdef
  have hjq : W jq = M.alpha dq := Nat.find_spec hex
  have hmin : ∀ t < jq, W t ≠ M.alpha dq := fun t ht => Nat.find_min hex ht
  have hq0 : x₀ ≠ dq := by
    rw [← hX0]
    exact hXne 0 q (by omega) (by omega) (by omega)
  have hjq1 : 1 ≤ jq := by
    by_contra h0
    have h00 : jq = 0 := by omega
    rw [h00] at hjq
    exact hq0 (by
      have h := congrArg M.alpha hjq
      simpa [hW, M.alpha_involutive] using h)
  have hWne0 : ∀ t, 1 ≤ t → t < jq → W t ≠ M.alpha x₀ := by
    intro t ht1 htq hWt
    refine hmin (jq - t) (by omega) ?_
    rw [← hjq]
    show (M.facePerm ^ (jq - t)) (M.alpha x₀) = (M.facePerm ^ jq) (M.alpha x₀)
    have e : (M.facePerm ^ jq) (M.alpha x₀) = (M.facePerm ^ (jq - t)) (W t) := by
      show (M.facePerm ^ jq) (M.alpha x₀) =
        (M.facePerm ^ (jq - t)) ((M.facePerm ^ t) (M.alpha x₀))
      rw [facePerm_pow_apply_pow, show jq - t + t = jq by omega]
    rw [e, hWt]
  -- (b) `X s` reaches `α (X q)`
  have hb1 : Relation.EqvGen (AvoidEdgeStep M1 dq) (X s) z := by
    have h := eqvGen_facePerm_run M1 dq (fun t => X (s + t)) (n - 1 - s)
      (fun t ht => by
        show M1.facePerm (X (s + t)) = X (s + (t + 1))
        rw [hfp _ (hXne _ _ (by omega) (by omega) (by omega)) (hfa0 _), hXstep, Nat.add_assoc])
      (fun t ht => ⟨hXne _ _ (by omega) (by omega) (by omega), hfa _⟩)
    simpa [hzdef, show s + (n - 1 - s) = n - 1 by omega] using h
  have hb2 : Relation.EqvGen (AvoidEdgeStep M1 dq) z (W 1) := by
    have h := eqvGen_facePerm_step M1 dq z (hXne _ _ (by omega) (by omega) (by omega)) (hfa _)
    have e : M1.facePerm z = W 1 := by
      have h' := PinchSplit.facePerm_apply_alpha_left M x x₀
      rw [hax] at h'
      rw [h']
      simp [hW]
    rwa [e] at h
  have hb3 : Relation.EqvGen (AvoidEdgeStep M1 dq) (W 1) (M.alpha dq) := by
    have h := eqvGen_facePerm_run M1 dq (fun t => W (1 + t)) (jq - 1)
      (fun t ht => by
        show M1.facePerm (W (1 + t)) = W (1 + (t + 1))
        rw [hfp _ (ne_of_faceOf_ne (by rw [hWf, hzdef, hXf]; exact hAf))
          (hWne0 _ (by omega) (by omega)), hWstep, Nat.add_assoc])
      (fun t ht => ⟨ne_of_faceOf_ne (by rw [hWf, hdq, hXf]; exact hAf),
        hmin _ (by omega)⟩)
    simpa [show 1 + (jq - 1) = jq by omega, hjq] using h
  -- (c) `X r` reaches `X s` through `b`
  have hBa : M.faceOf (M.alpha (X r)) ≠ M.faceOf (M.alpha x) := by
    rw [hax, hzdef, hXf]; exact hBf
  have hBb : M.faceOf (M.alpha (X r)) ≠ M.faceOf (M.alpha x₀) := fun h => hAB h.symm
  have hnotmerged : ∀ e, M.faceOf e = M.faceOf (M.alpha (X r)) →
      M1.faceOf e ≠ M1.faceOf (M.alpha x) := by
    intro e he h
    rcases (C.faceOf_merged_iff e).mp h with h' | h'
    · exact hBa (he ▸ h')
    · exact hBb (he ▸ h')
  have hc : Relation.EqvGen (AvoidEdgeStep M1 dq) (X r) (X s) := by
    have hcross1 : Relation.EqvGen (AvoidEdgeStep M1 dq) (X r) (M.alpha (X r)) :=
      Relation.EqvGen.rel _ _
        (Or.inr ⟨hXne _ _ (by omega) (by omega) (by omega), hfa _, rfl⟩)
    have hfaceB1 : M1.faceOf (M.alpha (X r)) = M1.faceOf (M.alpha (X s)) :=
      ((PinchSplit.faceOf_eq_iff_of_avoid M x x₀ hBa hBb (M.alpha (X s))).mpr hB.symm).symm
    have hwalk : Relation.EqvGen (AvoidEdgeStep M1 dq) (M.alpha (X r)) (M.alpha (X s)) :=
      AvoidEdgeStep.eqvGen_of_faceOf_eq (M := M1) hfaceB1
        (fun h => hnotmerged _ rfl (h.symm.trans (hmerged_f dq (hXf q))))
        (fun h => hnotmerged _ rfl (h.symm.trans (hmerged_a _ hA.symm)))
    have hsB : M.faceOf (M.alpha (X s)) = M.faceOf (M.alpha (X r)) := hB.symm
    have hcross2 : Relation.EqvGen (AvoidEdgeStep M1 dq) (M.alpha (X s)) (X s) := by
      refine Relation.EqvGen.rel _ _ (Or.inr ⟨?_, ?_, M.alpha_involutive _⟩)
      · exact ne_of_faceOf_ne (by rw [hsB, hdq, hXf]; exact hBf)
      · exact ne_of_faceOf_ne (by rw [hsB, ← hA]; exact hBb)
    exact (hcross1.trans _ _ _ hwalk).trans _ _ _ hcross2
  exact hbridge ((((Relation.EqvGen.symm _ _ ha).trans _ _ _ hc).trans _ _ _ hb1).trans _ _ _
    (hb2.trans _ _ _ hb3))

end NeighbourFaces

/-- **The neighbour faces of one face of a planar map do not interleave.** -/
def NeighbourFacesNoninterleavingStatement : Prop :=
  ∀ (M : CombMap.{u}), M.IsPlanar → ∀ (x₀ : M.Dart) (n : ℕ), (M.facePerm ^ n) x₀ = x₀ →
    (∀ a b, a < n → b < n → (M.facePerm ^ a) x₀ = (M.facePerm ^ b) x₀ → a = b) →
    ∀ r q s : ℕ, 0 < r → r < q → q < s → s < n →
      M.faceOf (M.alpha x₀) = M.faceOf (M.alpha ((M.facePerm ^ q) x₀)) →
      M.faceOf (M.alpha ((M.facePerm ^ r) x₀)) = M.faceOf (M.alpha ((M.facePerm ^ s) x₀)) →
      M.faceOf (M.alpha x₀) ≠ M.faceOf (M.alpha ((M.facePerm ^ r) x₀)) →
      M.faceOf (M.alpha x₀) ≠ M.faceOf x₀ →
      M.faceOf (M.alpha ((M.facePerm ^ r) x₀)) ≠ M.faceOf x₀ → False

theorem neighbourFacesNoninterleaving : NeighbourFacesNoninterleavingStatement.{u} := by
  intro M hM x₀ n hcyc hinj r q s hr hrq hqs hsn hA hB hAB hAf hBf
  exact NeighbourFaces.false_of_interleave M hM x₀ n hcyc hinj hr hrq hqs hsn hA hB hAB hAf hBf

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.NeighbourFaces.eqvGen_facePerm_run
#audit_axioms GroupApproximation.GGT.VanKampen.NeighbourFaces.false_of_interleave
#audit_closed_axioms GroupApproximation.GGT.VanKampen.neighbourFacesNoninterleaving
