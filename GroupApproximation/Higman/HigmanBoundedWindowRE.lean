import GroupApproximation.Higman.HigmanPrimitiveRecursiveRunSemantics
import GroupApproximation.Higman.TraceRelationRE
import GroupApproximation.Higman.REPredNormalForm

/-!
# The unconditional bounded-window theorem

Integer inputs are represented by differences of two natural auxiliary
coordinates.  The signed input itself is retained, while all natural codes,
the search witness, and the Boolean output are existentially forgotten.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- Place `addGraph` as `positive = signed + negative`. -/
def signedInputCoord (n : ℕ) (i : Fin n) (j : ℕ) : ℤ :=
  if j = 0 then (i.val : ℤ)
  else if j = 1 then ((n + 2 * i.val + 1 : ℕ) : ℤ)
  else ((n + 2 * i.val : ℕ) : ℤ)

/-- Place a natural graph in the contiguous auxiliary interval beginning at
`n`.  Its `2n+1` inputs are the positive/negative pairs and search witness;
its last coordinate is the Boolean output. -/
def signedSearchCoord (n : ℕ) (j : ℕ) : ℤ := ((n + j : ℕ) : ℤ)

noncomputable def signedSearchAssembly (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ) : Set E :=
  (⋂ i ∈ (Finset.univ : Finset (Fin n)),
      placeAt 3 (signedInputCoord n i) addGraph) ∩
    placeAt (2 * n + 2) (signedSearchCoord n) (natGraph Q) ∩
      pinAt ((n + (2 * n + 1) : ℕ) : ℤ) 1

noncomputable def signedSearchProjection (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ) : Set E :=
  freeAux (2 * n + 2) n (signedSearchAssembly n Q) ∩ windowSupport n

theorem higmanGenerated_signedSearchProjection (n : ℕ)
    (Q : List.Vector ℕ (2 * n + 1) → ℕ)
    (hQ : HigmanGenerated (natGraph Q)) :
    HigmanGenerated (signedSearchProjection n Q) := by
  classical
  unfold signedSearchProjection signedSearchAssembly
  refine HigmanGenerated.inter (higmanGenerated_freeAux (2 * n + 2) n ?_)
    (higmanGenerated_windowSupport n)
  exact HigmanGenerated.inter
    (HigmanGenerated.inter
      (higmanGenerated_biInter Finset.univ
        (fun i : Fin n => placeAt 3 (signedInputCoord n i) addGraph)
        (fun i _ => higmanGenerated_placeAt 3 (signedInputCoord n i) addGraph
          higmanGenerated_addGraph_unconditional))
      (higmanGenerated_placeAt (2 * n + 2) (signedSearchCoord n)
        (natGraph Q) hQ))
    (higmanGenerated_pinAt ((n + (2 * n + 1) : ℕ) : ℤ) 1)

/-- Decode the positive/negative pairs supplied to the natural search graph. -/
def signedSearchTuple (n : ℕ) (a : List.Vector ℕ (2 * n + 1)) : Fin n → ℤ :=
  fun i => natDiffZ (a.get ⟨2 * i.val, by omega⟩)
    (a.get ⟨2 * i.val + 1, by omega⟩)

def signedSearchWitness (n : ℕ) (a : List.Vector ℕ (2 * n + 1)) : ℕ :=
  a.get ⟨2 * n, by omega⟩

/-- The Boolean matrix, encoded as the natural output `0` or `1`. -/
def signedSearchFn (n : ℕ) (search : (Fin n → ℤ) → ℕ → Bool)
    (a : List.Vector ℕ (2 * n + 1)) : ℕ :=
  Encodable.encode (search (signedSearchTuple n a) (signedSearchWitness n a))

theorem primrec'_signedSearchFn (n : ℕ) (search : (Fin n → ℤ) → ℕ → Bool)
    (hsearch : Primrec₂ search) : Nat.Primrec' (signedSearchFn n search) := by
  have htuple : Primrec (signedSearchTuple n) := by
    have hi : Primrec₂ fun (i : Fin n) (a : List.Vector ℕ (2 * n + 1)) =>
        natDiffZ (a.get ⟨2 * i.val, by omega⟩)
          (a.get ⟨2 * i.val + 1, by omega⟩) :=
      Primrec.fin_curry₁.2 fun i => primrec_natDiffZ.comp
        (Primrec.vector_get.comp Primrec.id
          (Primrec.const (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1))))
        (Primrec.vector_get.comp Primrec.id
          (Primrec.const (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n + 1))))
    exact Primrec.fin_curry.2 (hi.comp Primrec.snd Primrec.fst)
  have hwitness : Primrec (signedSearchWitness n) :=
    Primrec.vector_get.comp Primrec.id
      (Primrec.const (⟨2 * n, by omega⟩ : Fin (2 * n + 1)))
  have hb : Primrec fun a : List.Vector ℕ (2 * n + 1) =>
      search (signedSearchTuple n a) (signedSearchWitness n a) :=
    hsearch.comp htuple hwitness
  exact Nat.Primrec'.of_prim (Primrec.encode.comp hb)

theorem higmanGenerated_signedSearch (n : ℕ)
    (search : (Fin n → ℤ) → ℕ → Bool) (hsearch : Primrec₂ search) :
    HigmanGenerated (signedSearchProjection n (signedSearchFn n search)) :=
  higmanGenerated_signedSearchProjection n _
    (higmanGenerated_natGraph_of_primrec' (primrec'_signedSearchFn n search hsearch))

private theorem finsupp_sum_apply {α : Type*} [Fintype α]
    (u : α → E) (j : ℤ) : (∑ i, u i) j = ∑ i, u i j := by
  classical
  change (Finset.univ.sum u) j = Finset.univ.sum fun i => u i j
  induction (Finset.univ : Finset α) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Finsupp.add_apply]

private noncomputable def signedWide {n : ℕ} (f : E) (k : ℕ) : E :=
  (((f + ∑ i : Fin n,
      Finsupp.single ((n + 2 * i.val : ℕ) : ℤ) (zpos (f (i.val : ℤ)) : ℤ)) +
    ∑ i : Fin n,
      Finsupp.single ((n + 2 * i.val + 1 : ℕ) : ℤ) (zneg (f (i.val : ℤ)) : ℤ)) +
    Finsupp.single ((n + 2 * n : ℕ) : ℤ) (k : ℤ)) +
    Finsupp.single ((n + 2 * n + 1 : ℕ) : ℤ) 1

private theorem signedWide_old {n : ℕ} (f : E) (k : ℕ) (j : ℕ) (hj : j < n) :
    signedWide (n := n) f k (j : ℤ) = f (j : ℤ) := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hp : (∑ i : Fin n, if ((n + 2 * i.val : ℕ) : ℤ) = (j : ℤ)
      then (zpos (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  have hn : (∑ i : Fin n, if ((n + 2 * i.val + 1 : ℕ) : ℤ) = (j : ℤ)
      then (zneg (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  rw [hp, hn]
  split_ifs <;> omega

private theorem signedWide_pos {n : ℕ} (f : E) (k : ℕ) (i : Fin n)
    (hf : f ∈ windowSupport n) :
    signedWide (n := n) f k ((n + 2 * i.val : ℕ) : ℤ) =
      (zpos (f (i.val : ℤ)) : ℤ) := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hf0 := ((mem_windowSupport_iff n f).mp hf).2
    (((n + 2 * i.val : ℕ) : ℤ)) (by push_cast; omega)
  rw [hf0]
  simp only [zero_add]
  have hp : (∑ j : Fin n, if ((n + 2 * j.val : ℕ) : ℤ) =
      ((n + 2 * i.val : ℕ) : ℤ) then (zpos (f (j.val : ℤ)) : ℤ) else 0) =
      (zpos (f (i.val : ℤ)) : ℤ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg]
      intro h
      have hnat : n + 2 * j.val = n + 2 * i.val := by exact_mod_cast h
      exact hji (Fin.ext (by omega))
    · simp
  rw [hp]
  have hn : (∑ j : Fin n, if ((n + 2 * j.val + 1 : ℕ) : ℤ) =
      ((n + 2 * i.val : ℕ) : ℤ) then (zneg (f (j.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]
  rw [hn]
  split_ifs <;> omega

private theorem signedWide_neg {n : ℕ} (f : E) (k : ℕ) (i : Fin n)
    (hf : f ∈ windowSupport n) :
    signedWide (n := n) f k ((n + 2 * i.val + 1 : ℕ) : ℤ) =
      (zneg (f (i.val : ℤ)) : ℤ) := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hf0 := ((mem_windowSupport_iff n f).mp hf).2
    (((n + 2 * i.val + 1 : ℕ) : ℤ)) (by push_cast; omega)
  rw [hf0]
  have hp : (∑ j : Fin n, if ((n + 2 * j.val : ℕ) : ℤ) =
      ((n + 2 * i.val + 1 : ℕ) : ℤ) then (zpos (f (j.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]
  rw [hp, zero_add]
  have hn : (∑ j : Fin n, if ((n + 2 * j.val + 1 : ℕ) : ℤ) =
      ((n + 2 * i.val + 1 : ℕ) : ℤ) then (zneg (f (j.val : ℤ)) : ℤ) else 0) =
      (zneg (f (i.val : ℤ)) : ℤ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg]
      intro h
      have hnat : n + 2 * j.val + 1 = n + 2 * i.val + 1 := by exact_mod_cast h
      exact hji (Fin.ext (by omega))
    · simp
  rw [hn]
  split_ifs <;> omega

private theorem signedWide_witness {n : ℕ} (f : E) (k : ℕ)
    (hf : f ∈ windowSupport n) :
    signedWide (n := n) f k ((n + 2 * n : ℕ) : ℤ) = (k : ℤ) := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hf0 := ((mem_windowSupport_iff n f).mp hf).2
    (((n + 2 * n : ℕ) : ℤ)) (by push_cast; omega)
  rw [hf0]
  have hp : (∑ i : Fin n, if ((n + 2 * i.val : ℕ) : ℤ) =
      ((n + 2 * n : ℕ) : ℤ) then (zpos (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  have hn : (∑ i : Fin n, if ((n + 2 * i.val + 1 : ℕ) : ℤ) =
      ((n + 2 * n : ℕ) : ℤ) then (zneg (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  rw [hp, hn]
  simp

private theorem signedWide_output {n : ℕ} (f : E) (k : ℕ)
    (hf : f ∈ windowSupport n) :
    signedWide (n := n) f k ((n + 2 * n + 1 : ℕ) : ℤ) = 1 := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hf0 := ((mem_windowSupport_iff n f).mp hf).2
    (((n + 2 * n + 1 : ℕ) : ℤ)) (by push_cast; omega)
  rw [hf0]
  have hp : (∑ i : Fin n, if ((n + 2 * i.val : ℕ) : ℤ) =
      ((n + 2 * n + 1 : ℕ) : ℤ) then (zpos (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  have hn : (∑ i : Fin n, if ((n + 2 * i.val + 1 : ℕ) : ℤ) =
      ((n + 2 * n + 1 : ℕ) : ℤ) then (zneg (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  rw [hp, hn]
  simp

private theorem signedWide_off {n : ℕ} (f : E) (k : ℕ) (j : ℤ)
    (hj : ∀ a : ℕ, a < 2 * n + 2 → j ≠ ((n + a : ℕ) : ℤ)) :
    signedWide (n := n) f k j = f j := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hp : (∑ i : Fin n, if ((n + 2 * i.val : ℕ) : ℤ) = j
      then (zpos (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (hj (2 * i.val) (by omega)).symm]
  have hn : (∑ i : Fin n, if ((n + 2 * i.val + 1 : ℕ) : ℤ) = j
      then (zneg (f (i.val : ℤ)) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with h
    · exact (hj (2 * i.val + 1) (by omega) (by push_cast at h ⊢; omega)).elim
    · rfl
  rw [hp, hn]
  have hfirst : (n : ℤ) + 2 * (n : ℤ) ≠ j := by
    intro h
    exact hj (2 * n) (by omega) (by push_cast; omega)
  have hsecond : (n : ℤ) + 2 * (n : ℤ) + 1 ≠ j := by
    intro h
    exact hj (2 * n + 1) (by omega) (by push_cast; omega)
  have hfirst' : (((n + 2 * n : ℕ) : ℤ)) ≠ j := by
    intro h
    exact hfirst (by push_cast at h ⊢; omega)
  have hsecond' : (((n + 2 * n + 1 : ℕ) : ℤ)) ≠ j := by
    intro h
    exact hsecond (by push_cast at h ⊢; omega)
  rw [if_neg hfirst', if_neg hsecond']
  simp

private theorem signedWide_aux_nonneg {n : ℕ} (f : E) (k a : ℕ)
    (hf : f ∈ windowSupport n) :
    0 ≤ signedWide (n := n) f k ((n + a : ℕ) : ℤ) := by
  classical
  simp only [signedWide, Finsupp.add_apply, finsupp_sum_apply, Finsupp.single_apply]
  have hf0 := ((mem_windowSupport_iff n f).mp hf).2
    (((n + a : ℕ) : ℤ)) (by push_cast; omega)
  rw [hf0]
  positivity

@[simp] theorem signedInputCoord_zero (n : ℕ) (i : Fin n) :
    signedInputCoord n i 0 = (i.val : ℤ) := by simp [signedInputCoord]

@[simp] theorem signedInputCoord_one (n : ℕ) (i : Fin n) :
    signedInputCoord n i 1 = ((n + 2 * i.val + 1 : ℕ) : ℤ) := by
  simp [signedInputCoord]

@[simp] theorem signedInputCoord_two (n : ℕ) (i : Fin n) :
    signedInputCoord n i 2 = ((n + 2 * i.val : ℕ) : ℤ) := by
  simp [signedInputCoord]

theorem signedSearchProjection_eq (n : ℕ)
    (search : (Fin n → ℤ) → ℕ → Bool) :
    signedSearchProjection n (signedSearchFn n search) =
      winRel n (fun x => ∃ k, search x k = true) := by
  classical
  ext f
  constructor
  · rintro ⟨⟨g, ⟨⟨hadds, hgraph⟩, hpin⟩, hfg⟩, hwindow⟩
    refine ⟨hwindow, ?_⟩
    obtain ⟨w, hw, hplace⟩ := hgraph
    let a : List.Vector ℕ (2 * n + 1) :=
      List.Vector.ofFn fun j => (w (j.val : ℤ)).toNat
    refine ⟨a.get ⟨2 * n, by omega⟩, ?_⟩
    have htuple : signedSearchTuple n a = winVars n f := by
      funext i
      obtain ⟨r, hr, hrplace⟩ :=
        Set.mem_iInter₂.mp hadds i (Finset.mem_univ i)
      have h0 := hrplace 0 (by omega)
      have h1 := hrplace 1 (by omega)
      have h2 := hrplace 2 (by omega)
      simp only [signedInputCoord_zero, signedInputCoord_one,
        signedInputCoord_two] at h0 h1 h2
      have hkeep : f (i.val : ℤ) = g (i.val : ℤ) :=
        hfg (i.val : ℤ) (by intro j hj; push_cast; omega)
      have hp := hplace (2 * i.val) (by omega)
      have hq := hplace (2 * i.val + 1) (by omega)
      simp only [signedSearchCoord] at hp hq
      have hpnon := hw.2.1 (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1))
      have hqnon := hw.2.1 (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n + 1))
      change natDiffZ (a.get ⟨2 * i.val, by omega⟩)
        (a.get ⟨2 * i.val + 1, by omega⟩) = f (i.val : ℤ)
      rw [natDiffZ_eq]
      simp only [a, List.Vector.get_ofFn, Int.toNat_of_nonneg hpnon,
        Int.toNat_of_nonneg hqnon]
      have hq' : g ((n + 2 * i.val + 1 : ℕ) : ℤ) =
          w ((2 * i.val + 1 : ℕ) : ℤ) := by
        convert hq using 1
        push_cast
        ring
      rw [← hp, ← hq']
      calc
        g ((n + 2 * i.val : ℕ) : ℤ) - g ((n + 2 * i.val + 1 : ℕ) : ℤ) =
            r 2 - r 1 := congrArg₂ (· - ·) h2 h1
        _ = r 0 := by rw [hr.2.2]; ring
        _ = f (i.val : ℤ) := by simpa using h0.symm.trans hkeep.symm
    have hout := hplace (2 * n + 1) (by omega)
    simp only [signedSearchCoord] at hout
    have hnatout : (signedSearchFn n search a : ℤ) = 1 := by
      rw [← hw.2.2]
      exact hout.symm.trans hpin
    have hwit : signedSearchWitness n a = a.get ⟨2 * n, by omega⟩ := rfl
    unfold signedSearchFn at hnatout
    rw [htuple, hwit] at hnatout
    cases hb : search (winVars n f) (a.get ⟨2 * n, by omega⟩) <;>
      simp [hb] at hnatout ⊢
  · rintro ⟨hwindow, k, hk⟩
    let g := signedWide (n := n) f k
    let a : List.Vector ℕ (2 * n + 1) :=
      List.Vector.ofFn fun j => (g ((n + j.val : ℕ) : ℤ)).toNat
    have haTuple : signedSearchTuple n a = winVars n f := by
      funext i
      change natDiffZ (a.get ⟨2 * i.val, by omega⟩)
        (a.get ⟨2 * i.val + 1, by omega⟩) = f (i.val : ℤ)
      rw [natDiffZ_eq]
      simp only [a, List.Vector.get_ofFn]
      rw [Int.toNat_of_nonneg (signedWide_aux_nonneg f k (2 * i.val) hwindow),
        Int.toNat_of_nonneg (signedWide_aux_nonneg f k (2 * i.val + 1) hwindow)]
      have hp := signedWide_pos f k i hwindow
      have hq := signedWide_neg f k i hwindow
      have hz : signedWide (n := n) f k ((n + 2 * i.val : ℕ) : ℤ) -
          signedWide (n := n) f k ((n + 2 * i.val + 1 : ℕ) : ℤ) =
          f (i.val : ℤ) := by rw [hp, hq, zpos_sub_zneg]
      convert hz using 1
      congr 1
    have haWitness : signedSearchWitness n a = k := by
      unfold signedSearchWitness
      simp only [a, List.Vector.get_ofFn]
      change (signedWide (n := n) f k ((n + 2 * n : ℕ) : ℤ)).toNat = k
      have hw := congrArg Int.toNat (signedWide_witness f k hwindow)
      simpa using hw
    have haQ : signedSearchFn n search a = 1 := by
      simp [signedSearchFn, haTuple, haWitness, hk]
    refine ⟨⟨g, ?_, fun j hj => (signedWide_off f k j hj).symm⟩, hwindow⟩
    refine ⟨?_, ?_⟩
    · constructor
      · refine Set.mem_iInter₂.mpr fun i _ => ?_
        let r : E := Finsupp.single 0 (f (i.val : ℤ)) +
          Finsupp.single 1 (zneg (f (i.val : ℤ)) : ℤ) +
          Finsupp.single 2 (zpos (f (i.val : ℤ)) : ℤ)
        refine ⟨r, ?_, fun j hj => ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro t ht
            simp only [r, Finsupp.add_apply, Finsupp.single_apply]
            split_ifs <;> omega
          · intro t ht
            simp only [r, Finsupp.add_apply, Finsupp.single_apply]
            split_ifs <;> omega
          · simp only [r, Finsupp.add_apply, Finsupp.single_apply]
            simp
            have hz := zpos_sub_zneg (f (i.val : ℤ))
            omega
        · have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases hj3 with rfl | rfl | rfl
          · dsimp only [g]
            simpa [r] using signedWide_old f k i.val i.isLt
          · dsimp only [g]
            simpa [r] using signedWide_neg f k i hwindow
          · dsimp only [g]
            simpa [r] using signedWide_pos f k i hwindow
      · refine ⟨natGraphSeq (signedSearchFn n search) a,
          natGraphSeq_mem (signedSearchFn n search) a, fun j hj => ?_⟩
        by_cases hin : j < 2 * n + 1
        · rw [natGraphSeq_input _ a ⟨j, hin⟩]
          simp only [signedSearchCoord, a, List.Vector.get_ofFn]
          rw [Int.toNat_of_nonneg (signedWide_aux_nonneg f k j hwindow)]
        · have hjlast : j = 2 * n + 1 := by omega
          subst j
          rw [natGraphSeq_output, haQ]
          dsimp only [signedSearchCoord, g]
          convert signedWide_output f k hwindow using 1
          · push_cast
            ring
          · norm_num
    · change g (((n + (2 * n + 1) : ℕ) : ℤ)) = 1
      dsimp only [g]
      convert signedWide_output f k hwindow using 1
      push_cast
      ring

end Seq
end Higman
end GroupApproximation
