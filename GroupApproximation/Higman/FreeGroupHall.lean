import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.ProfiniteClosure

/-!
# Marshall Hall separation for finitely generated free subgroups

The finite action below is the coset-graph proof of Hall's theorem.  For a
finitely generated subgroup `H ≤ FreeGroup α` and `w ∉ H`, retain only the
finitely many right cosets visited while reading chosen generators of `H`
and `w`.  Right multiplication by each free generator is then a partial
bijection of this finite set.  Completing the complements arbitrarily gives
a finite permutation action.  Every chosen generator fixes the base coset,
whereas `w` moves it.

Using actual cosets as vertices means all Stallings folds are already built
into the construction.  No finiteness assumption on the alphabet is needed.
-/

namespace GroupApproximation
namespace FreeGroupHall

open scoped Classical

variable {α : Type*}

/-- The group element represented by one signed free letter. -/
def letterValue (x : α × Bool) : FreeGroup α :=
  bif x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹

theorem mk_eq_wordProd (L : List (α × Bool)) :
    FreeGroup.mk L = (L.map letterValue).prod := by
  calc
    FreeGroup.mk L = (MonoidHom.id (FreeGroup α)) (FreeGroup.mk L) := rfl
    _ = (FreeGroup.lift FreeGroup.of) (FreeGroup.mk L) :=
      FreeGroup.lift_unique (MonoidHom.id (FreeGroup α)) (fun _ ↦ rfl)
    _ = (L.map letterValue).prod := by
      rw [FreeGroup.lift_mk]
      rfl

theorem drop_map_eq {A B : Type*} (f : A → B) (L : List A) (k : ℕ) :
    (L.map f).drop k = (L.drop k).map f := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
      cases L with
      | nil => rfl
      | cons x L => exact ih L

theorem mk_drop_succ (L : List (α × Bool)) (k : ℕ) (hk : k < L.length) :
    FreeGroup.mk (L.drop (k + 1)) =
      (letterValue L[k])⁻¹ * FreeGroup.mk (L.drop k) := by
  rw [mk_eq_wordProd, mk_eq_wordProd]
  have hp := List.prod_drop_succ (L.map letterValue) k (by simpa)
  rw [List.getElem_map] at hp
  rw [← drop_map_eq, ← drop_map_eq]
  exact hp

abbrev Coset (H : Subgroup (FreeGroup α)) :=
  Quotient (QuotientGroup.rightRel H)

/-- Right multiplication by `g⁻¹` on right cosets.  The inverse is chosen so
that `g ↦ cosetStep g` is a left action, hence a homomorphism to
permutations. -/
noncomputable def cosetStep (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) : Coset H → Coset H :=
  Quotient.map (fun x ↦ x * g⁻¹) (by
    intro x y hxy
    apply QuotientGroup.rightRel_apply.mpr
    have hxy' := QuotientGroup.rightRel_apply.mp hxy
    have heq : (y * g⁻¹) * (x * g⁻¹)⁻¹ = y * x⁻¹ := by group
    rw [heq]
    exact hxy')

@[simp] theorem cosetStep_mk (H : Subgroup (FreeGroup α))
    (g x : FreeGroup α) :
    cosetStep H g (Quotient.mk _ x) = Quotient.mk _ (x * g⁻¹) := rfl

theorem cosetStep_mul (H : Subgroup (FreeGroup α))
    (g h : FreeGroup α) (x : Coset H) :
    cosetStep H (g * h) x = cosetStep H g (cosetStep H h x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
      group

@[simp] theorem cosetStep_one (H : Subgroup (FreeGroup α))
    (x : Coset H) : cosetStep H 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
      apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
      group

@[simp] theorem cosetStep_inv_cosetStep (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) (x : Coset H) :
    cosetStep H g⁻¹ (cosetStep H g x) = x := by
  rw [← cosetStep_mul H g⁻¹ g x]
  simp

@[simp] theorem cosetStep_cosetStep_inv (H : Subgroup (FreeGroup α))
    (g : FreeGroup α) (x : Coset H) :
    cosetStep H g (cosetStep H g⁻¹ x) = x := by
  rw [← cosetStep_mul H g g⁻¹ x]
  simp

/-- The coset reached after the suffix beginning at `k` has been read. -/
noncomputable def suffixCoset (H : Subgroup (FreeGroup α))
    (L : List (α × Bool)) (k : ℕ) : Coset H :=
  Quotient.mk _ ((FreeGroup.mk (L.drop k))⁻¹)

/-- The finite set of cosets visited while reading a word from right to left. -/
noncomputable def wordVertices (H : Subgroup (FreeGroup α))
    (L : List (α × Bool)) : Finset (Coset H) :=
  (Finset.range (L.length + 1)).image (suffixCoset H L)

/-- Vertices retained for a finite family of words. -/
noncomputable def vertices (H : Subgroup (FreeGroup α))
    (W : Finset (FreeGroup α)) : Finset (Coset H) :=
  W.biUnion (fun w ↦ wordVertices H w.toWord)

theorem suffixCoset_mem_vertices (H : Subgroup (FreeGroup α))
    {W : Finset (FreeGroup α)} {w : FreeGroup α} (hw : w ∈ W)
    {k : ℕ} (hk : k ≤ w.toWord.length) :
    suffixCoset H w.toWord k ∈ vertices H W := by
  rw [vertices, Finset.mem_biUnion]
  refine ⟨w, hw, ?_⟩
  rw [wordVertices, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

section PartialAction

variable (H : Subgroup (FreeGroup α)) (W : Finset (FreeGroup α))

abbrev Vertex := {x : Coset H // x ∈ vertices H W}

def IsSource (a : α) (x : Vertex H W) : Prop :=
  cosetStep H (FreeGroup.of a) x.1 ∈ vertices H W

def IsTarget (a : α) (y : Vertex H W) : Prop :=
  cosetStep H (FreeGroup.of a)⁻¹ y.1 ∈ vertices H W

noncomputable def fwd (a : α) (x : Vertex H W) (hx : IsSource H W a x) :
    Vertex H W := ⟨cosetStep H (FreeGroup.of a) x.1, hx⟩

noncomputable def bwd (a : α) (y : Vertex H W) (hy : IsTarget H W a y) :
    Vertex H W := ⟨cosetStep H (FreeGroup.of a)⁻¹ y.1, hy⟩

noncomputable def sourceTargetEquiv (a : α) :
    {x : Vertex H W // IsSource H W a x} ≃
      {y : Vertex H W // IsTarget H W a y} where
  toFun x := ⟨fwd H W a x.1 x.2, by
    exact (show cosetStep H (FreeGroup.of a)⁻¹
        (cosetStep H (FreeGroup.of a) x.1.1) ∈ vertices H W by
      rw [cosetStep_inv_cosetStep]
      exact x.1.2)⟩
  invFun y := ⟨bwd H W a y.1 y.2, by
    exact (show cosetStep H (FreeGroup.of a)
        (cosetStep H (FreeGroup.of a)⁻¹ y.1.1) ∈ vertices H W by
      rw [cosetStep_cosetStep_inv]
      exact y.1.2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [fwd, bwd]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [fwd, bwd]

theorem card_compl_eq (a : α) :
    Fintype.card {x : Vertex H W // ¬ IsSource H W a x} =
      Fintype.card {y : Vertex H W // ¬ IsTarget H W a y} := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    Fintype.card_congr (sourceTargetEquiv H W a)]

/-- Completion of the restricted coset action to a permutation of the finite
vertex set. -/
noncomputable def letterPerm (a : α) : Equiv.Perm (Vertex H W) :=
  (Equiv.sumCompl (IsSource H W a)).symm.trans
    (((sourceTargetEquiv H W a).sumCongr
        (Fintype.equivOfCardEq (card_compl_eq H W a))).trans
      (Equiv.sumCompl (IsTarget H W a)))

theorem letterPerm_apply_of_source (a : α) (x : Vertex H W)
    (hx : IsSource H W a x) :
    letterPerm H W a x = fwd H W a x hx := by
  rw [letterPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hx]
  rfl

theorem letterPerm_symm_apply_of_target (a : α) (y : Vertex H W)
    (hy : IsTarget H W a y) :
    (letterPerm H W a).symm y = bwd H W a y hy := by
  rw [letterPerm, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hy]
  rfl

/-- A retained suffix, bundled as a vertex of the finite coset graph. -/
noncomputable def suffixVertex {w : FreeGroup α} (hw : w ∈ W)
    (k : ℕ) (hk : k ≤ w.toWord.length) : Vertex H W :=
  ⟨suffixCoset H w.toWord k, suffixCoset_mem_vertices H hw hk⟩

/-- The permutation attached to one signed letter. -/
noncomputable def toLetterPerm (x : α × Bool) : Equiv.Perm (Vertex H W) :=
  bif x.2 then letterPerm H W x.1 else (letterPerm H W x.1)⁻¹

theorem cosetStep_suffixCoset_of_true {L : List (α × Bool)}
    {k : ℕ} (hk : k < L.length) (hb : L[k].2 = true) :
    cosetStep H (FreeGroup.of L[k].1) (suffixCoset H L (k + 1)) =
      suffixCoset H L k := by
  change Quotient.mk _ ((FreeGroup.mk (L.drop (k + 1)))⁻¹ *
      (FreeGroup.of L[k].1)⁻¹) = Quotient.mk _ ((FreeGroup.mk (L.drop k))⁻¹)
  apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
  have hm := mk_drop_succ L k hk
  simp only [letterValue, hb, cond_true] at hm
  rw [hm]
  group

theorem cosetStep_suffixCoset_of_false {L : List (α × Bool)}
    {k : ℕ} (hk : k < L.length) (hb : L[k].2 = false) :
    cosetStep H (FreeGroup.of L[k].1) (suffixCoset H L k) =
      suffixCoset H L (k + 1) := by
  change Quotient.mk _ ((FreeGroup.mk (L.drop k))⁻¹ *
      (FreeGroup.of L[k].1)⁻¹) =
        Quotient.mk _ ((FreeGroup.mk (L.drop (k + 1)))⁻¹)
  apply congrArg (Quotient.mk (QuotientGroup.rightRel H))
  have hm := mk_drop_succ L k hk
  simp only [letterValue, hb, cond_false] at hm
  rw [hm]
  group

/-- Reading the `k`-th retained letter moves the suffix vertex `k+1` to
the suffix vertex `k`. -/
theorem toLetterPerm_getElem_apply {w : FreeGroup α} (hw : w ∈ W)
    {k : ℕ} (hk : k < w.toWord.length) :
    toLetterPerm H W w.toWord[k]
        (suffixVertex H W hw (k + 1) (by omega)) =
      suffixVertex H W hw k (Nat.le_of_lt hk) := by
  cases hb : w.toWord[k].2 with
  | true =>
      simp only [toLetterPerm, hb, cond_true]
      have hs : IsSource H W w.toWord[k].1
          (suffixVertex H W hw (k + 1) (by omega)) := by
        change cosetStep H (FreeGroup.of w.toWord[k].1)
            (suffixCoset H w.toWord (k + 1)) ∈ vertices H W
        rw [cosetStep_suffixCoset_of_true H hk hb]
        exact suffixCoset_mem_vertices H hw (Nat.le_of_lt hk)
      rw [letterPerm_apply_of_source H W _ _ hs]
      apply Subtype.ext
      exact cosetStep_suffixCoset_of_true H hk hb
  | false =>
      simp only [toLetterPerm, hb, cond_false]
      have hs : IsSource H W w.toWord[k].1
          (suffixVertex H W hw k (Nat.le_of_lt hk)) := by
        change cosetStep H (FreeGroup.of w.toWord[k].1)
            (suffixCoset H w.toWord k) ∈ vertices H W
        rw [cosetStep_suffixCoset_of_false H hk hb]
        exact suffixCoset_mem_vertices H hw (by omega)
      have hp := letterPerm_apply_of_source H W w.toWord[k].1
        (suffixVertex H W hw k (Nat.le_of_lt hk)) hs
      have hp' : letterPerm H W w.toWord[k].1
          (suffixVertex H W hw k (Nat.le_of_lt hk)) =
            suffixVertex H W hw (k + 1) (by omega) := by
        rw [hp]
        apply Subtype.ext
        exact cosetStep_suffixCoset_of_false H hk hb
      change (letterPerm H W w.toWord[k].1).symm
          (suffixVertex H W hw (k + 1) (by omega)) =
        suffixVertex H W hw k (Nat.le_of_lt hk)
      rw [← hp']
      exact Equiv.symm_apply_apply _ _

/-- Telescoping along a retained word. -/
theorem prod_map_drop_apply {w : FreeGroup α} (hw : w ∈ W) :
    ∀ j : ℕ, ∀ hj : j ≤ w.toWord.length,
      ((w.toWord.drop (w.toWord.length - j)).map
          (toLetterPerm H W)).prod
          (suffixVertex H W hw w.toWord.length le_rfl) =
        suffixVertex H W hw (w.toWord.length - j) (by omega) := by
  intro j
  induction j with
  | zero =>
      intro _
      apply Subtype.ext
      simp [suffixVertex]
  | succ j ih =>
      intro hj
      have hk : w.toWord.length - (j + 1) < w.toWord.length := by omega
      rw [List.drop_eq_getElem_cons hk, List.map_cons, List.prod_cons,
        Equiv.Perm.mul_apply,
        show w.toWord.length - (j + 1) + 1 =
          w.toWord.length - j from by omega,
        ih (by omega)]
      have hi : w.toWord.length - j =
          w.toWord.length - (j + 1) + 1 := by omega
      simpa only [hi] using toLetterPerm_getElem_apply H W hw hk

/-- The homomorphism supplied by completing the finite partial coset action. -/
noncomputable def wordHom : FreeGroup α →* Equiv.Perm (Vertex H W) :=
  FreeGroup.lift (letterPerm H W)

theorem wordHom_apply_suffixEnd {w : FreeGroup α} (hw : w ∈ W) :
    wordHom H W w (suffixVertex H W hw w.toWord.length le_rfl) =
      suffixVertex H W hw 0 (Nat.zero_le _) := by
  change (FreeGroup.lift (letterPerm H W)) w
      (suffixVertex H W hw w.toWord.length le_rfl) =
    suffixVertex H W hw 0 (Nat.zero_le _)
  calc
    _ = (FreeGroup.lift (letterPerm H W)) (FreeGroup.mk w.toWord)
        (suffixVertex H W hw w.toWord.length le_rfl) := by
      rw [FreeGroup.mk_toWord]
    _ = ((w.toWord.map (toLetterPerm H W)).prod)
        (suffixVertex H W hw w.toWord.length le_rfl) := by
      rw [FreeGroup.lift_mk]
      rfl
    _ = _ := by
      simpa only [Nat.sub_self, List.drop_zero] using
        prod_map_drop_apply H W hw w.toWord.length le_rfl

end PartialAction

section Separation

variable (H : Subgroup (FreeGroup α))

/-- The finite Hall action associated to finite subgroup generators `X` and
the element `w` to be separated. -/
noncomputable def hallHom (X : Finset (FreeGroup α)) (w : FreeGroup α) :
    FreeGroup α →* Equiv.Perm (Vertex H (insert w X)) :=
  wordHom H (insert w X)

noncomputable def baseVertex (X : Finset (FreeGroup α)) (w : FreeGroup α) :
    Vertex H (insert w X) :=
  suffixVertex H (insert w X) (Finset.mem_insert_self w X)
    w.toWord.length le_rfl

theorem suffixEnd_eq_base {X : Finset (FreeGroup α)} {w u : FreeGroup α}
    (hu : u ∈ insert w X) :
    suffixVertex H (insert w X) hu u.toWord.length le_rfl =
      baseVertex H X w := by
  apply Subtype.ext
  simp [suffixVertex, suffixCoset, baseVertex]

theorem hallHom_apply_base {X : Finset (FreeGroup α)} {w u : FreeGroup α}
    (hu : u ∈ insert w X) :
    hallHom H X w u (baseVertex H X w) =
      suffixVertex H (insert w X) hu 0 (Nat.zero_le _) := by
  rw [← suffixEnd_eq_base H hu, hallHom]
  exact wordHom_apply_suffixEnd H (insert w X) hu

theorem hallHom_fixes_of_mem {X : Finset (FreeGroup α)} {w u : FreeGroup α}
    (huX : u ∈ X) (huH : u ∈ H) :
    hallHom H X w u (baseVertex H X w) = baseVertex H X w := by
  have hu : u ∈ insert w X := Finset.mem_insert_of_mem huX
  rw [hallHom_apply_base H hu]
  apply Subtype.ext
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hmku : FreeGroup.mk u.toWord = u := FreeGroup.mk_toWord
  have hnil : FreeGroup.mk ([] : List (α × Bool)) = 1 := by
    rw [mk_eq_wordProd]
    rfl
  simpa [suffixVertex, suffixCoset, baseVertex, hmku, hnil] using huH

theorem hallHom_fixes_closure {X : Finset (FreeGroup α)} {w : FreeGroup α}
    (hXH : (X : Set (FreeGroup α)) ⊆ H)
    {u : FreeGroup α} (hu : u ∈ Subgroup.closure (X : Set (FreeGroup α))) :
    hallHom H X w u (baseVertex H X w) = baseVertex H X w := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      exact hallHom_fixes_of_mem H hu (hXH hu)
  | one => simp
  | mul x y _ _ hx hy => simp [hx, hy]
  | inv x _ hx =>
      rw [map_inv]
      change (hallHom H X w x).symm (baseVertex H X w) = baseVertex H X w
      calc
        _ = (hallHom H X w x).symm
            (hallHom H X w x (baseVertex H X w)) :=
          congrArg (hallHom H X w x).symm hx.symm
        _ = _ := Equiv.symm_apply_apply _ _

theorem hallHom_moves {X : Finset (FreeGroup α)} {w : FreeGroup α}
    (hw : w ∉ H) :
    hallHom H X w w (baseVertex H X w) ≠ baseVertex H X w := by
  rw [hallHom_apply_base H (Finset.mem_insert_self w X)]
  intro heq
  have hrel := Quotient.exact (congrArg Subtype.val heq)
  apply hw
  have := QuotientGroup.rightRel_apply.mp hrel
  have hmkw : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
  have hnil : FreeGroup.mk ([] : List (α × Bool)) = 1 := by
    rw [mk_eq_wordProd]
    rfl
  simpa [suffixVertex, suffixCoset, baseVertex, hmkw, hnil] using this

/-- Conjugate permutations to a universe-zero finite set, as required by the
definition of `profiniteClosure`. -/
noncomputable def permTransport {Y : Type*} {n : ℕ} (e : Y ≃ Fin n) :
    Equiv.Perm Y →* Equiv.Perm (Fin n) where
  toFun p := (e.symm.trans p).trans e
  map_one' := by ext y; simp
  map_mul' p q := by ext y; simp

@[simp] theorem permTransport_apply {Y : Type*} {n : ℕ} (e : Y ≃ Fin n)
    (p : Equiv.Perm Y) (y : Fin n) :
    permTransport e p y = e (p (e.symm y)) := rfl

theorem permTransport_injective {Y : Type*} {n : ℕ} (e : Y ≃ Fin n) :
    Function.Injective (permTransport e) := by
  intro p q hp
  ext y
  have heval := congrArg (fun r : Equiv.Perm (Fin n) ↦ r (e y)) hp
  simp only [permTransport_apply, Equiv.symm_apply_apply] at heval
  exact e.injective heval

noncomputable def vertexEquivFin (X : Finset (FreeGroup α)) (w : FreeGroup α) :
    Vertex H (insert w X) ≃ Fin (Fintype.card (Vertex H (insert w X))) :=
  Fintype.equivFin _

/-- The universe-zero finite quotient implementing Hall separation. -/
noncomputable def hallFiniteHom (X : Finset (FreeGroup α)) (w : FreeGroup α) :
    FreeGroup α →* Equiv.Perm (Fin (Fintype.card (Vertex H (insert w X)))) :=
  (permTransport (vertexEquivFin H X w)).comp (hallHom H X w)

/-- **Marshall Hall separation for free groups.**  Every finitely generated
subgroup of a free group is closed in the profinite topology. -/
theorem profiniteClosure_eq_of_fg (hH : H.FG) : profiniteClosure H = H := by
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff H).mp hH
  classical
  let X : Finset (FreeGroup α) := hSfin.toFinset
  have hX : (X : Set (FreeGroup α)) = S := Set.Finite.coe_toFinset hSfin
  apply le_antisymm
  · intro w hw
    by_contra hnot
    have hXH : (X : Set (FreeGroup α)) ⊆ H := by
      rw [hX, ← hS]
      exact Subgroup.subset_closure
    have hsep : hallFiniteHom H X w w ∉ H.map (hallFiniteHom H X w) := by
      rintro ⟨u, huH, hueq⟩
      have hucl : u ∈ Subgroup.closure (X : Set (FreeGroup α)) := by
        rw [hX, hS]
        exact huH
      have hfix := hallHom_fixes_closure (w := w) H hXH hucl
      have hraw : hallHom H X w u = hallHom H X w w :=
        permTransport_injective (vertexEquivFin H X w) hueq
      have heval := congrArg (fun p : Equiv.Perm (Vertex H (insert w X)) ↦
        p (baseVertex H X w)) hraw
      exact hallHom_moves H hnot (heval.symm.trans hfix)
    exact hsep (hw _ (hallFiniteHom H X w))
  · exact le_profiniteClosure H

end Separation

end FreeGroupHall
end GroupApproximation
