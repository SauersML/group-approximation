import GroupApproximation.Dynamics.Surjunctivity
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finite windows for nonuniform cellular maps

These maps may have coordinate-dependent rules. Composition reads a product
of memory sets, in outer-to-inner order. The window comparison theorem is
the local calculation used when deleting inactive corrections in peeling.
-/

namespace GroupApproximation.Surjunctivity

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] [DecidableEq G] {B : Type v}

omit [DecidableEq G] in
theorem HasMemory.mono {τ : (G → B) → (G → B)} {M N : Finset G}
    (hτ : HasMemory τ M) (hMN : M ⊆ N) : HasMemory τ N := by
  intro x y g hxy
  exact hτ x y g fun m hm => hxy m (hMN hm)

omit [DecidableEq G] in
theorem hasMemory_id : HasMemory (id : (G → B) → (G → B)) {1} := by
  intro x y g hxy
  simpa using hxy 1 (Finset.mem_singleton_self 1)

theorem HasMemory.comp {σ τ : (G → B) → (G → B)} {M N : Finset G}
    (hσ : HasMemory σ M) (hτ : HasMemory τ N) : HasMemory (σ ∘ τ) (M * N) := by
  classical
  intro x y g hxy
  apply hσ (τ x) (τ y) g
  intro m hm
  apply hτ x y (g * m)
  intro n hn
  simpa only [mul_assoc] using hxy (m * n) (Finset.mul_mem_mul hm hn)

theorem IsFiniteMemory.comp {σ τ : (G → B) → (G → B)}
    (hσ : IsFiniteMemory σ) (hτ : IsFiniteMemory τ) :
    IsFiniteMemory (σ ∘ τ) := by
  rcases hσ with ⟨M, hM⟩
  rcases hτ with ⟨N, hN⟩
  exact ⟨M * N, hM.comp hN⟩

omit [DecidableEq G] in
/-- Equality of inputs on the enlarged window gives equality on the output window. -/
theorem HasMemory.eqOn {τ : (G → B) → (G → B)} {M : Finset G}
    (hτ : HasMemory τ M) {R : Set G} {x y : G → B}
    (hxy : Set.EqOn x y (R * (M : Set G))) : Set.EqOn (τ x) (τ y) R := by
  intro g hg
  apply hτ x y g
  intro m hm
  exact hxy (Set.mul_mem_mul hg hm)

omit [Group G] [DecidableEq G] in
/-- A coordinate fixed for every input is also fixed by the inverse. -/
theorem Equiv.symm_apply_eq_on {R : Set G} (e : (G → B) ≃ (G → B))
    (he : ∀ x, Set.EqOn (e x) x R) (y : G → B) :
    Set.EqOn (e.symm y) y R := by
  intro g hg
  have h := he (e.symm y) hg
  simpa only [e.apply_symm_apply] using h.symm

/-- A map together with a concrete uniform memory containing the identity. -/
structure WindowMap (G : Type u) [Group G] (B : Type v) where
  toFun : (G → B) → (G → B)
  memory : Finset G
  one_mem : 1 ∈ memory
  hasMemory : HasMemory toFun memory

namespace WindowMap

def identity : WindowMap G B where
  toFun := id
  memory := {1}
  one_mem := Finset.mem_singleton_self 1
  hasMemory := hasMemory_id

def comp (f h : WindowMap G B) : WindowMap G B where
  toFun := f.toFun ∘ h.toFun
  memory := f.memory * h.memory
  one_mem := by simpa using Finset.mul_mem_mul f.one_mem h.one_mem
  hasMemory := f.hasMemory.comp h.hasMemory

/-- The head of the list acts last, matching the order of memory products. -/
def compose : List (WindowMap G B) → WindowMap G B
  | [] => identity
  | f :: fs => f.comp (compose fs)

@[simp] theorem compose_nil_apply (x : G → B) :
    (compose ([] : List (WindowMap G B))).toFun x = x := rfl

@[simp] theorem compose_cons_apply (f : WindowMap G B)
    (fs : List (WindowMap G B)) (x : G → B) :
    (compose (f :: fs)).toFun x = f.toFun ((compose fs).toFun x) := rfl

/-- Compare a list of local maps with any other list, on successively enlarged
windows. The comparison maps need no memory bound of their own. -/
def AgreeAlong : List (WindowMap G B) → List ((G → B) → (G → B)) → Set G → Prop
  | [], [], _ => True
  | f :: fs, h :: hs, R =>
      (∀ x, Set.EqOn (f.toFun x) (h x) R) ∧
        AgreeAlong fs hs (R * (f.memory : Set G))
  | _, _, _ => False

def evaluate : List ((G → B) → (G → B)) → (G → B) → (G → B)
  | [], x => x
  | h :: hs, x => h (evaluate hs x)

/-- The shrinking-window comparison used in the marked-site induction. -/
theorem compose_eqOn_evaluate (fs : List (WindowMap G B))
    (hs : List ((G → B) → (G → B))) (R : Set G)
    (h : AgreeAlong fs hs R) (x : G → B) :
    Set.EqOn ((compose fs).toFun x) (evaluate hs x) R := by
  induction fs generalizing hs R with
  | nil =>
      cases hs with
      | nil => exact fun _ _ => rfl
      | cons t ts => exact False.elim h
  | cons f fs ih =>
      cases hs with
      | nil => exact False.elim h
      | cons t ts =>
          obtain ⟨hhead, htail⟩ := h
          intro g hg
          exact (f.hasMemory.eqOn (ih ts _ htail) hg).trans
            (hhead (evaluate ts x) hg)

/-- One common enlarged window contains every intermediate window. The
identity in each memory is what makes the head comparison valid on `R`. -/
theorem agreeAlong_of_commonWindow (fs : List (WindowMap G B))
    (model : WindowMap G B → (G → B) → (G → B)) (R : Set G)
    (h : ∀ f ∈ fs, ∀ x, Set.EqOn (f.toFun x) (model f x)
      (R * ((compose fs).memory : Set G))) :
    AgreeAlong fs (fs.map model) R := by
  induction fs generalizing R with
  | nil => trivial
  | cons f fs ih =>
      constructor
      · intro x g hg
        apply h f (List.mem_cons_self ..) x
        exact ⟨g, hg, 1, (compose (f :: fs)).one_mem, mul_one g⟩
      · apply ih
        intro t ht x g hg
        apply h t (List.mem_cons_of_mem f ht) x
        obtain ⟨a, ha, q, hq, rfl⟩ := hg
        obtain ⟨r, hr, p, hp, rfl⟩ := ha
        refine ⟨r, hr, p * q, ?_, (mul_assoc r p q).symm⟩
        exact Finset.mul_mem_mul hp hq

/-- Comparing every local rule on one common window compares the composites. -/
theorem compose_eqOn_of_commonWindow (fs : List (WindowMap G B))
    (model : WindowMap G B → (G → B) → (G → B)) (R : Set G)
    (h : ∀ f ∈ fs, ∀ x, Set.EqOn (f.toFun x) (model f x)
      (R * ((compose fs).memory : Set G))) (x : G → B) :
    Set.EqOn ((compose fs).toFun x) (evaluate (fs.map model) x) R :=
  compose_eqOn_evaluate fs (fs.map model) R
    (agreeAlong_of_commonWindow fs model R h) x

/-- Replacing inactive maps by identity has the same global effect as
deleting them; this assertion needs no commutativity of the maps. -/
theorem evaluate_keep (fs : List (WindowMap G B))
    (keep : WindowMap G B → Prop) [DecidablePred keep] (x : G → B) :
    evaluate (fs.map fun f => if keep f then f.toFun else id) x =
      (compose (fs.filter keep)).toFun x := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      by_cases hf : keep f
      · simp [hf, evaluate, ih]
      · simp [hf, evaluate, ih]

/-- Inactive corrections can be deleted on a window if they fix each
coordinate of its enlargement for every input configuration. -/
theorem compose_eqOn_filter (fs : List (WindowMap G B))
    (keep : WindowMap G B → Prop) [DecidablePred keep] (R : Set G)
    (h : ∀ f ∈ fs, ¬ keep f → ∀ x, Set.EqOn (f.toFun x) x
      (R * ((compose fs).memory : Set G))) (x : G → B) :
    Set.EqOn ((compose fs).toFun x) ((compose (fs.filter keep)).toFun x) R := by
  have hcompare := compose_eqOn_of_commonWindow fs
    (fun f => if keep f then f.toFun else id) R ?_ x
  · simpa only [evaluate_keep] using hcompare
  · intro f hf y
    by_cases hk : keep f
    · simp only [if_pos hk]
      exact Set.eqOn_refl _ _
    · simpa only [if_neg hk, id_eq] using h f hf hk y

/-- Local cancellation: if the retained corrections cancel globally, then
the full composite fixes the requested window. -/
theorem compose_eqOn_id_of_filter (fs : List (WindowMap G B))
    (keep : WindowMap G B → Prop) [DecidablePred keep] (R : Set G)
    (h : ∀ f ∈ fs, ¬ keep f → ∀ x, Set.EqOn (f.toFun x) x
      (R * ((compose fs).memory : Set G)))
    (hcancel : (compose (fs.filter keep)).toFun = id) (x : G → B) :
    Set.EqOn ((compose fs).toFun x) x R := by
  simpa only [hcancel, id_eq] using compose_eqOn_filter fs keep R h x

universe w

/-- Indexed comparison retains labels even when two local maps happen to be equal. -/
theorem agreeAlong_indexed_of_commonWindow {I : Type w} (L : List I)
    (f : I → WindowMap G B) (model : I → (G → B) → (G → B)) (R : Set G)
    (h : ∀ i ∈ L, ∀ x, Set.EqOn ((f i).toFun x) (model i x)
      (R * ((compose (L.map f)).memory : Set G))) :
    AgreeAlong (L.map f) (L.map model) R := by
  induction L generalizing R with
  | nil => trivial
  | cons i L ih =>
      constructor
      · intro x g hg
        apply h i (List.mem_cons_self ..) x
        exact ⟨g, hg, 1, (compose ((i :: L).map f)).one_mem, mul_one g⟩
      · apply ih
        intro j hj x g hg
        apply h j (List.mem_cons_of_mem i hj) x
        obtain ⟨a, ha, q, hq, rfl⟩ := hg
        obtain ⟨r, hr, p, hp, rfl⟩ := ha
        refine ⟨r, hr, p * q, ?_, (mul_assoc r p q).symm⟩
        exact Finset.mul_mem_mul hp hq

theorem compose_eqOn_indexed_of_commonWindow {I : Type w} (L : List I)
    (f : I → WindowMap G B) (model : I → (G → B) → (G → B)) (R : Set G)
    (h : ∀ i ∈ L, ∀ x, Set.EqOn ((f i).toFun x) (model i x)
      (R * ((compose (L.map f)).memory : Set G))) (x : G → B) :
    Set.EqOn ((compose (L.map f)).toFun x) (evaluate (L.map model) x) R :=
  compose_eqOn_evaluate (L.map f) (L.map model) R
    (agreeAlong_indexed_of_commonWindow L f model R h) x

theorem evaluate_indexed_keep {I : Type w} (L : List I) (f : I → WindowMap G B)
    (keep : I → Prop) [DecidablePred keep] (x : G → B) :
    evaluate (L.map fun i => if keep i then (f i).toFun else id) x =
      (compose ((L.filter keep).map f)).toFun x := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      by_cases hi : keep i
      · simp [hi, evaluate, ih]
      · simp [hi, evaluate, ih]

theorem compose_eqOn_indexed_filter {I : Type w} (L : List I)
    (f : I → WindowMap G B) (keep : I → Prop) [DecidablePred keep] (R : Set G)
    (h : ∀ i ∈ L, ¬ keep i → ∀ x, Set.EqOn ((f i).toFun x) x
      (R * ((compose (L.map f)).memory : Set G))) (x : G → B) :
    Set.EqOn ((compose (L.map f)).toFun x)
      ((compose ((L.filter keep).map f)).toFun x) R := by
  have hcompare := compose_eqOn_indexed_of_commonWindow L f
    (fun i => if keep i then (f i).toFun else id) R ?_ x
  · simpa only [evaluate_indexed_keep] using hcompare
  · intro i hi y
    by_cases hk : keep i
    · simp only [if_pos hk]
      exact Set.eqOn_refl _ _
    · simpa only [if_neg hk, id_eq] using h i hi hk y

end WindowMap
end GroupApproximation.Surjunctivity
