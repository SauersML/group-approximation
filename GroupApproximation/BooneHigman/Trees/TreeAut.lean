import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Action.End

/-!
# Automorphisms of rooted trees and self-similar groups

For an alphabet `X`, the rooted tree `T_X` has vertex set `List X`: the root is `[]` and the
children of `w` are the words `w ++ [x]`.  An automorphism of `T_X` is the same thing as a
permutation of `List X` that preserves length and the prefix order.

* `treeAut X : Subgroup (Equiv.Perm (List X))` and `TreeAut X`, the group `Aut(T_X)`, acting on
  words by `•`.
* `TreeAut.state g w`, the state (section) `g|_w`, characterized by `TreeAut.smul_append`:
  `g • (w ++ v) = g • w ++ state g w • v`.  Its calculus: `state_nil`, `state_append`, `state_one`,
  `state_mul`, `state_inv`.
* `TreeAut.rootPerm g : Equiv.Perm X`, the action on the first level, with the homomorphism
  `TreeAut.rootPermHom` and `TreeAut.smul_cons`: `g • (x :: v) = rootPerm g x :: state g [x] • v`.
* `TreeAut.ofWreath σ f`, the automorphism with root permutation `σ` and first-level states `f`,
  with `rootPerm_ofWreath`, `state_ofWreath` and `ofWreath_rootPerm_state`.  Together with
  `state_mul` this is the wreath recursion `Aut(T_X) ≅ Sym(X) ≀_X Aut(T_X)`.
* `IsSelfSimilar G` (Zaremsky, arXiv:2405.09722, Definition 2.1), `IsSelfSimilar.state_mem` for all
  vertices, and `IsSelfSimilarRep ρ` for a faithful homomorphism with self-similar range.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Trees

variable {X : Type*}

/-- A map of words is a *tree map* when it preserves length and prefixes. -/
def IsTreeMap (f : List X → List X) : Prop :=
  (∀ w, (f w).length = w.length) ∧ ∀ w v, f w <+: f (w ++ v)

variable (X) in
/-- The automorphism group of the rooted tree `X^*`: the permutations of words that preserve
length and prefixes. -/
def treeAut : Subgroup (Equiv.Perm (List X)) where
  carrier := {g | IsTreeMap g}
  one_mem' := by
    show IsTreeMap (1 : Equiv.Perm (List X))
    exact ⟨fun _ => rfl, fun w v => List.prefix_append w v⟩
  mul_mem' := by
    intro g h hg hh
    have hg : IsTreeMap g := hg
    have hh : IsTreeMap h := hh
    show IsTreeMap (g * h)
    refine ⟨fun w => ?_, fun w v => ?_⟩
    · rw [Equiv.Perm.mul_apply, hg.1, hh.1]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      obtain ⟨r, hr⟩ := hh.2 w v
      rw [← hr]
      exact hg.2 _ _
  inv_mem' := by
    intro g hg
    have hg : IsTreeMap g := hg
    show IsTreeMap (Equiv.symm g)
    have hlen : ∀ w, (g.symm w).length = w.length := fun w => by
      have h := hg.1 (g.symm w)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    refine ⟨hlen, fun w v => ?_⟩
    have hgu : g (g.symm (w ++ v)) = w ++ v := Equiv.apply_symm_apply g _
    have hul : w.length ≤ (g.symm (w ++ v)).length := by
      rw [hlen, List.length_append]; omega
    have key := hg.2 ((g.symm (w ++ v)).take w.length) ((g.symm (w ++ v)).drop w.length)
    rw [List.take_append_drop, hgu] at key
    have hlt : (g ((g.symm (w ++ v)).take w.length)).length = w.length := by
      rw [hg.1, List.length_take]; omega
    have hw : g ((g.symm (w ++ v)).take w.length) = w := by
      rw [List.prefix_iff_eq_take.1 key, hlt, List.take_left]
    have hsw := congrArg g.symm hw
    rw [Equiv.symm_apply_apply] at hsw
    rw [← hsw]
    exact List.take_prefix _ _

variable (X) in
/-- `Aut(T_X)`, the automorphism group of the rooted tree of words over `X`. -/
abbrev TreeAut := ↥(treeAut X)

namespace TreeAut

theorem smul_def (g : TreeAut X) (w : List X) : g • w = (g : Equiv.Perm (List X)) w := rfl

theorem isTreeMap (g : TreeAut X) : IsTreeMap (fun w : List X => g • w) := g.2

theorem length_smul (g : TreeAut X) (w : List X) : (g • w).length = w.length :=
  g.isTreeMap.1 w

theorem smul_prefix (g : TreeAut X) (w v : List X) : g • w <+: g • (w ++ v) :=
  g.isTreeMap.2 w v

@[simp] theorem smul_nil (g : TreeAut X) : g • ([] : List X) = [] :=
  List.eq_nil_of_length_eq_zero (length_smul g [])

theorem ext {g h : TreeAut X} (hgh : ∀ w : List X, g • w = h • w) : g = h :=
  Subtype.ext (Equiv.ext hgh)

/-! ## States -/

/-- The words of the state `g|_w`: `stateFun g w v` is `g • (w ++ v)` with `g • w` removed. -/
def stateFun (g : TreeAut X) (w v : List X) : List X := (g • (w ++ v)).drop w.length

theorem smul_append_stateFun (g : TreeAut X) (w v : List X) :
    g • (w ++ v) = g • w ++ stateFun g w v := by
  have h := List.prefix_iff_eq_append.1 (smul_prefix g w v)
  rw [length_smul] at h
  exact h.symm

theorem stateFun_eq_of_smul_append (g : TreeAut X) {w x y : List X}
    (h : g • (w ++ x) = g • w ++ y) : stateFun g w x = y :=
  List.append_cancel_left ((smul_append_stateFun g w x).symm.trans h)

theorem length_stateFun (g : TreeAut X) (w v : List X) : (stateFun g w v).length = v.length := by
  have h := congrArg List.length (smul_append_stateFun g w v)
  rw [List.length_append, length_smul, length_smul, List.length_append] at h
  omega

theorem stateFun_append (g : TreeAut X) (w v u : List X) :
    stateFun g w (v ++ u) = stateFun g w v ++ stateFun g (w ++ v) u := by
  apply stateFun_eq_of_smul_append
  rw [← List.append_assoc w v u, smul_append_stateFun g (w ++ v) u,
    smul_append_stateFun g w v, List.append_assoc]

theorem isTreeMap_stateFun (g : TreeAut X) (w : List X) : IsTreeMap (stateFun g w) :=
  ⟨length_stateFun g w, fun v u => by rw [stateFun_append]; exact List.prefix_append _ _⟩

/-- The state `g|_w` as a permutation of words; its inverse is `(g⁻¹)|_(g • w)`. -/
def statePerm (g : TreeAut X) (w : List X) : Equiv.Perm (List X) where
  toFun := stateFun g w
  invFun := stateFun g⁻¹ (g • w)
  left_inv v := by
    apply stateFun_eq_of_smul_append
    rw [← smul_append_stateFun g w v, inv_smul_smul, inv_smul_smul]
  right_inv v := by
    apply stateFun_eq_of_smul_append
    have h := smul_append_stateFun g⁻¹ (g • w) v
    rw [inv_smul_smul] at h
    rw [← h, smul_inv_smul]

/-- The **state** (section) `g|_w` of `g` at the vertex `w`. -/
def state (g : TreeAut X) (w : List X) : TreeAut X := ⟨statePerm g w, isTreeMap_stateFun g w⟩

theorem state_smul (g : TreeAut X) (w v : List X) : state g w • v = stateFun g w v := rfl

/-- The defining property of states: `g • (w ++ v) = g • w ++ g|_w • v`. -/
theorem smul_append (g : TreeAut X) (w v : List X) : g • (w ++ v) = g • w ++ state g w • v :=
  smul_append_stateFun g w v

/-- States are determined by the defining property. -/
theorem state_smul_eq_of_smul_append (g : TreeAut X) {w x y : List X}
    (h : g • (w ++ x) = g • w ++ y) : state g w • x = y :=
  stateFun_eq_of_smul_append g h

@[simp] theorem state_nil (g : TreeAut X) : state g [] = g :=
  ext fun v => by
    show stateFun g [] v = g • v
    exact stateFun_eq_of_smul_append g (by simp)

theorem state_append (g : TreeAut X) (w u : List X) : state g (w ++ u) = state (state g w) u :=
  ext fun v =>
    List.append_cancel_left ((stateFun_append g w u v).symm.trans (smul_append (state g w) u v))

@[simp] theorem state_one (w : List X) : state (1 : TreeAut X) w = 1 :=
  ext fun v => by
    show stateFun 1 w v = (1 : TreeAut X) • v
    exact stateFun_eq_of_smul_append 1 (by simp only [one_smul])

theorem state_mul (g h : TreeAut X) (w : List X) :
    state (g * h) w = state g (h • w) * state h w :=
  ext fun v => by
    show stateFun (g * h) w v = state g (h • w) • state h w • v
    apply stateFun_eq_of_smul_append
    rw [mul_smul, mul_smul, smul_append h w v, smul_append g (h • w)]

theorem state_inv (g : TreeAut X) (w : List X) : state g⁻¹ w = (state g (g⁻¹ • w))⁻¹ := by
  have h := state_mul g g⁻¹ w
  rw [mul_inv_cancel, state_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-! ## The first level -/

/-- The letter that `g` sends `x` to, read off the first level. -/
def rootFun (g : TreeAut X) (x : X) : X := (g • [x]).headD x

theorem smul_singleton (g : TreeAut X) (x : X) : g • [x] = [rootFun g x] := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 (length_smul g [x])
  simp [rootFun, ha]

theorem rootFun_mul (g h : TreeAut X) (x : X) : rootFun (g * h) x = rootFun g (rootFun h x) := by
  have e : (g * h) • [x] = g • h • [x] := mul_smul g h [x]
  rw [smul_singleton (g * h) x, smul_singleton h x, smul_singleton g (rootFun h x)] at e
  exact List.singleton_inj.1 e

theorem rootFun_one (x : X) : rootFun (1 : TreeAut X) x = x := by
  have e : (1 : TreeAut X) • [x] = [x] := one_smul _ _
  rw [smul_singleton] at e
  exact List.singleton_inj.1 e

/-- The action of `g` on the first level `X`. -/
def rootPerm (g : TreeAut X) : Equiv.Perm X where
  toFun := rootFun g
  invFun := rootFun g⁻¹
  left_inv x := by rw [← rootFun_mul, inv_mul_cancel, rootFun_one]
  right_inv x := by rw [← rootFun_mul, mul_inv_cancel, rootFun_one]

@[simp] theorem rootPerm_apply (g : TreeAut X) (x : X) : rootPerm g x = rootFun g x := rfl

/-- The first level as a homomorphism `Aut(T_X) →* Sym(X)`. -/
def rootPermHom : TreeAut X →* Equiv.Perm X where
  toFun := rootPerm
  map_one' := Equiv.ext rootFun_one
  map_mul' g h := Equiv.ext (rootFun_mul g h)

@[simp] theorem rootPermHom_apply (g : TreeAut X) : rootPermHom g = rootPerm g := rfl

/-- The wreath recursion on words: `g • (x :: v) = rootPerm g x :: g|_[x] • v`. -/
theorem smul_cons (g : TreeAut X) (x : X) (v : List X) :
    g • (x :: v) = rootPerm g x :: state g [x] • v := by
  have h := smul_append g [x] v
  rw [smul_singleton] at h
  exact h

/-! ## Automorphisms from wreath data -/

/-- The words of `ofWreath σ f`. -/
def ofWreathFun (σ : Equiv.Perm X) (f : X → TreeAut X) : List X → List X
  | [] => []
  | x :: v => σ x :: f x • v

theorem isTreeMap_ofWreathFun (σ : Equiv.Perm X) (f : X → TreeAut X) :
    IsTreeMap (ofWreathFun σ f) := by
  refine ⟨?_, ?_⟩
  · rintro (_ | ⟨x, v⟩)
    · rfl
    · simp only [ofWreathFun, List.length_cons, length_smul]
  · rintro (_ | ⟨x, v⟩) u
    · exact List.nil_prefix
    · simp only [ofWreathFun, List.cons_append, List.cons_prefix_cons, true_and]
      exact smul_prefix (f x) v u

/-- `ofWreath σ f` as a permutation of words. -/
def ofWreathPerm (σ : Equiv.Perm X) (f : X → TreeAut X) : Equiv.Perm (List X) where
  toFun := ofWreathFun σ f
  invFun := ofWreathFun σ⁻¹ fun y => (f (σ⁻¹ y))⁻¹
  left_inv := by
    rintro (_ | ⟨x, v⟩)
    · rfl
    · simp [ofWreathFun]
  right_inv := by
    rintro (_ | ⟨y, v⟩)
    · rfl
    · simp [ofWreathFun]

/-- The tree automorphism with root permutation `σ` and first-level states `f`:
`ofWreath σ f • (x :: v) = σ x :: f x • v`. -/
def ofWreath (σ : Equiv.Perm X) (f : X → TreeAut X) : TreeAut X :=
  ⟨ofWreathPerm σ f, isTreeMap_ofWreathFun σ f⟩

@[simp] theorem ofWreath_smul_nil (σ : Equiv.Perm X) (f : X → TreeAut X) :
    ofWreath σ f • ([] : List X) = [] := rfl

@[simp] theorem ofWreath_smul_cons (σ : Equiv.Perm X) (f : X → TreeAut X) (x : X) (v : List X) :
    ofWreath σ f • (x :: v) = σ x :: f x • v := rfl

@[simp] theorem rootPerm_ofWreath (σ : Equiv.Perm X) (f : X → TreeAut X) :
    rootPerm (ofWreath σ f) = σ :=
  Equiv.ext fun x => by simp [rootFun]

@[simp] theorem state_ofWreath (σ : Equiv.Perm X) (f : X → TreeAut X) (x : X) :
    state (ofWreath σ f) [x] = f x :=
  ext fun v => by
    show stateFun (ofWreath σ f) [x] v = f x • v
    exact stateFun_eq_of_smul_append _ (by simp)

/-- Every automorphism is recovered from its root permutation and first-level states. -/
theorem ofWreath_rootPerm_state (g : TreeAut X) :
    ofWreath (rootPerm g) (fun x => state g [x]) = g :=
  ext fun w => by
    cases w with
    | nil => simp
    | cons x v => rw [ofWreath_smul_cons, smul_cons]

theorem eq_iff_rootPerm_state {g h : TreeAut X} :
    g = h ↔ rootPerm g = rootPerm h ∧ ∀ x, state g [x] = state h [x] := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← ofWreath_rootPerm_state g, ← ofWreath_rootPerm_state h, h1]
    simp only [h2]

end TreeAut

open TreeAut

/-! ## Self-similar groups -/

/-- **Self-similar groups** (Zaremsky, arXiv:2405.09722, Definition 2.1): a subgroup
`G ≤ Aut(T_X)` is self-similar when its image under the wreath recursion
`Aut(T_X) ≅ Sym(X) ≀_X Aut(T_X)` lies in `Sym(X) ≀_X G`.  By `TreeAut.ofWreath_rootPerm_state`
this says exactly that every first-level state of every element of `G` lies in `G`. -/
def IsSelfSimilar (G : Subgroup (TreeAut X)) : Prop :=
  ∀ g ∈ G, ∀ x : X, state g [x] ∈ G

theorem IsSelfSimilar.state_mem {G : Subgroup (TreeAut X)} (hG : IsSelfSimilar G)
    {g : TreeAut X} (hg : g ∈ G) (w : List X) : state g w ∈ G := by
  induction w generalizing g with
  | nil => rwa [state_nil]
  | cons x w ih =>
    show state g ([x] ++ w) ∈ G
    rw [state_append]
    exact ih (hG g hg x)

theorem isSelfSimilar_iff {G : Subgroup (TreeAut X)} :
    IsSelfSimilar G ↔ ∀ g ∈ G, ∀ w : List X, state g w ∈ G :=
  ⟨fun hG _ hg w => hG.state_mem hg w, fun h g hg x => h g hg [x]⟩

theorem isSelfSimilar_top : IsSelfSimilar (⊤ : Subgroup (TreeAut X)) :=
  fun _ _ _ => Subgroup.mem_top _

theorem isSelfSimilar_bot : IsSelfSimilar (⊥ : Subgroup (TreeAut X)) := by
  intro g hg x
  rw [Subgroup.mem_bot] at hg ⊢
  rw [hg, state_one]

theorem IsSelfSimilar.inf {G H : Subgroup (TreeAut X)} (hG : IsSelfSimilar G)
    (hH : IsSelfSimilar H) : IsSelfSimilar (G ⊓ H) :=
  fun g hg x => ⟨hG g hg.1 x, hH g hg.2 x⟩

/-- A faithful self-similar action of an abstract group `Γ` on the tree `X^*`. -/
def IsSelfSimilarRep {Γ : Type*} [Group Γ] (ρ : Γ →* TreeAut X) : Prop :=
  Function.Injective ρ ∧ IsSelfSimilar ρ.range

theorem isSelfSimilar_range_iff {Γ : Type*} [Group Γ] (ρ : Γ →* TreeAut X) :
    IsSelfSimilar ρ.range ↔ ∀ γ : Γ, ∀ x : X, ∃ δ : Γ, state (ρ γ) [x] = ρ δ := by
  constructor
  · intro h γ x
    obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.1 (h (ρ γ) ⟨γ, rfl⟩ x)
    exact ⟨δ, hδ.symm⟩
  · rintro h _ ⟨γ, rfl⟩ x
    obtain ⟨δ, hδ⟩ := h γ x
    exact ⟨δ, hδ.symm⟩

end Trees
end BooneHigman
end GroupApproximation
