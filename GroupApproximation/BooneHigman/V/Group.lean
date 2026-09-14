import GroupApproximation.BooneHigman.V.Cantor
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.IsEmpty.Basic

/-!
# The Higman–Thompson group `V_d` as prefix substitutions

For a finite alphabet `X` with `d` letters, the Higman–Thompson group `V_{d,1}` is the group of
permutations of `Cantor X` that cut the boundary into finitely many cones and move each cone onto a cone
by a prefix substitution `w y ↦ v y`.  Refining every cone to a common depth, such a permutation is one
with `HasDepth f N` for some `N`: every cone of depth `N` is carried onto a cone by a prefix substitution.

* `MapsCone f w v` says that `f (w y) = v y` for every stream `y`;
* `HasDepth f N` holds when every cone of depth `N` is carried onto some cone by a prefix substitution;
  it is monotone in `N`, the depth of a product is at most the sum of the depths, and an inverse has a
  depth (`HasDepth.exists_inv`, which uses that `X` is finite);
* `higmanThompsonV X` is the subgroup of those permutations;
* `localize w : Equiv.Perm (Cantor X) →* Equiv.Perm (Cantor X)` is the action of a permutation inside the
  cone of `w` (`w y ↦ w (g y)`, identity elsewhere), an injective homomorphism that preserves `V`.

For `X = Fin 2` the definitions are those of `Leavitt/FamilyVEmbedding.lean` (`ThompsonV.HasDepth`,
`ThompsonV.tableGroup`) with the letter type generalized.
-/

namespace GroupApproximation
namespace BooneHigman

variable {X : Type*}

/-! ### Prefix substitutions -/

/-- `f` carries the cone of `w` onto the cone of `v` by substituting the prefix `w` by `v`. -/
def MapsCone (f : Equiv.Perm (Cantor X)) (w v : List X) : Prop :=
  ∀ x : Cantor X, f (prepend w x) = prepend v x

theorem MapsCone.unique [Nontrivial X] {f : Equiv.Perm (Cantor X)} {w v v' : List X}
    (h : MapsCone f w v) (h' : MapsCone f w v') : v = v' :=
  prepend_injective_word fun x ↦ (h x).symm.trans (h' x)

theorem MapsCone.append {f : Equiv.Perm (Cantor X)} {w v : List X} (h : MapsCone f w v)
    (c : List X) : MapsCone f (w ++ c) (v ++ c) := by
  intro x
  rw [prepend_append, h, prepend_append]

theorem MapsCone.inv {f : Equiv.Perm (Cantor X)} {w v : List X} (h : MapsCone f w v) :
    MapsCone f⁻¹ v w := by
  intro x
  conv_lhs => rw [← h x]
  simp

theorem MapsCone.comp {f g : Equiv.Perm (Cantor X)} {u v z : List X} (hg : MapsCone g u v)
    (hf : MapsCone f v z) : MapsCone (f * g) u z := by
  intro x
  rw [Equiv.Perm.mul_apply, hg, hf]

@[simp] theorem mapsCone_one (w : List X) : MapsCone (1 : Equiv.Perm (Cantor X)) w w :=
  fun _ ↦ rfl

/-- A permutation carrying a cone onto a cone carries the image of the cone onto the cone. -/
theorem MapsCone.image_cone {f : Equiv.Perm (Cantor X)} {w v : List X} (h : MapsCone f w v) :
    f '' cone w = cone v := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hy
    rw [h z]
    exact prepend_mem_cone v z
  · intro hx
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hx
    exact ⟨prepend w z, prepend_mem_cone w z, h z⟩

/-! ### Depth -/

/-- `f` acts as a prefix substitution on every cone of depth `N`. -/
def HasDepth (f : Equiv.Perm (Cantor X)) (N : ℕ) : Prop :=
  ∀ w : List X, w.length = N → ∃ v, MapsCone f w v

/-- The identity has every depth: the satisfiability witness for `HasDepth`. -/
theorem hasDepth_one (N : ℕ) : HasDepth (1 : Equiv.Perm (Cantor X)) N :=
  fun w _ ↦ ⟨w, mapsCone_one w⟩

open Classical in
/-- The image word of a cone under a prefix substitution. -/
noncomputable def coneTarget (f : Equiv.Perm (Cantor X)) (w : List X) : List X :=
  if h : ∃ v, MapsCone f w v then h.choose else []

theorem mapsCone_coneTarget {f : Equiv.Perm (Cantor X)} {w : List X}
    (h : ∃ v, MapsCone f w v) : MapsCone f w (coneTarget f w) := by
  rw [coneTarget, dif_pos h]
  exact h.choose_spec

/-- A depth-`N` table refines to a depth-`M` table for every `M ≥ N`. -/
theorem HasDepth.mono {f : Equiv.Perm (Cantor X)} {N M : ℕ} (h : HasDepth f N) (hNM : N ≤ M) :
    HasDepth f M := by
  intro w hw
  obtain ⟨v, hv⟩ := h (w.take N) (by simp only [List.length_take, hw]; omega)
  refine ⟨v ++ w.drop N, ?_⟩
  have h' := hv.append (w.drop N)
  rwa [List.take_append_drop] at h'

theorem HasDepth.mul {f g : Equiv.Perm (Cantor X)} {N M : ℕ} (hf : HasDepth f N)
    (hg : HasDepth g M) : HasDepth (f * g) (M + N) := by
  intro u hu
  obtain ⟨v, hv⟩ := hg (u.take M) (by simp only [List.length_take, hu]; omega)
  have hgu : MapsCone g u (v ++ u.drop M) := by
    have h' := hv.append (u.drop M)
    rwa [List.take_append_drop] at h'
  have hzlen : N ≤ (v ++ u.drop M).length := by
    simp only [List.length_append, List.length_drop, hu]
    omega
  obtain ⟨y, hy⟩ := hf ((v ++ u.drop M).take N) (by simp only [List.length_take]; omega)
  have hfz : MapsCone f (v ++ u.drop M) (y ++ (v ++ u.drop M).drop N) := by
    have h' := hy.append ((v ++ u.drop M).drop N)
    rwa [List.take_append_drop] at h'
  exact ⟨_, hgu.comp hfz⟩

/-- The inverse of a permutation with a depth has a depth: its depth is the longest target word of
the depth-`N` cones, of which there are finitely many. -/
theorem HasDepth.exists_inv [Finite X] {f : Equiv.Perm (Cantor X)} {N : ℕ} (h : HasDepth f N) :
    ∃ M, HasDepth f⁻¹ M := by
  classical
  have : Fintype X := Fintype.ofFinite X
  refine ⟨Finset.univ.sup fun p : Fin N → X ↦ (coneTarget f (List.ofFn p)).length, ?_⟩
  intro u hu
  by_cases hX : IsEmpty X
  · exact ⟨u, fun y ↦ (hX.false (y 0)).elim⟩
  obtain ⟨a⟩ : Nonempty X := not_isEmpty_iff.mp hX
  set x : Cantor X := prepend u (fun _ ↦ a) with hx
  set w : List X := firstWord N (f⁻¹ x) with hw
  have hwlen : w.length = N := length_firstWord N _
  have hmap : MapsCone f w (coneTarget f w) := mapsCone_coneTarget (h w hwlen)
  have hfx : prepend (coneTarget f w) (dropN N (f⁻¹ x)) = x := by
    have hsplit : prepend w (dropN N (f⁻¹ x)) = f⁻¹ x := by
      rw [hw]
      exact prepend_firstWord N (f⁻¹ x)
    have h' := hmap (dropN N (f⁻¹ x))
    rw [hsplit] at h'
    simpa using h'.symm
  have hlen : (coneTarget f w).length ≤ u.length := by
    have hmem : (coneTarget f w).length ≤
        Finset.univ.sup fun p : Fin N → X ↦ (coneTarget f (List.ofFn p)).length :=
      Finset.le_sup (f := fun p : Fin N → X ↦ (coneTarget f (List.ofFn p)).length)
        (Finset.mem_univ fun i : Fin N ↦ (f⁻¹ x) i)
    rw [hu]
    exact hmem
  have hpre : coneTarget f w <+: u :=
    prefix_of_prepend_eq (a := dropN N (f⁻¹ x)) (b := fun _ ↦ a) (by rw [hfx, hx]) hlen
  obtain ⟨c, hc⟩ := hpre
  refine ⟨w ++ c, ?_⟩
  have h' := hmap.inv.append c
  rwa [hc] at h'

/-! ### The group -/

/-- **The Higman–Thompson group `V_{d,1}`** over the alphabet `X` (`d = |X|`): the permutations of the
boundary acting at some depth as prefix substitutions on cones. -/
def higmanThompsonV (X : Type*) [Finite X] : Subgroup (Equiv.Perm (Cantor X)) where
  carrier := {f | ∃ N, HasDepth f N}
  one_mem' := ⟨0, hasDepth_one 0⟩
  mul_mem' := by
    rintro a b ⟨N, hN⟩ ⟨M, hM⟩
    exact ⟨M + N, hN.mul hM⟩
  inv_mem' := by
    rintro a ⟨N, hN⟩
    exact hN.exists_inv

theorem mem_higmanThompsonV [Finite X] {f : Equiv.Perm (Cantor X)} :
    f ∈ higmanThompsonV X ↔ ∃ N, HasDepth f N := Iff.rfl

/-! ### Acting inside a cone -/

open Classical in
/-- The action of a map `g` inside the cone of `w`: `w y ↦ w (g y)`, and the identity off the cone. -/
noncomputable def localizeFun (w : List X) (g : Cantor X → Cantor X) (x : Cantor X) : Cantor X :=
  if IsStreamPrefix w x then prepend w (g (dropN w.length x)) else x

theorem localizeFun_prepend (w : List X) (g : Cantor X → Cantor X) (y : Cantor X) :
    localizeFun w g (prepend w y) = prepend w (g y) := by
  rw [localizeFun, if_pos (isStreamPrefix_prepend w y), dropN_prepend]

theorem localizeFun_of_not {w : List X} {x : Cantor X} (hx : ¬ IsStreamPrefix w x)
    (g : Cantor X → Cantor X) : localizeFun w g x = x := by
  rw [localizeFun, if_neg hx]

theorem localizeFun_comp (w : List X) (g h : Cantor X → Cantor X) :
    localizeFun w g ∘ localizeFun w h = localizeFun w (g ∘ h) := by
  funext x
  by_cases hx : IsStreamPrefix w x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hx
    rw [Function.comp_apply, localizeFun_prepend, localizeFun_prepend, localizeFun_prepend,
      Function.comp_apply]
  · rw [Function.comp_apply, localizeFun_of_not hx, localizeFun_of_not hx, localizeFun_of_not hx]

theorem localizeFun_id (w : List X) : localizeFun w (id : Cantor X → Cantor X) = id := by
  funext x
  by_cases hx : IsStreamPrefix w x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hx
    rw [localizeFun_prepend]
    rfl
  · rw [localizeFun_of_not hx]
    rfl

theorem localizeFun_leftInverse (w : List X) (g : Equiv.Perm (Cantor X)) (x : Cantor X) :
    localizeFun w g.symm (localizeFun w g x) = x := by
  have h1 := congrFun (localizeFun_comp w g.symm g) x
  rw [Equiv.symm_comp_self, localizeFun_id] at h1
  exact h1

/-- The action of permutations inside the cone of `w`, as a group homomorphism. -/
noncomputable def localize (w : List X) : Equiv.Perm (Cantor X) →* Equiv.Perm (Cantor X) where
  toFun g :=
    { toFun := localizeFun w g
      invFun := localizeFun w g.symm
      left_inv := localizeFun_leftInverse w g
      right_inv := fun x ↦ by
        have h1 := localizeFun_leftInverse w g.symm x
        rwa [Equiv.symm_symm] at h1 }
  map_one' := Equiv.ext fun x ↦ by
    show localizeFun w (⇑(1 : Equiv.Perm (Cantor X))) x = x
    rw [Equiv.Perm.coe_one]
    exact congrFun (localizeFun_id w) x
  map_mul' g h := Equiv.ext fun x ↦ by
    show localizeFun w (⇑(g * h)) x = localizeFun w g (localizeFun w h x)
    rw [Equiv.Perm.coe_mul]
    exact (congrFun (localizeFun_comp w g h) x).symm

@[simp] theorem localize_apply_prepend (w : List X) (g : Equiv.Perm (Cantor X)) (y : Cantor X) :
    localize w g (prepend w y) = prepend w (g y) :=
  localizeFun_prepend w g y

theorem localize_apply_of_not {w : List X} {x : Cantor X} (hx : ¬ IsStreamPrefix w x)
    (g : Equiv.Perm (Cantor X)) : localize w g x = x :=
  localizeFun_of_not hx g

theorem localize_injective (w : List X) : Function.Injective (localize (X := X) w) := by
  intro g h hgh
  refine Equiv.ext fun y ↦ ?_
  have h1 := congrArg (fun k : Equiv.Perm (Cantor X) ↦ k (prepend w y)) hgh
  simp only [localize_apply_prepend] at h1
  exact prepend_injective w h1

/-- Acting at depth `N` inside the cone of `w` is acting at depth `|w| + N`. -/
theorem HasDepth.localize {g : Equiv.Perm (Cantor X)} {N : ℕ} (h : HasDepth g N) (w : List X) :
    HasDepth (localize w g) (w.length + N) := by
  intro u hu
  by_cases hwu : w <+: u
  · obtain ⟨r, rfl⟩ := hwu
    have hr : r.length = N := by
      simp only [List.length_append] at hu
      omega
    obtain ⟨v, hv⟩ := h r hr
    refine ⟨w ++ v, fun y ↦ ?_⟩
    rw [prepend_append, prepend_append, localize_apply_prepend, hv]
  · refine ⟨u, fun y ↦ localize_apply_of_not (fun hy ↦ hwu ?_) g⟩
    exact prefix_of_isStreamPrefix_of_length_le hy (isStreamPrefix_prepend u y) (by omega)

theorem localize_mem_higmanThompsonV [Finite X] {g : Equiv.Perm (Cantor X)}
    (hg : g ∈ higmanThompsonV X) (w : List X) : localize w g ∈ higmanThompsonV X := by
  obtain ⟨N, hN⟩ := hg
  exact ⟨w.length + N, hN.localize w⟩

end BooneHigman
end GroupApproximation
