import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kac–Moody–Steinberg group `GHB(p)`

Caprace–Conder–Kaluba–Witzel, *Hyperbolic generalized triangle groups, property (T)
and finite simple quotients* (arXiv:2011.09276), Theorem 1.3 and Corollary 7.8:
for every prime `p ≥ 7` the group

```
GHB(p) = ⟨a, b, c | aᵖ, bᵖ, cᵖ, [a,b,a], [a,b,b],
                    [c,b,c], [c,b,b,c], [c,b,b,b], [c,a,c], [c,a,a,c], [c,a,a,a]⟩
```

is an infinite hyperbolic group with property (T).  The commutator convention is
`[x,y] = x⁻¹ y⁻¹ x y`, iterated to the left: `[x,y,z] = [[x,y],z]`.

It is the fundamental group of a triangle of groups whose vertex groups are
`⟨a,b⟩ ≅ U₃(p)` (the Heisenberg group over `F_p`) and `⟨c,b⟩ ≅ ⟨c,a⟩ ≅ U₄(p)`
(the `p`-Sylow subgroup of `Sp₄(F_p)`), with presentations (CCKW Proposition 7.2)

```
U₃(p) = ⟨x, y | xᵖ, yᵖ, [x,y,x], [x,y,y]⟩,
U₄(p) = ⟨x, y | xᵖ, yᵖ, [x,y,x], [x,y,y,x], [x,y,y,y]⟩.
```

This module records the presentations, finite presentation of `GHB(p)`, the
relations among its generators, and the three homomorphisms from `U₃(p)` and
`U₄(p)` onto the vertex subgroups.
-/

namespace GroupApproximation
namespace KMSGroup

/-! ## The commutator convention -/

section Commutators

variable {G H : Type*} [Group G] [Group H]

/-- The commutator convention of Caprace–Conder–Kaluba–Witzel: `[x,y] = x⁻¹ y⁻¹ x y`. -/
def comm (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- The left-normed triple commutator `[x,y,z] = [[x,y],z]`. -/
def comm3 (x y z : G) : G := comm (comm x y) z

/-- The left-normed quadruple commutator `[x,y,z,w] = [[[x,y],z],w]`. -/
def comm4 (x y z w : G) : G := comm (comm3 x y z) w

@[simp] theorem map_comm (f : G →* H) (x y : G) : f (comm x y) = comm (f x) (f y) := by
  simp [comm]

@[simp] theorem map_comm3 (f : G →* H) (x y z : G) :
    f (comm3 x y z) = comm3 (f x) (f y) (f z) := by
  simp [comm3]

@[simp] theorem map_comm4 (f : G →* H) (x y z w : G) :
    f (comm4 x y z w) = comm4 (f x) (f y) (f z) (f w) := by
  simp [comm4]

end Commutators

/-! ## The presentation of `GHB(p)` -/

/-- The generator `a` of the free group on three letters. -/
abbrev ga : FreeGroup (Fin 3) := FreeGroup.of 0

/-- The generator `b` of the free group on three letters. -/
abbrev gb : FreeGroup (Fin 3) := FreeGroup.of 1

/-- The generator `c` of the free group on three letters. -/
abbrev gc : FreeGroup (Fin 3) := FreeGroup.of 2

/-- The eleven relators of `GHB(p)`, in the order printed in CCKW Theorem 1.3. -/
def relatorList (p : ℕ) : List (FreeGroup (Fin 3)) :=
  [ga ^ p, gb ^ p, gc ^ p, comm3 ga gb ga, comm3 ga gb gb,
    comm3 gc gb gc, comm4 gc gb gb gc, comm4 gc gb gb gb,
    comm3 gc ga gc, comm4 gc ga ga gc, comm4 gc ga ga ga]

/-- The relator set of `GHB(p)`. -/
abbrev relators (p : ℕ) : Set (FreeGroup (Fin 3)) :=
  ↑(relatorList p).toFinset

/-- **The Kac–Moody–Steinberg group `GHB(p)`** (CCKW Theorem 1.3). -/
abbrev GHB (p : ℕ) : Type := PresentedGroup (relators p)

/-- `GHB(p)` is finitely presented: three generators and eleven relators. -/
instance isFinitelyPresented (p : ℕ) : Group.IsFinitelyPresented (GHB p) := inferInstance

/-- The generator `a` of `GHB(p)`. -/
def a (p : ℕ) : GHB p := PresentedGroup.of 0

/-- The generator `b` of `GHB(p)`. -/
def b (p : ℕ) : GHB p := PresentedGroup.of 1

/-- The generator `c` of `GHB(p)`. -/
def c (p : ℕ) : GHB p := PresentedGroup.of 2

/-- A listed relator is trivial in `GHB(p)`. -/
theorem mk_relator {p : ℕ} {r : FreeGroup (Fin 3)} (hr : r ∈ relatorList p) :
    PresentedGroup.mk (relators p) r = 1 :=
  PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure (by simpa [relators] using hr))

theorem a_pow (p : ℕ) : a p ^ p = 1 := by
  have h := mk_relator (p := p) (r := ga ^ p) (by simp [relatorList])
  rw [map_pow] at h
  exact h

theorem b_pow (p : ℕ) : b p ^ p = 1 := by
  have h := mk_relator (p := p) (r := gb ^ p) (by simp [relatorList])
  rw [map_pow] at h
  exact h

theorem c_pow (p : ℕ) : c p ^ p = 1 := by
  have h := mk_relator (p := p) (r := gc ^ p) (by simp [relatorList])
  rw [map_pow] at h
  exact h

theorem rel_aba (p : ℕ) : comm3 (a p) (b p) (a p) = 1 := by
  have h := mk_relator (p := p) (r := comm3 ga gb ga) (by simp [relatorList])
  rw [map_comm3] at h
  exact h

theorem rel_abb (p : ℕ) : comm3 (a p) (b p) (b p) = 1 := by
  have h := mk_relator (p := p) (r := comm3 ga gb gb) (by simp [relatorList])
  rw [map_comm3] at h
  exact h

theorem rel_cbc (p : ℕ) : comm3 (c p) (b p) (c p) = 1 := by
  have h := mk_relator (p := p) (r := comm3 gc gb gc) (by simp [relatorList])
  rw [map_comm3] at h
  exact h

theorem rel_cbbc (p : ℕ) : comm4 (c p) (b p) (b p) (c p) = 1 := by
  have h := mk_relator (p := p) (r := comm4 gc gb gb gc) (by simp [relatorList])
  rw [map_comm4] at h
  exact h

theorem rel_cbbb (p : ℕ) : comm4 (c p) (b p) (b p) (b p) = 1 := by
  have h := mk_relator (p := p) (r := comm4 gc gb gb gb) (by simp [relatorList])
  rw [map_comm4] at h
  exact h

theorem rel_cac (p : ℕ) : comm3 (c p) (a p) (c p) = 1 := by
  have h := mk_relator (p := p) (r := comm3 gc ga gc) (by simp [relatorList])
  rw [map_comm3] at h
  exact h

theorem rel_caac (p : ℕ) : comm4 (c p) (a p) (a p) (c p) = 1 := by
  have h := mk_relator (p := p) (r := comm4 gc ga ga gc) (by simp [relatorList])
  rw [map_comm4] at h
  exact h

theorem rel_caaa (p : ℕ) : comm4 (c p) (a p) (a p) (a p) = 1 := by
  have h := mk_relator (p := p) (r := comm4 gc ga ga ga) (by simp [relatorList])
  rw [map_comm4] at h
  exact h

/-! ## The vertex groups `U₃(p)` and `U₄(p)` -/

/-- The first generator of the free group on two letters. -/
abbrev gx : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The second generator of the free group on two letters. -/
abbrev gy : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The relators of `U₃(p)` (CCKW Proposition 7.2(i)). -/
def u3RelatorList (p : ℕ) : List (FreeGroup (Fin 2)) :=
  [gx ^ p, gy ^ p, comm3 gx gy gx, comm3 gx gy gy]

/-- The relator set of `U₃(p)`. -/
abbrev u3Relators (p : ℕ) : Set (FreeGroup (Fin 2)) :=
  ↑(u3RelatorList p).toFinset

/-- **`U₃(p)`**, the Heisenberg group over `F_p`, by its presentation. -/
abbrev U3 (p : ℕ) : Type := PresentedGroup (u3Relators p)

/-- The relators of `U₄(p)` (CCKW Proposition 7.2(ii)). -/
def u4RelatorList (p : ℕ) : List (FreeGroup (Fin 2)) :=
  [gx ^ p, gy ^ p, comm3 gx gy gx, comm4 gx gy gy gx, comm4 gx gy gy gy]

/-- The relator set of `U₄(p)`. -/
abbrev u4Relators (p : ℕ) : Set (FreeGroup (Fin 2)) :=
  ↑(u4RelatorList p).toFinset

/-- **`U₄(p)`**, the `p`-Sylow subgroup of `Sp₄(F_p)`, by its presentation. -/
abbrev U4 (p : ℕ) : Type := PresentedGroup (u4Relators p)

/-- `U₃(p)` maps onto the vertex subgroup `⟨a, b⟩`. -/
def u3ToAB (p : ℕ) : U3 p →* GHB p :=
  PresentedGroup.toGroup (f := ![a p, b p]) (by
    intro r hr
    have hr' : r ∈ u3RelatorList p := by simpa [u3Relators] using hr
    simp only [u3RelatorList, List.mem_cons, List.mem_nil_iff, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · simpa using a_pow p
    · simpa using b_pow p
    · simpa using rel_aba p
    · simpa using rel_abb p)

/-- `U₄(p)` maps onto the vertex subgroup `⟨c, b⟩`. -/
def u4ToCB (p : ℕ) : U4 p →* GHB p :=
  PresentedGroup.toGroup (f := ![c p, b p]) (by
    intro r hr
    have hr' : r ∈ u4RelatorList p := by simpa [u4Relators] using hr
    simp only [u4RelatorList, List.mem_cons, List.mem_nil_iff, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · simpa using c_pow p
    · simpa using b_pow p
    · simpa using rel_cbc p
    · simpa using rel_cbbc p
    · simpa using rel_cbbb p)

/-- `U₄(p)` maps onto the vertex subgroup `⟨c, a⟩`. -/
def u4ToCA (p : ℕ) : U4 p →* GHB p :=
  PresentedGroup.toGroup (f := ![c p, a p]) (by
    intro r hr
    have hr' : r ∈ u4RelatorList p := by simpa [u4Relators] using hr
    simp only [u4RelatorList, List.mem_cons, List.mem_nil_iff, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · simpa using c_pow p
    · simpa using a_pow p
    · simpa using rel_cac p
    · simpa using rel_caac p
    · simpa using rel_caaa p)

/-- The image of a homomorphism out of a presented group on two generators is the
subgroup generated by the images of the two generators. -/
theorem range_toGroup_two {rels : Set (FreeGroup (Fin 2))} {G : Type*} [Group G]
    {x y : G} (h : ∀ r ∈ rels, FreeGroup.lift ![x, y] r = 1) :
    (PresentedGroup.toGroup h).range = Subgroup.closure {x, y} := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · left
      simp [PresentedGroup.toGroup.of]
    · right
      simp [PresentedGroup.toGroup.of]
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, rfl⟩, by simp [PresentedGroup.toGroup.of]⟩
    · exact ⟨_, ⟨1, rfl⟩, by simp [PresentedGroup.toGroup.of]⟩

/-- The vertex subgroup `⟨a, b⟩` is the image of `U₃(p)`. -/
theorem range_u3ToAB (p : ℕ) : (u3ToAB p).range = Subgroup.closure {a p, b p} :=
  range_toGroup_two _

/-- The vertex subgroup `⟨c, b⟩` is the image of `U₄(p)`. -/
theorem range_u4ToCB (p : ℕ) : (u4ToCB p).range = Subgroup.closure {c p, b p} :=
  range_toGroup_two _

/-- The vertex subgroup `⟨c, a⟩` is the image of `U₄(p)`. -/
theorem range_u4ToCA (p : ℕ) : (u4ToCA p).range = Subgroup.closure {c p, a p} :=
  range_toGroup_two _

end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.isFinitelyPresented
#audit_axioms GroupApproximation.KMSGroup.rel_caaa
#audit_axioms GroupApproximation.KMSGroup.range_u3ToAB
#audit_axioms GroupApproximation.KMSGroup.range_u4ToCB
#audit_axioms GroupApproximation.KMSGroup.range_u4ToCA
