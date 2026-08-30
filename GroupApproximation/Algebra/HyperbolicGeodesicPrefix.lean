import GroupApproximation.Algebra.HyperbolicSlimTriangles
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Prefixes of chosen geodesics, and the fellow-travelling they satisfy

This module is the geometric half of "a hyperbolic group is finitely
presented".  It sets up the vocabulary the ladder argument of
`Algebra/HyperbolicFinitePresentation.lean` runs on, and proves the one
inequality that argument needs.

## The vocabulary

For a finite generating set `S`, `Alph S` is its elements read as letters,
`eval` multiplies a positive word over that alphabet in `G`, `toFree` spells it
in `FreeGroup (Alph S)`, and `wordHom S` is the resulting epimorphism onto `G`.
`FreeLen w n` says `w` is spelled by at most `n` letters and inverse letters;
it is the length notion the relator ball is measured in, and it is closed under
multiplication, inversion and `toFree`.

`geo hS g` is a chosen geodesic spelling of `g` over the alphabet, produced from
`Algebra/WordMetricComparison.exists_isGeodesicWord` by lifting a `List G` whose
letters lie in `S` to a `List (Alph S)`.  `geo hS 1 = []`, which is what makes
the telescoping downstream start at the identity.

## The one inequality

The ladder compares the length-`j` prefixes of `geo hS g` and of `geo hS (g*s)`
for a single letter `s`, and needs them to stay a bounded distance apart.  That
looks like it should cost the slim-triangles comparison.  It does not:

> `wordDist_le_of_isBetween`.  If `p` lies between `x` and `y` and `q` lies
> between `x` and `z`, then
> `d(p,q) ≤ |d(x,p) − d(x,q)| + 2 d(y,z) + 2δ`.

The proof is one application of the four-point condition in the Gromov-product
form `Algebra/HyperbolicGroup.isFourPointHyperbolic_iff_gromovProduct` already
supplies, at `x` with the auxiliary point `z`:

* `(q·z)_x = d(x,q)` because `q` lies between `x` and `z`;
* `(p·z)_x ≥ d(x,p) − d(y,z)`, by `d(p,z) ≤ d(p,y) + d(y,z)` and
  `d(x,z) ≥ d(x,y) − d(y,z)`;
* the four-point condition bounds `(p·q)_x` below by the smaller of those, less
  `δ`, and `d(p,q) = d(x,p) + d(x,y) − 2(p·q)_x` is what is left.

Everything is doubled, so no division appears and the arithmetic is `omega`.
`wordDist_prefix_fellow` is the specialisation the ladder uses, at
`d(y,z) ≤ 1` and prefix indices differing by at most one, with the constant
`2δ + 3`.

Slim triangles are not used anywhere in this file, and neither is
`Algebra/HyperbolicSlimFourPoint.lean`; the import of
`Algebra/HyperbolicSlimTriangles.lean` is for `IsBetween` and
`isBetween_of_geodesic_append` alone.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u

/-! ## 0.  Two list lemmas -/

/-- Cutting one more letter off a list splits as a prefix and a single-letter
tail, at every index, including past the end of the list. -/
theorem take_succ_append {α : Type*} (l : List α) (j : ℕ) :
    l.take (j + 1) = l.take j ++ (l.drop j).take 1 := by
  induction j generalizing l with
  | zero => simp
  | succ j ih =>
    cases l with
    | nil => simp
    | cons x t =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
        List.cons.injEq, true_and]
      exact ih t

/-! ## 1.  The alphabet of a finite generating set -/

variable {G : Type u} [Group G]

/-- The elements of a finite generating set, read as letters. -/
abbrev Alph (S : Finset G) : Type u := {x : G // x ∈ S}

/-- The value in `G` of a positive word over the alphabet. -/
def eval {S : Finset G} (l : List (Alph S)) : G := (l.map Subtype.val).prod

@[simp] theorem eval_nil {S : Finset G} : eval ([] : List (Alph S)) = 1 := by
  simp [eval]

theorem eval_append {S : Finset G} (l₁ l₂ : List (Alph S)) :
    eval (l₁ ++ l₂) = eval l₁ * eval l₂ := by
  simp [eval, List.prod_append]

theorem mem_of_mem_map_val {S : Finset G} {l : List (Alph S)} {x : G}
    (hx : x ∈ l.map Subtype.val) : x ∈ (S : Set G) := by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact Finset.mem_coe.mpr a.2

/-- The free word spelled by a positive list. -/
def toFree {A : Type u} (l : List A) : FreeGroup A :=
  FreeGroup.mk (l.map (fun a => (a, true)))

@[simp] theorem toFree_nil {A : Type u} : toFree ([] : List A) = 1 := rfl

theorem toFree_append {A : Type u} (l₁ l₂ : List A) :
    toFree (l₁ ++ l₂) = toFree l₁ * toFree l₂ := by
  simp [toFree]

/-- **The epimorphism spelled by the alphabet.** -/
def wordHom (S : Finset G) : FreeGroup (Alph S) →* G :=
  FreeGroup.lift Subtype.val

theorem wordHom_toFree {S : Finset G} (l : List (Alph S)) :
    wordHom S (toFree l) = eval l := by
  simp [wordHom, toFree, eval, List.map_map, Function.comp_def]

theorem wordHom_surjective {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) :
    Function.Surjective (wordHom S) := by
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff, ← hS.closure_eq, Subgroup.closure_le]
  intro x hx
  exact ⟨FreeGroup.of ⟨x, Finset.mem_coe.mp hx⟩, by simp [wordHom]⟩

/-! ## 2.  Length in the free group -/

/-- `w` is spelled by at most `n` letters and inverse letters. -/
def FreeLen {A : Type u} (w : FreeGroup A) (n : ℕ) : Prop :=
  ∃ l : List (A × Bool), l.length ≤ n ∧ FreeGroup.mk l = w

theorem FreeLen.mono {A : Type u} {w : FreeGroup A} {n m : ℕ} (h : FreeLen w n)
    (hnm : n ≤ m) : FreeLen w m := by
  obtain ⟨l, hl, hw⟩ := h
  exact ⟨l, le_trans hl hnm, hw⟩

theorem freeLen_one {A : Type u} : FreeLen (1 : FreeGroup A) 0 :=
  ⟨[], le_refl 0, rfl⟩

theorem FreeLen.mul {A : Type u} {w₁ w₂ : FreeGroup A} {n₁ n₂ : ℕ}
    (h₁ : FreeLen w₁ n₁) (h₂ : FreeLen w₂ n₂) : FreeLen (w₁ * w₂) (n₁ + n₂) := by
  obtain ⟨l₁, hl₁, rfl⟩ := h₁
  obtain ⟨l₂, hl₂, rfl⟩ := h₂
  refine ⟨l₁ ++ l₂, ?_, FreeGroup.mul_mk.symm⟩
  rw [List.length_append]
  omega

theorem FreeLen.inv {A : Type u} {w : FreeGroup A} {n : ℕ} (h : FreeLen w n) :
    FreeLen w⁻¹ n := by
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨FreeGroup.invRev l, ?_, FreeGroup.inv_mk.symm⟩
  rw [FreeGroup.invRev_length]
  exact hl

theorem freeLen_toFree {A : Type u} (l : List A) : FreeLen (toFree l) l.length :=
  ⟨l.map (fun a => (a, true)), by simp, rfl⟩

/-! ## 3.  The chosen geodesic spelling -/

/-- A list of letters of `S` lifts to a list over the alphabet. -/
theorem exists_list_alph {S : Finset G} :
    ∀ (l : List G), (∀ x ∈ l, x ∈ (S : Set G)) →
      ∃ l' : List (Alph S), l'.map Subtype.val = l
  | [], _ => ⟨[], rfl⟩
  | (x :: t), h => by
      obtain ⟨t', ht'⟩ :=
        exists_list_alph t (fun y hy => h y (List.mem_cons_of_mem _ hy))
      refine ⟨⟨x, Finset.mem_coe.mp (h x (by simp))⟩ :: t', ?_⟩
      simp [ht']

theorem exists_geodesicList {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) :
    ∃ l : List (Alph S), eval l = g ∧ l.length = wordNorm (S : Set G) g := by
  obtain ⟨l, hl⟩ := exists_isGeodesicWord hS g
  obtain ⟨l', hl'⟩ := exists_list_alph l hl.isWord.letters
  refine ⟨l', ?_, ?_⟩
  · show (l'.map Subtype.val).prod = g
    rw [hl', hl.isWord.prod_eq]
  · have h1 : l'.length = l.length := by rw [← hl']; simp
    rw [h1, hl.length_eq]

/-- **The chosen geodesic spelling of an element.** -/
noncomputable def geo {S : Finset G} (hS : IsSymmetricGeneratingSet (S : Set G))
    (g : G) : List (Alph S) := (exists_geodesicList hS g).choose

theorem geo_eval {S : Finset G} (hS : IsSymmetricGeneratingSet (S : Set G))
    (g : G) : eval (geo hS g) = g :=
  (exists_geodesicList hS g).choose_spec.1

theorem geo_length {S : Finset G} (hS : IsSymmetricGeneratingSet (S : Set G))
    (g : G) : (geo hS g).length = wordNorm (S : Set G) g :=
  (exists_geodesicList hS g).choose_spec.2

theorem geo_one {S : Finset G} (hS : IsSymmetricGeneratingSet (S : Set G)) :
    geo hS (1 : G) = [] := by
  have h : (geo hS (1 : G)).length = 0 := by
    rw [geo_length, wordNorm_one]
  cases hc : geo hS (1 : G) with
  | nil => rfl
  | cons x t =>
    rw [hc] at h
    simp at h

theorem geo_isGeodesicWord {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) :
    IsGeodesicWord (S : Set G) ((geo hS g).map Subtype.val) g := by
  refine ⟨⟨fun x hx => mem_of_mem_map_val hx, geo_eval hS g⟩, ?_⟩
  have h1 : ((geo hS g).map Subtype.val).length = (geo hS g).length := by simp
  rw [h1, geo_length]

/-! ## 4.  Prefix points of the chosen geodesic -/

/-- **A prefix of the chosen geodesic lands between the identity and the
element**, at the distance its length prescribes. -/
theorem isBetween_geo_take {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) (j : ℕ) :
    IsBetween (S : Set G) 1 (eval ((geo hS g).take j)) g ∧
      wordDist (S : Set G) 1 (eval ((geo hS g).take j))
        = min j (wordNorm (S : Set G) g) := by
  have hsplit :
      ((geo hS g).take j).map Subtype.val ++ ((geo hS g).drop j).map Subtype.val
        = (geo hS g).map Subtype.val := by
    rw [← List.map_append, List.take_append_drop]
  have hgeo := geo_isGeodesicWord hS g
  have hprod :
      (((geo hS g).take j).map Subtype.val ++
        ((geo hS g).drop j).map Subtype.val).prod = g := by
    rw [hsplit]
    exact hgeo.isWord.prod_eq
  have hgeo' : IsGeodesicWord (S : Set G)
      (((geo hS g).take j).map Subtype.val ++ ((geo hS g).drop j).map Subtype.val)
      ((((geo hS g).take j).map Subtype.val ++
        ((geo hS g).drop j).map Subtype.val).prod) := by
    rw [hprod, hsplit]
    exact hgeo
  obtain ⟨hb, hd⟩ := isBetween_of_geodesic_append hS 1 hgeo'
  rw [one_mul, one_mul, hprod] at hb
  rw [one_mul] at hd
  have hlen : (((geo hS g).take j).map Subtype.val).length
      = min j (wordNorm (S : Set G) g) := by
    rw [List.length_map, List.length_take, geo_length]
  refine ⟨hb, ?_⟩
  show wordDist (S : Set G) 1 (((geo hS g).take j).map Subtype.val).prod
      = min j (wordNorm (S : Set G) g)
  rw [hd, hlen]

/-! ## 5.  The fellow-travelling inequality -/

/-- **Two points on geodesics out of `x` stay close when their endpoints are
close.**

`d(p,q) ≤ |d(x,p) − d(x,q)| + 2 d(y,z) + 2δ`, written subtraction-free.  One
application of the four-point condition at `x` with auxiliary point `z`; see
the header for the three ingredients. -/
theorem wordDist_le_of_isBetween {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S) (hδ : IsFourPointHyperbolic S δ)
    {x y z p q : G} (hp : IsBetween S x p y) (hq : IsBetween S x q z) :
    wordDist S p q + 2 * min (wordDist S x p) (wordDist S x q)
      ≤ wordDist S x p + wordDist S x q + 2 * wordDist S y z + 2 * δ := by
  have hgp := (isFourPointHyperbolic_iff_gromovProduct hS δ).mp hδ
  have hmain := hgp x p q z
  have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
  have hq' : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have htri1 : wordDist S p z ≤ wordDist S p y + wordDist S y z :=
    wordDist_triangle hS p y z
  have htri2 : wordDist S x y ≤ wordDist S x z + wordDist S z y :=
    wordDist_triangle hS x z y
  have hcomm : wordDist S z y = wordDist S y z := wordDist_comm hS z y
  rcases le_total (twiceGromovProduct S x p z) (twiceGromovProduct S x q z)
    with hm | hm
  · rw [min_eq_left hm] at hmain
    simp only [twiceGromovProduct] at hmain
    rcases le_total (wordDist S x p) (wordDist S x q) with hle | hle
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hle]; omega
  · rw [min_eq_right hm] at hmain
    simp only [twiceGromovProduct] at hmain
    rcases le_total (wordDist S x p) (wordDist S x q) with hle | hle
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hle]; omega

/-- **The prefix form the ladder uses.**  The length-`j` prefixes of the chosen
geodesics to `g` and to `g * s`, for a letter `s`, are `2δ + 3` apart. -/
theorem wordDist_prefix_fellow {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) {δ : ℕ}
    (hδ : IsFourPointHyperbolic (S : Set G) δ) (g s : G)
    (hs : wordNorm (S : Set G) s ≤ 1) (j : ℕ) :
    wordDist (S : Set G) (eval ((geo hS g).take j))
        (eval ((geo hS (g * s)).take j)) ≤ 2 * δ + 3 := by
  obtain ⟨hb₁, hd₁⟩ := isBetween_geo_take hS g j
  obtain ⟨hb₂, hd₂⟩ := isBetween_geo_take hS (g * s) j
  have hyz : wordDist (S : Set G) g (g * s) = wordNorm (S : Set G) s := by
    show wordNorm (S : Set G) (g⁻¹ * (g * s)) = wordNorm (S : Set G) s
    rw [inv_mul_cancel_left]
  have hnorm : wordNorm (S : Set G) (g * s)
      ≤ wordNorm (S : Set G) g + wordNorm (S : Set G) s :=
    wordNorm_mul_le hS g s
  have hnorm' : wordNorm (S : Set G) g
      ≤ wordNorm (S : Set G) (g * s) + wordNorm (S : Set G) s := by
    have h := wordNorm_mul_le hS (g * s) s⁻¹
    rw [mul_inv_cancel_right, wordNorm_inv hS s] at h
    exact h
  have hmain := wordDist_le_of_isBetween hS hδ hb₁ hb₂
  rw [hd₁, hd₂, hyz] at hmain
  rcases le_total (min j (wordNorm (S : Set G) g))
    (min j (wordNorm (S : Set G) (g * s))) with hle | hle
  · rw [min_eq_left hle] at hmain
    have h1 := min_le_left j (wordNorm (S : Set G) g)
    have h2 := min_le_right j (wordNorm (S : Set G) g)
    have h3 := min_le_left j (wordNorm (S : Set G) (g * s))
    have h4 := min_le_right j (wordNorm (S : Set G) (g * s))
    omega
  · rw [min_eq_right hle] at hmain
    have h1 := min_le_left j (wordNorm (S : Set G) g)
    have h2 := min_le_right j (wordNorm (S : Set G) g)
    have h3 := min_le_left j (wordNorm (S : Set G) (g * s))
    have h4 := min_le_right j (wordNorm (S : Set G) (g * s))
    omega

end Hyperbolic
end GroupApproximation
