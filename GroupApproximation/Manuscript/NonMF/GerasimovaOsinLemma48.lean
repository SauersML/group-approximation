import GroupApproximation.Manuscript.NonMF.GerasimovaOsinCombingConstruction

/-!
# Gerasimova–Osin, Lemma 4.8

Gerasimova–Osin (arXiv:1910.14524v3), §4:

> **Lemma 4.8.** For every `g ∈ G` and `s ∈ S`, we have `C(1,s) ∩ C(s,g) ∩ C(1,g) ≠ ∅`.
>
> *Proof.* … If `s = 1`, then we have `1 ∈ C(1,s) ∩ C(s,g) ∩ C(1,g)`.  Thus, we can
> assume that `s ≠ 1` without loss of generality.  Consider the geodesic triangle `Δ` with
> vertices `1, s, g`, and sides `p = γ_s`, `q = sγ_{s⁻¹g}`, and `r = γ_g`.  To prove the
> lemma it suffices to find a vertex `v ∈ V(p)` such that `v ∈ V(q)Ω² ∩ V(r)Ω²` (25).
> … Proposition 3.6 and inequality (16) imply that `aᵢ` cannot be an isolated
> `H`-component in `Δ`.  … no two distinct `H`-components of a geodesic path in `Γ(G,𝒜)`
> can be connected …  In particular, `aᵢ` cannot be connected to another `H`-component of
> `p` and therefore it is connected to an `H`-component of `q` or `r`.  We consider several
> cases.  **Case 1.** There is `1 ≤ i ≤ n` such that `aᵢ` is connected to an `H`-component
> `c` of `q` and an `H`-component `d` of `r`. … **Case 2.** Suppose that no `aᵢ` is
> connected to `H`-components of both `q` and `r`. … **2.a** … `a₁` is connected to an
> `H`-component `c` of `q`. … **2.b** … `aₙ` is connected to an `H`-component `d` of `r`.
> … **2.c** … `a₁` is connected to an `H`-component of `r` and `aₙ` is connected to an
> `H`-component of `q`.  Then there exists `1 ≤ i < n` such that `aᵢ` is connected to an
> `H`-component `d` of `r` and `aᵢ₊₁` is connected to an `H`-component `c` of `q`. …

## Repository form

* Proposition 3.6 is the projection clause of DGO Proposition 4.14 at `(1,1)` carried by
  `GOSetting.proj`; it bounds any isolated component of a quadrilateral, so the pentagon
  `pᵢ aᵢ p'ᵢ q r⁻¹` is the triangle `p q r⁻¹` itself, and the triangles and pentagons
  closing the connecting edges are quadrilaterals with a short first side.
* A component of a quadrilateral `p ++ q ++ r ++ revWord s` lies in one of the four sides
  (`fourGon_comp_cases`), with its vertex in the coordinates of that side.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 4.1(b)).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u

section Helpers

variable {G : Type u} [Group G]

theorem getElem?_fourGon_p' (p q r s : List (RelLetter G Unit)) {j : ℕ} (hj : j < p.length) :
    (p ++ q ++ r ++ revWord s)[j]? = p[j]? := by
  rw [List.getElem?_append_left (show j < (p ++ q ++ r).length by
      rw [List.length_append, List.length_append]; omega),
    List.getElem?_append_left (show j < (p ++ q).length by
      rw [List.length_append]; omega),
    List.getElem?_append_left hj]

/-- **A component letter of a quadrilateral lies on one of its four sides**, with its
vertex read in the coordinates of that side. -/
theorem fourGon_comp_cases {p q r s : List (RelLetter G Unit)} {j : ℕ} {g : G}
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hread : (p ++ q ++ r ++ revWord s)[j]? = some (RelLetter.comp () g)) :
    (j < p.length ∧ p[j]? = some (RelLetter.comp () g) ∧
        vertex (1 : G) (p ++ q ++ r ++ revWord s) j = vertex (1 : G) p j) ∨
    (∃ m : ℕ, m < q.length ∧ j = p.length + m ∧ q[m]? = some (RelLetter.comp () g) ∧
        vertex (1 : G) (p ++ q ++ r ++ revWord s) j
          = RelLetter.listVal p * vertex (1 : G) q m) ∨
    (∃ m : ℕ, m < r.length ∧ j = p.length + q.length + m ∧
        r[m]? = some (RelLetter.comp () g) ∧
        vertex (1 : G) (p ++ q ++ r ++ revWord s) j
          = RelLetter.listVal p * RelLetter.listVal q * vertex (1 : G) r m) ∨
    (∃ (m : ℕ) (g' : G), m < s.length ∧
        j = p.length + q.length + r.length + (s.length - 1 - m) ∧
        s[m]? = some (RelLetter.comp () g') ∧
        vertex (1 : G) (p ++ q ++ r ++ revWord s) j = vertex (1 : G) s (m + 1)) := by
  have hjlt := (List.getElem?_eq_some_iff.mp hread).1
  rw [length_fourGon] at hjlt
  by_cases h1 : j < p.length
  · refine Or.inl ⟨h1, ?_, vertex_fourGon_first p q r s 1 h1.le⟩
    rw [← getElem?_fourGon_p' p q r s h1]
    exact hread
  by_cases h2 : j < p.length + q.length
  · refine Or.inr (Or.inl ⟨j - p.length, by omega, by omega, ?_, ?_⟩)
    · rw [← getElem?_fourGon_q' p q r s (show j - p.length < q.length by omega),
        show p.length + (j - p.length) = j by omega]
      exact hread
    · have h := vertex_fourGon_side p q r s (1 : G) (show j - p.length ≤ q.length by omega)
      rw [show p.length + (j - p.length) = j by omega, one_mul] at h
      exact h
  by_cases h3 : j < p.length + q.length + r.length
  · refine Or.inr (Or.inr (Or.inl ⟨j - (p.length + q.length), by omega, by omega, ?_, ?_⟩))
    · rw [← getElem?_fourGon_r' p q r s (show j - (p.length + q.length) < r.length by omega),
        show p.length + q.length + (j - (p.length + q.length)) = j by omega]
      exact hread
    · have h := vertex_fourGon_third p q r s (1 : G)
        (show j - (p.length + q.length) ≤ r.length by omega)
      rw [show p.length + q.length + (j - (p.length + q.length)) = j by omega, one_mul] at h
      exact h
  · have hk : j - (p.length + q.length + r.length) < s.length := by omega
    have hs := getElem?_fourGon_s' p q r s hk
    rw [show p.length + q.length + r.length + (j - (p.length + q.length + r.length)) = j
      by omega, hread] at hs
    obtain ⟨g', hg'⟩ := exists_comp_of_invLetter_eq_comp (Option.some.inj hs).symm
    refine Or.inr (Or.inr (Or.inr ⟨s.length - 1 - (j - (p.length + q.length + r.length)), g',
      by omega, by omega, List.getElem?_eq_some_iff.mpr ⟨by omega, hg'⟩, ?_⟩))
    have h := vertex_fourGon_opposite_closed p q r s hclose
      (s.length - 1 - (j - (p.length + q.length + r.length)) + 1)
    rw [show p.length + q.length + r.length +
        (s.length - (s.length - 1 - (j - (p.length + q.length + r.length)) + 1)) = j
      by omega] at h
    exact h

/-- A component letter spans an element of its subgroup. -/
theorem comp_span_mem {D : RelGenSet G Unit} {f : G} {w : List (RelLetter G Unit)}
    (hlet : ∀ a ∈ w, D.IsLetter a) {m : ℕ} {g₁ : G}
    (hm : w[m]? = some (RelLetter.comp () g₁)) :
    (vertex f w m)⁻¹ * vertex f w (m + 1) ∈ D.fam () := by
  rw [vertex_succ_of_getElem? hm, inv_mul_cancel_left]
  exact hlet _ (mem_of_getElem?_eq_some hm)

/-- **No two distinct components of a geodesic word are connected**, on letters. -/
theorem geodesic_comp_not_connected {D : RelGenSet G Unit} {f g : G}
    {w : List (RelLetter G Unit)} (hw : IsGeodesicWord D f g w) {m j : ℕ} {g₁ g₂ : G}
    (hm : w[m]? = some (RelLetter.comp () g₁)) (hj : w[j]? = some (RelLetter.comp () g₂))
    (hne : m ≠ j) (hconn : (vertex f w m)⁻¹ * vertex f w j ∈ D.fam ()) : False := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hjlen : j ≤ w.length := (List.getElem?_eq_some_iff.mp hj).1.le
    have h1 := sub_le_wordDist_vertex D hw m j hlt.le hjlen
    have h2 := wordDist_le_one_of_mem_fam D hconn
    have hj' : j = m + 1 := by omega
    subst hj'
    exact not_consecutive_comp_of_isGeodesicWord hw hm hj
  · have hmlen : m ≤ w.length := (List.getElem?_eq_some_iff.mp hm).1.le
    have hconn' : (vertex f w j)⁻¹ * vertex f w m ∈ D.fam () := by
      have e := inv_mem hconn
      rwa [mul_inv_rev, inv_inv] at e
    have h1 := sub_le_wordDist_vertex D hw j m hlt.le hmlen
    have h2 := wordDist_le_one_of_mem_fam D hconn'
    have hm' : m = j + 1 := by omega
    subst hm'
    exact not_consecutive_comp_of_isGeodesicWord hw hj hm

theorem vertex_take_of_le (w : List (RelLetter G Unit)) (v : G) {k m : ℕ} (hmk : m ≤ k) :
    vertex v (w.take k) m = vertex v w m := by
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take, List.take_take,
    Nat.min_eq_left hmk]

theorem vertex_drop_one (w : List (RelLetter G Unit)) (k m : ℕ) :
    vertex (1 : G) (w.drop k) m = (vertex (1 : G) w k)⁻¹ * vertex (1 : G) w (k + m) :=
  eq_inv_mul_of_mul_eq (vertex_drop_eq w 1 k m)

theorem listVal_take_eq_vertex (w : List (RelLetter G Unit)) (k : ℕ) :
    RelLetter.listVal (w.take k) = vertex (1 : G) w k := by
  rw [vertex_eq_mul_listVal_take, one_mul]

theorem listVal_drop_eq (w : List (RelLetter G Unit)) (k : ℕ) :
    RelLetter.listVal (w.drop k) = (vertex (1 : G) w k)⁻¹ * RelLetter.listVal w := by
  have h := listVal_append (w.take k) (w.drop k)
  rw [List.take_append_drop, listVal_take_eq_vertex] at h
  rw [h, inv_mul_cancel_left]

/-- A geodesic word read from `1` has its component letters in the letters of `D`. -/
theorem getElem?_letter_mem {D : RelGenSet G Unit} {f g : G} {w : List (RelLetter G Unit)}
    (hw : IsGeodesicWord D f g w) {m : ℕ} {g₁ : G}
    (hm : w[m]? = some (RelLetter.comp () g₁)) : g₁ ∈ D.fam () :=
  hw.1 _ (mem_of_getElem?_eq_some hm)

end Helpers

section Triangle

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Finset G} {t : G} {C : ℕ}

/-- **`aᵢ` is connected to an `H`-component of `q` or of `r`.**  The triangle `p q r⁻¹` is
the quadrilateral `p ++ q ++ [] ++ revWord r`; `aᵢ` is deep, so not isolated in it, and it is
connected to no other component of the geodesic `p`. -/
theorem go_triangle_connected (hS : GOSetting D (F : Set G) t C) {s g : G} {fs : List G}
    (hfsF : ∀ f ∈ fs, f ∈ (F : Set G)) (hs : RelLetter.listVal (altWord t fs) = s)
    {i : ℕ} (hi : i < fs.length) :
    (∃ (m : ℕ) (g₁ : G), (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₁) ∧
      (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
        (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∈ D.fam ()) ∨
    (∃ (m : ℕ) (g₁ : G), (goGamma D (F : Set G) t g)[m]? = some (RelLetter.comp () g₁) ∧
      (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
        vertex (1 : G) (goGamma D (F : Set G) t g) (m + 1) ∈ D.fam ()) := by
  have hp : IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t fs) :=
    isGeodesicWord_altWord hS hfsF
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hvalq : RelLetter.listVal (goGamma D (F : Set G) t (s⁻¹ * g)) = s⁻¹ * g := by
    have h := hq.2.1
    rwa [one_mul] at h
  have hvalr : RelLetter.listVal (goGamma D (F : Set G) t g) = g := by
    have h := hr.2.1
    rwa [one_mul] at h
  have hclose : RelLetter.listVal (goGamma D (F : Set G) t g)
      = RelLetter.listVal (altWord t fs) *
        RelLetter.listVal (goGamma D (F : Set G) t (s⁻¹ * g)) *
        RelLetter.listVal ([] : List (RelLetter G Unit)) := by
    rw [hvalr, hs, hvalq, RelLetter.listVal_nil, mul_one, mul_inv_cancel_left]
  have hlet := fourGon_letters (p := altWord t fs) (r := ([] : List (RelLetter G Unit)))
    hS.base_symm hp.1 hq.1 (by simp) hr.1
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_oneOneSides D (altWord t fs)
    (goGamma D (F : Set G) t (s⁻¹ * g)) [] (goGamma D (F : Set G) t g) hlet
    (isOneOneSide_of_isGeodesicWord hp)
    (isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord hq))
    (isOneOneSide_of_length_le_one (by simp))
    (isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord hr)) hclose
  have hplen : (altWord t fs).length = 2 * fs.length := length_altWord t fs
  have hread0 : (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g))[2 * i]? = some (RelLetter.comp () t) := by
    rw [getElem?_fourGon_p' (altWord t fs) (goGamma D (F : Set G) t (s⁻¹ * g)) []
      (goGamma D (F : Set G) t g) (j := 2 * i) (by omega), getElem?_altWord_two_mul hi]
  have hprev : 2 * i = 0 ∨ ∃ x : G, (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g))[2 * i - 1]? = some (RelLetter.base x) := by
    rcases i with _ | i'
    · exact Or.inl rfl
    · have hi' : i' < fs.length := by omega
      refine Or.inr ⟨fs[i'], ?_⟩
      rw [getElem?_fourGon_p' (altWord t fs) (goGamma D (F : Set G) t (s⁻¹ * g)) []
        (goGamma D (F : Set G) t g) (j := 2 * (i' + 1) - 1) (by omega),
        show 2 * (i' + 1) - 1 = 2 * i' + 1 by omega, getElem?_altWord_odd,
        List.getElem?_eq_getElem hi']
      rfl
  have hnext : ∃ x : G, (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g))[2 * i + 1]? = some (RelLetter.base x) := by
    refine ⟨fs[i], ?_⟩
    rw [getElem?_fourGon_p' (altWord t fs) (goGamma D (F : Set G) t (s⁻¹ * g)) []
      (goGamma D (F : Set G) t g) (j := 2 * i + 1) (by omega), getElem?_altWord_odd,
      List.getElem?_eq_getElem hi]
    rfl
  have hcomp := isComp_unit_of_reads hread0 hprev (Or.inr hnext)
  have hv0 : vertex (1 : G) (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g)) (2 * i) = vertex (1 : G) (altWord t fs) (2 * i) :=
    vertex_fourGon_first _ _ _ _ 1 (by omega)
  have hv1 : vertex (1 : G) (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g)) (2 * i + 1)
        = vertex (1 : G) (altWord t fs) (2 * i) * t := by
    rw [vertex_fourGon_first _ _ _ _ 1 (by omega),
      vertex_succ_of_getElem? (getElem?_altWord_two_mul hi)]
    rfl
  have htdeep4 : t ∉ D.relBall () (C * 4) := fun hmem =>
    hS.t_deep (relBall_mono_radius D () (by omega) hmem)
  have hnotiso : ¬ IsIsolated D.fam () 1 (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++
      [] ++ revWord (goGamma D (F : Set G) t g)) (2 * i) := by
    intro hiso
    have hball := hS.proj 4 1 _ hpoly () (2 * i) (2 * i + 1) hcomp hiso
    rw [hv0, hv1, inv_mul_cancel_left] at hball
    exact htdeep4 hball
  obtain ⟨j, hj, hjstart, hjconn⟩ : ∃ j, j ≠ 2 * i ∧
      IsCompStart () (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
        revWord (goGamma D (F : Set G) t g)) j ∧
      Connected D.fam () 1 (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
        revWord (goGamma D (F : Set G) t g)) (2 * i) j := by
    by_contra hcon
    exact hnotiso ⟨⟨2 * i + 1, hcomp⟩, fun j hj hjs hjc => hcon ⟨j, hj, hjs, hjc⟩⟩
  obtain ⟨g₂, hread⟩ := exists_read_of_isCompStart hjstart
  have hc : (vertex (1 : G) (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
      revWord (goGamma D (F : Set G) t g)) (2 * i))⁻¹ *
      vertex (1 : G) (altWord t fs ++ goGamma D (F : Set G) t (s⁻¹ * g) ++ [] ++
        revWord (goGamma D (F : Set G) t g)) j ∈ D.fam () := hjconn
  rw [hv0] at hc
  rcases fourGon_comp_cases hclose hread with ⟨_, hpread, hvj⟩ | ⟨m, _, rfl, hqread, hvj⟩ |
      ⟨m, hm, _, _, _⟩ | ⟨m, g', _, rfl, hrread, hvj⟩
  · exfalso
    rw [hvj] at hc
    exact geodesic_comp_not_connected hp (getElem?_altWord_two_mul hi) hpread
      (fun e => hj e.symm) hc
  · left
    refine ⟨m, g₂, hqread, ?_⟩
    rw [hvj, hs] at hc
    exact hc
  · simp at hm
  · right
    refine ⟨m, g', hrread, ?_⟩
    rw [hvj] at hc
    exact hc

end Triangle

section Closing

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}

theorem next_of_not_comp {w : List (RelLetter G Unit)} {i : ℕ} (hi : i < w.length)
    (hnext : ∀ g₁ : G, w[i + 1]? ≠ some (RelLetter.comp () g₁)) :
    i + 1 = w.length ∨ ∃ x : G, w[i + 1]? = some (RelLetter.base x) := by
  rcases h : w[i + 1]? with _ | a
  · left
    have e := List.getElem?_eq_none_iff.mp h
    omega
  · right
    cases a with
    | base x => exact ⟨x, h⟩
    | comp lam g₁ =>
      cases lam
      exact absurd h (hnext g₁)

theorem prev_of_not_comp {w : List (RelLetter G Unit)} {i : ℕ} (hi : i < w.length)
    (hprev : ∀ g₁ : G, 0 < i → w[i - 1]? ≠ some (RelLetter.comp () g₁)) :
    i = 0 ∨ ∃ x : G, w[i - 1]? = some (RelLetter.base x) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inl h0
  · right
    rcases h : w[i - 1]? with _ | a
    · have e := List.getElem?_eq_none_iff.mp h
      omega
    · cases a with
      | base x => exact ⟨x, h⟩
      | comp lam g₁ =>
        cases lam
        exact absurd h (hprev g₁ hpos)

/-- **A connecting edge closing a quadrilateral is short.**  If the edge `h` is the first
side of `[h] ++ u₁ ++ u₂ ++ revWord u₃` and no component of the other three sides is
connected to it, then `d̂(1,h) ≤ 4C`.  This is the step "`e` is isolated in the geodesic
triangle …; by Proposition 3.6, `d̂(1, Lab(e)) ≤ 3C`" of Lemma 4.8, with the triangle or
pentagon realised as a quadrilateral.  That `h` is a whole component is part of the
conclusion: a subgroup letter next to it would be connected to it. -/
theorem closing_edge_mem_relBall (hS : GOSetting D F t C) {h : G} (hh : h ∈ D.fam ())
    {u₁ u₂ u₃ : List (RelLetter G Unit)}
    (hl₁ : ∀ a ∈ u₁, D.IsLetter a) (hl₂ : ∀ a ∈ u₂, D.IsLetter a)
    (hl₃ : ∀ a ∈ u₃, D.IsLetter a)
    (hs₁ : IsOneOneSide D u₁) (hs₂ : IsOneOneSide D u₂) (hs₃ : IsOneOneSide D u₃)
    (hclose : RelLetter.listVal u₃ = h * RelLetter.listVal u₁ * RelLetter.listVal u₂)
    (h₁ : ∀ (m : ℕ) (g₁ : G), u₁[m]? = some (RelLetter.comp () g₁) →
      h * vertex (1 : G) u₁ m ∉ D.fam ())
    (h₂ : ∀ (m : ℕ) (g₁ : G), u₂[m]? = some (RelLetter.comp () g₁) →
      h * RelLetter.listVal u₁ * vertex (1 : G) u₂ m ∉ D.fam ())
    (h₃ : ∀ (m : ℕ) (g₁ : G), u₃[m]? = some (RelLetter.comp () g₁) →
      vertex (1 : G) u₃ (m + 1) ∉ D.fam ()) :
    h ∈ D.relBall () (C * 4) := by
  have hclose' : RelLetter.listVal u₃ = RelLetter.listVal [RelLetter.comp () h] *
      RelLetter.listVal u₁ * RelLetter.listVal u₂ := by
    rw [hclose, listVal_singleton]
    rfl
  have hlet := fourGon_letters (p := [RelLetter.comp () h]) hS.base_symm
    (fun a ha => by rw [List.mem_singleton.mp ha]; exact hh) hl₁ hl₂ hl₃
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_oneOneSides D [RelLetter.comp () h] u₁ u₂ u₃
    hlet (isOneOneSide_of_length_le_one (by simp)) hs₁ hs₂ hs₃ hclose'
  have hread0 : ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃)[0]?
      = some (RelLetter.comp () h) := by
    first | rfl | simp
  have hlen0 : 0 < ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃).length := by
    rw [length_fourGon]
    simp
  -- the letter after `h` is not a subgroup letter
  have hnext : ∀ g₁ : G,
      ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃)[0 + 1]? ≠ some (RelLetter.comp () g₁) := by
    intro g₁ hg
    rcases fourGon_comp_cases hclose' hg with ⟨hj1, _, _⟩ | ⟨m, _, hm1, hm, _⟩ |
        ⟨m, _, hm1, hm, _⟩ | ⟨m, g', hmlt, hm1, hm, _⟩
    · simp only [List.length_singleton] at hj1
      omega
    · simp only [List.length_singleton] at hm1
      have hm0 : m = 0 := by omega
      rw [hm0] at hm
      apply h₁ 0 g₁ hm
      rw [vertex_zero, mul_one]
      exact hh
    · simp only [List.length_singleton] at hm1
      have hu₁ : u₁ = [] := List.length_eq_zero_iff.mp (by omega)
      have hm0 : m = 0 := by omega
      rw [hm0] at hm
      apply h₂ 0 g₁ hm
      rw [hu₁, vertex_zero, RelLetter.listVal_nil, mul_one, mul_one]
      exact hh
    · simp only [List.length_singleton] at hm1
      have hu₁ : u₁ = [] := List.length_eq_zero_iff.mp (by omega)
      have hu₂ : u₂ = [] := List.length_eq_zero_iff.mp (by omega)
      apply h₃ m g' hm
      rw [show m + 1 = u₃.length by omega, vertex_length, one_mul, hclose, hu₁, hu₂,
        RelLetter.listVal_nil, mul_one, mul_one]
      exact hh
  have hcomp := isComp_unit_of_reads hread0 (Or.inl rfl) (next_of_not_comp hlen0 hnext)
  have hv1 : vertex (1 : G) ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃) 1 = h := by
    have e := vertex_succ_of_getElem? (v := (1 : G)) hread0
    rw [vertex_zero, one_mul] at e
    exact e
  have hiso : IsIsolated D.fam () 1 ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃) 0 := by
    refine ⟨⟨1, hcomp⟩, fun j hj hjs hjc => ?_⟩
    obtain ⟨g₂, hread⟩ := exists_read_of_isCompStart hjs
    have hc : (vertex (1 : G) ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃) 0)⁻¹ *
        vertex (1 : G) ([RelLetter.comp () h] ++ u₁ ++ u₂ ++ revWord u₃) j ∈ D.fam () := hjc
    rw [vertex_zero, inv_one, one_mul] at hc
    rcases fourGon_comp_cases hclose' hread with ⟨hj1, _, _⟩ | ⟨m, _, rfl, hm, hvj⟩ |
        ⟨m, _, rfl, hm, hvj⟩ | ⟨m, g', _, rfl, hm, hvj⟩
    · simp only [List.length_singleton] at hj1
      exact hj (by omega)
    · rw [hvj, listVal_singleton] at hc
      exact h₁ m g₂ hm hc
    · rw [hvj, listVal_singleton] at hc
      exact h₂ m g₂ hm hc
    · rw [hvj] at hc
      exact h₃ m g' hm hc
  have hball := hS.proj 4 1 _ hpoly () 0 1 hcomp hiso
  rwa [vertex_zero, hv1, inv_one, one_mul] at hball

/-- **The connecting edge in the middle of a quadrilateral** `u₀ ++ [h] ++ [] ++ revWord u₃`:
the triangle `pᵢ f⁻¹ r'⁻¹` of Case 1, whose two long sides both start at `1`. -/
theorem middle_edge_mem_relBall (hS : GOSetting D F t C) {h : G} (hh : h ∈ D.fam ())
    {u₀ u₃ : List (RelLetter G Unit)}
    (hl₀ : ∀ a ∈ u₀, D.IsLetter a) (hl₃ : ∀ a ∈ u₃, D.IsLetter a)
    (hs₀ : IsOneOneSide D u₀) (hs₃ : IsOneOneSide D u₃)
    (hclose : RelLetter.listVal u₃ = RelLetter.listVal u₀ * h)
    (h₀ : ∀ (m : ℕ) (g₁ : G), u₀[m]? = some (RelLetter.comp () g₁) →
      (RelLetter.listVal u₀)⁻¹ * vertex (1 : G) u₀ m ∉ D.fam ())
    (h₃ : ∀ (m : ℕ) (g₁ : G), u₃[m]? = some (RelLetter.comp () g₁) →
      (RelLetter.listVal u₀)⁻¹ * vertex (1 : G) u₃ (m + 1) ∉ D.fam ()) :
    h ∈ D.relBall () (C * 4) := by
  have hclose' : RelLetter.listVal u₃ = RelLetter.listVal u₀ *
      RelLetter.listVal [RelLetter.comp () h] *
      RelLetter.listVal ([] : List (RelLetter G Unit)) := by
    rw [hclose, listVal_singleton, RelLetter.listVal_nil, mul_one]
    rfl
  have hlet := fourGon_letters (q := [RelLetter.comp () h])
    (r := ([] : List (RelLetter G Unit))) hS.base_symm hl₀
    (fun a ha => by rw [List.mem_singleton.mp ha]; exact hh) (by simp) hl₃
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_oneOneSides D u₀ [RelLetter.comp () h] [] u₃
    hlet hs₀ (isOneOneSide_of_length_le_one (by simp)) (isOneOneSide_of_length_le_one (by simp))
    hs₃ hclose'
  have hread0 : (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃)[u₀.length]?
      = some (RelLetter.comp () h) := by
    have e := getElem?_fourGon_q' u₀ [RelLetter.comp () h] [] u₃ (i := 0) (by simp)
    rw [Nat.add_zero] at e
    rw [e]
    rfl
  have hlen0 : u₀.length < (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃).length := by
    rw [length_fourGon]
    simp
  have hv0 : vertex (1 : G) (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃) u₀.length
      = RelLetter.listVal u₀ := by
    rw [vertex_fourGon_first u₀ [RelLetter.comp () h] [] u₃ 1 le_rfl, vertex_length, one_mul]
  have hprev : ∀ g₁ : G, 0 < u₀.length →
      (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃)[u₀.length - 1]?
        ≠ some (RelLetter.comp () g₁) := by
    intro g₁ hpos hg
    have hlt : u₀.length - 1 < u₀.length := by omega
    rw [getElem?_fourGon_p' u₀ [RelLetter.comp () h] [] u₃ hlt] at hg
    apply h₀ (u₀.length - 1) g₁ hg
    have hspan := comp_span_mem (f := (1 : G)) hl₀ hg
    rw [show u₀.length - 1 + 1 = u₀.length by omega, vertex_length, one_mul] at hspan
    have e := inv_mem hspan
    rwa [mul_inv_rev, inv_inv] at e
  have hnext : ∀ g₁ : G,
      (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃)[u₀.length + 1]?
        ≠ some (RelLetter.comp () g₁) := by
    intro g₁ hg
    rcases fourGon_comp_cases hclose' hg with ⟨hj1, _, _⟩ | ⟨m, hm0, hm1, _, _⟩ |
        ⟨m, hm0, _, _, _⟩ | ⟨m, g', hmlt, hm1, hm, _⟩
    · omega
    · simp only [List.length_singleton] at hm0
      omega
    · simp at hm0
    · simp only [List.length_singleton, List.length_nil] at hm1
      apply h₃ m g' hm
      rw [show m + 1 = u₃.length by omega, vertex_length, one_mul, hclose, inv_mul_cancel_left]
      exact hh
  have hcomp := isComp_unit_of_reads hread0 (prev_of_not_comp hlen0 hprev)
    (next_of_not_comp hlen0 hnext)
  have hv1 : vertex (1 : G) (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃) (u₀.length + 1)
      = RelLetter.listVal u₀ * h := by
    have e := vertex_succ_of_getElem? (v := (1 : G)) hread0
    rw [hv0] at e
    exact e
  have hiso : IsIsolated D.fam () 1 (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃)
      u₀.length := by
    refine ⟨⟨u₀.length + 1, hcomp⟩, fun j hj hjs hjc => ?_⟩
    obtain ⟨g₂, hread⟩ := exists_read_of_isCompStart hjs
    have hc : (vertex (1 : G) (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃) u₀.length)⁻¹ *
        vertex (1 : G) (u₀ ++ [RelLetter.comp () h] ++ [] ++ revWord u₃) j ∈ D.fam () := hjc
    rw [hv0] at hc
    rcases fourGon_comp_cases hclose' hread with ⟨_, hm, hvj⟩ | ⟨m, hm1, rfl, _, _⟩ |
        ⟨m, hm0, _, _, _⟩ | ⟨m, g', _, rfl, hm, hvj⟩
    · rw [hvj] at hc
      exact h₀ j g₂ hm hc
    · simp only [List.length_singleton] at hm1
      exact hj (by omega)
    · simp at hm0
    · rw [hvj] at hc
      exact h₃ m g' hm hc
  have hball := hS.proj 4 1 _ hpoly () u₀.length (u₀.length + 1) hcomp hiso
  rwa [hv0, hv1, inv_mul_cancel_left] at hball

end Closing

section Cases

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Finset G} {t : G} {C : ℕ}

theorem goGamma_listVal (hS : GOSetting D (F : Set G) t C) (g : G) :
    RelLetter.listVal (goGamma D (F : Set G) t g) = g := by
  have e := (goGamma_isGeodesicWord hS g).2.1
  rwa [one_mul] at e

theorem goGamma_side (hS : GOSetting D (F : Set G) t C) (g : G) :
    IsOneOneSide D (goGamma D (F : Set G) t g) :=
  isOneOneSide_of_isGeodesicWord
    (isGeodesicWord_one_of_isGeodesicWord (goGamma_isGeodesicWord hS g))

theorem geodesic_take {w : List (RelLetter G Unit)} {g' : G} (hw : IsGeodesicWord D 1 g' w)
    {k : ℕ} (hk : k ≤ w.length) : IsGeodesicWord D 1 (vertex (1 : G) w k) (w.take k) := by
  have e := isGeodesicWord_segment D hw (i := 0) (j := k) (Nat.zero_le k) hk
  simpa only [vertex_zero, List.drop_zero, Nat.sub_zero] using e

theorem side_drop {w : List (RelLetter G Unit)} {f g' : G} (hw : IsGeodesicWord D f g' w)
    {k : ℕ} (hk : k ≤ w.length) : IsOneOneSide D (w.drop k) :=
  isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord (geodesic_drop hw hk))

theorem side_take {w : List (RelLetter G Unit)} {g' : G} (hw : IsGeodesicWord D 1 g' w)
    {k : ℕ} (hk : k ≤ w.length) : IsOneOneSide D (w.take k) :=
  isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord (geodesic_take hw hk))

/-- A component of the part of a geodesic after a component `c` is not connected to `c`,
read at the ends of the components. -/
theorem geodesic_drop_comp_not_connected {w : List (RelLetter G Unit)} {g' : G}
    (hw : IsGeodesicWord D 1 g' w) {m : ℕ} {g₁ : G}
    (hm : w[m]? = some (RelLetter.comp () g₁)) {k : ℕ} {g₂ : G}
    (hk : (w.drop (m + 1))[k]? = some (RelLetter.comp () g₂))
    (hmem : vertex (1 : G) (w.drop (m + 1)) (k + 1) ∈ D.fam ()) : False := by
  rw [List.getElem?_drop] at hk
  rw [vertex_drop_one] at hmem
  apply geodesic_comp_not_connected hw hm hk (by omega)
  have e : (vertex (1 : G) w m)⁻¹ * vertex (1 : G) w (m + 1 + k)
      = ((vertex (1 : G) w m)⁻¹ * vertex (1 : G) w (m + 1)) *
        ((vertex (1 : G) w (m + 1))⁻¹ * vertex (1 : G) w (m + 1 + (k + 1))) *
        ((vertex (1 : G) w (m + 1 + k))⁻¹ * vertex (1 : G) w (m + 1 + k + 1))⁻¹ := by
    rw [show m + 1 + (k + 1) = m + 1 + k + 1 by omega]
    group
  rw [e]
  exact mul_mem (mul_mem (comp_span_mem hw.1 hm) hmem) (inv_mem (comp_span_mem hw.1 hk))

/-- **Case 2.a**: `a₁` is connected to a component `c` of `q` and to none of `r`; the edge
`e` from `c₊` to `(a₁)₋ = 1` is short. -/
theorem go_case2a (hS : GOSetting D (F : Set G) t C) {s g : G} {m : ℕ} {g₁ : G}
    (hqm : (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₁))
    (hconn : s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m ∈ D.fam ())
    (hnotr : ∀ (k : ℕ) (g₂ : G),
      (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₂) →
      vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∉ D.fam ()) :
    (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹
      ∈ D.relBall () (C * 4) := by
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hm1 : m + 1 ≤ (goGamma D (F : Set G) t (s⁻¹ * g)).length :=
    (List.getElem?_eq_some_iff.mp hqm).1
  have hmem1 : s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1) ∈ D.fam () := by
    have e : s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1)
        = (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) *
          ((vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1)) := by group
    rw [e]
    exact mul_mem hconn (comp_span_mem hq.1 hqm)
  refine closing_edge_mem_relBall hS (inv_mem hmem1) (u₁ := goGamma D (F : Set G) t g)
    (u₂ := []) (u₃ := (goGamma D (F : Set G) t (s⁻¹ * g)).drop (m + 1)) hr.1 (by simp)
    (fun a ha => hq.1 a (List.mem_of_mem_drop ha)) (goGamma_side hS g)
    (isOneOneSide_of_length_le_one (by simp)) (side_drop hq hm1) ?_ ?_
    (fun k g₂ hk => by simp at hk) ?_
  · rw [listVal_drop_eq, goGamma_listVal hS, goGamma_listVal hS, RelLetter.listVal_nil,
      mul_one]
    group
  · intro k g₂ hk hmem
    apply hnotr k g₂ hk
    have e : vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)
        = (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1)) *
          ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) k) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) k)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)) := by group
    rw [e]
    exact mul_mem (mul_mem hmem1 hmem) (comp_span_mem hr.1 hk)
  · intro k g₂ hk hmem
    exact geodesic_drop_comp_not_connected hq hqm hk hmem

/-- **Case 2.b**: `aₙ` (starting at `x`, with `x t fₙ = s`) is connected to a component `d`
of `r` and to none of `q`; the edge `f` from `d₊` to `(aₙ)₊` is short. -/
theorem go_case2b (hS : GOSetting D (F : Set G) t C) {s g x f : G} {k : ℕ} {g₁ : G}
    (hf : f ∈ (F : Set G)) (hxs : x * t * f = s)
    (hrk : (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₁))
    (hconn : x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∈ D.fam ())
    (hnotq : ∀ (m : ℕ) (g₂ : G),
      (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₂) →
      x⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∉ D.fam ()) :
    (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t)
      ∈ D.relBall () (C * 4) := by
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hk1 : k + 1 ≤ (goGamma D (F : Set G) t g).length := (List.getElem?_eq_some_iff.mp hrk).1
  have hh : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) ∈ D.fam () := by
    have e : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t)
        = (x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * t := by group
    rw [e]
    exact mul_mem (inv_mem hconn) hS.t_mem
  refine closing_edge_mem_relBall hS hh (u₁ := [RelLetter.base f])
    (u₂ := goGamma D (F : Set G) t (s⁻¹ * g)) (u₃ := (goGamma D (F : Set G) t g).drop (k + 1))
    (fun a ha => by rw [List.mem_singleton.mp ha]; exact hS.F_base f hf) hq.1
    (fun a ha => hr.1 a (List.mem_of_mem_drop ha)) (isOneOneSide_of_length_le_one (by simp))
    (goGamma_side hS (s⁻¹ * g)) (side_drop hr hk1) ?_
    (fun m g₂ hm => by rcases m with _ | m <;> simp at hm) ?_ ?_
  · rw [listVal_drop_eq, goGamma_listVal hS, goGamma_listVal hS, listVal_singleton, ← hxs]
    simp only [RelLetter.val]
    group
  · intro m g₂ hm hmem
    apply hnotq m g₂ hm
    rw [listVal_singleton] at hmem
    have e : x⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)
        = (x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) *
            (RelLetter.base f : RelLetter G Unit).val *
            vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) := by
      simp only [RelLetter.val]
      rw [← hxs]
      group
    rw [e]
    exact mul_mem hconn hmem
  · intro m g₂ hm hmem
    exact geodesic_drop_comp_not_connected hr hrk hm hmem

/-- **Case 1, the edge `e`**: `aᵢ` is connected to a component `c` of `q`; the edge from
`c₋` to `(aᵢ)₊` is short, by the triangle `p'ᵢ q' e`. -/
theorem go_case1e (hS : GOSetting D (F : Set G) t C) {s g : G} {fs : List G}
    (hfsF : ∀ f ∈ fs, f ∈ (F : Set G)) (hs : RelLetter.listVal (altWord t fs) = s)
    {i : ℕ} (hi : i < fs.length) {m : ℕ} {g₁ : G}
    (hqm : (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₁))
    (hconn : (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
      (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∈ D.fam ()) :
    (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
      (vertex (1 : G) (altWord t fs) (2 * i) * t) ∈ D.relBall () (C * 4) := by
  have hp : IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t fs) :=
    isGeodesicWord_altWord hS hfsF
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hplen := length_altWord t fs
  have hread2i := getElem?_altWord_two_mul (t := t) hi
  have hv1 : vertex (1 : G) (altWord t fs) (2 * i + 1)
      = vertex (1 : G) (altWord t fs) (2 * i) * t := by
    rw [vertex_succ_of_getElem? hread2i]
    rfl
  have hml : m ≤ (goGamma D (F : Set G) t (s⁻¹ * g)).length :=
    (List.getElem?_eq_some_iff.mp hqm).1.le
  have hh : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
      (vertex (1 : G) (altWord t fs) (2 * i) * t) ∈ D.fam () := by
    have e : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
        (vertex (1 : G) (altWord t fs) (2 * i) * t)
        = ((vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
          (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m))⁻¹ * t := by group
    rw [e]
    exact mul_mem (inv_mem hconn) hS.t_mem
  refine closing_edge_mem_relBall hS hh (u₁ := (altWord t fs).drop (2 * i + 1))
    (u₂ := (goGamma D (F : Set G) t (s⁻¹ * g)).take m) (u₃ := [])
    (fun a ha => hp.1 a (List.mem_of_mem_drop ha))
    (fun a ha => hq.1 a (List.mem_of_mem_take ha)) (by simp)
    (side_drop hp (by omega)) (side_take hq hml) (isOneOneSide_of_length_le_one (by simp))
    ?_ ?_ ?_ (fun k g₂ hk => by simp at hk)
  · rw [RelLetter.listVal_nil, listVal_drop_eq, hv1, hs, listVal_take_eq_vertex]
    group
  · intro k g₂ hk hmem
    rw [List.getElem?_drop] at hk
    rw [vertex_drop_one, hv1] at hmem
    apply geodesic_comp_not_connected hp hread2i hk (by omega)
    have e : (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
        vertex (1 : G) (altWord t fs) (2 * i + 1 + k)
        = t * ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
            (vertex (1 : G) (altWord t fs) (2 * i) * t))⁻¹ *
          ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
            (vertex (1 : G) (altWord t fs) (2 * i) * t) *
            ((vertex (1 : G) (altWord t fs) (2 * i) * t)⁻¹ *
              vertex (1 : G) (altWord t fs) (2 * i + 1 + k))) := by group
    rw [e]
    exact mul_mem (mul_mem hS.t_mem (inv_mem hh)) hmem
  · intro k g₂ hk hmem
    have hkm : k < m := by
      have e := (List.getElem?_eq_some_iff.mp hk).1
      simp only [List.length_take] at e
      omega
    rw [List.getElem?_take_of_lt hkm] at hk
    rw [vertex_take_of_le _ _ hkm.le, listVal_drop_eq, hv1, hs] at hmem
    apply geodesic_comp_not_connected hq hqm hk (by omega)
    have e : (vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
        vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) k
        = (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
          (vertex (1 : G) (altWord t fs) (2 * i) * t) *
          ((vertex (1 : G) (altWord t fs) (2 * i) * t)⁻¹ * s) *
          vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) k := by group
    rw [e]
    exact hmem

/-- **Case 1, the edge `f`**: `aᵢ` is connected to a component `d` of `r`; the edge from
`(aᵢ)₋` to `d₋` is short, by the triangle `pᵢ f⁻¹ r'⁻¹`. -/
theorem go_case1f (hS : GOSetting D (F : Set G) t C) {g : G} {fs : List G}
    (hfsF : ∀ f ∈ fs, f ∈ (F : Set G)) {i : ℕ} (hi : i < fs.length) {k : ℕ} {g₁ : G}
    (hrk : (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₁))
    (hconn : (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
      vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∈ D.fam ()) :
    (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) k
      ∈ D.relBall () (C * 4) := by
  have hp : IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t fs) :=
    isGeodesicWord_altWord hS hfsF
  have hr := goGamma_isGeodesicWord hS g
  have hplen := length_altWord t fs
  have hread2i := getElem?_altWord_two_mul (t := t) hi
  have hkl : k ≤ (goGamma D (F : Set G) t g).length := (List.getElem?_eq_some_iff.mp hrk).1.le
  have hh : (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
      vertex (1 : G) (goGamma D (F : Set G) t g) k ∈ D.fam () := by
    have e : (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
        vertex (1 : G) (goGamma D (F : Set G) t g) k
        = ((vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
          vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) k)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ := by group
    rw [e]
    exact mul_mem hconn (inv_mem (comp_span_mem hr.1 hrk))
  refine middle_edge_mem_relBall hS hh (u₀ := (altWord t fs).take (2 * i))
    (u₃ := (goGamma D (F : Set G) t g).take k)
    (fun a ha => hp.1 a (List.mem_of_mem_take ha))
    (fun a ha => hr.1 a (List.mem_of_mem_take ha))
    (side_take hp (by omega)) (side_take hr hkl) ?_ ?_ ?_
  · rw [listVal_take_eq_vertex, listVal_take_eq_vertex]
    group
  · intro m g₂ hm hmem
    have hmi : m < 2 * i := by
      have e := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.length_take] at e
      omega
    rw [List.getElem?_take_of_lt hmi] at hm
    rw [listVal_take_eq_vertex, vertex_take_of_le _ _ hmi.le] at hmem
    exact geodesic_comp_not_connected hp hread2i hm (by omega) hmem
  · intro m g₂ hm hmem
    have hmk : m < k := by
      have e := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.length_take] at e
      omega
    rw [List.getElem?_take_of_lt hmk] at hm
    rw [listVal_take_eq_vertex, vertex_take_of_le _ _ (show m + 1 ≤ k by omega)] at hmem
    apply geodesic_comp_not_connected hr hm hrk (by omega)
    have e : (vertex (1 : G) (goGamma D (F : Set G) t g) m)⁻¹ *
        vertex (1 : G) (goGamma D (F : Set G) t g) k
        = ((vertex (1 : G) (goGamma D (F : Set G) t g) m)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (m + 1)) *
          ((vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (m + 1))⁻¹ *
          ((vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) k)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (comp_span_mem hr.1 hm) (inv_mem hmem)) hconn)
      (inv_mem (comp_span_mem hr.1 hrk))

/-- **Case 2.c, the edge `e`**: `aᵢ` (starting at `x`) is connected to a component `d` of
`r`, `aᵢ₊₁` (starting at `x t fᵢ`) to a component `c` of `q` and to none of `r`; the edge
from `c₊` to `(aᵢ₊₁)₋` is short, by the pentagon `e bᵢ⁻¹ f⁻¹ r' (q')⁻¹`. -/
theorem go_case2ce (hS : GOSetting D (F : Set G) t C) {s g x f : G} {k m : ℕ} {g₁ g₂ : G}
    (hf : f ∈ (F : Set G))
    (hrk : (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₁))
    (hconnr : x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∈ D.fam ())
    (hqm : (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₂))
    (hconnq : (x * t * f)⁻¹ *
      (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∈ D.fam ())
    (hnotr : ∀ (k' : ℕ) (g' : G),
      (goGamma D (F : Set G) t g)[k']? = some (RelLetter.comp () g') →
      (x * t * f)⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k' + 1) ∉ D.fam ()) :
    (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ * (x * t * f)
      ∈ D.relBall () (C * 4) := by
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hk1 : k + 1 ≤ (goGamma D (F : Set G) t g).length := (List.getElem?_eq_some_iff.mp hrk).1
  have hm1 : m + 1 ≤ (goGamma D (F : Set G) t (s⁻¹ * g)).length :=
    (List.getElem?_eq_some_iff.mp hqm).1
  have hfX := hS.F_base f hf
  have hfH := hS.F_not_fam f hf
  have he : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ * (x * t * f)
      ∈ D.fam () := by
    have e : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ * (x * t * f)
        = ((x * t * f)⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) *
          ((vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1)))⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem hconnq (comp_span_mem hq.1 hqm))
  have hhf : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) ∈ D.fam () := by
    have e : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t)
        = (x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * t := by group
    rw [e]
    exact mul_mem (inv_mem hconnr) hS.t_mem
  refine closing_edge_mem_relBall hS he
    (u₁ := [RelLetter.base f⁻¹,
      RelLetter.comp () ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t))⁻¹])
    (u₂ := (goGamma D (F : Set G) t g).drop (k + 1))
    (u₃ := (goGamma D (F : Set G) t (s⁻¹ * g)).drop (m + 1)) ?_
    (fun a ha => hr.1 a (List.mem_of_mem_drop ha))
    (fun a ha => hq.1 a (List.mem_of_mem_drop ha))
    (isOneOneSide_pair _ _ ?_) (side_drop hr hk1) (side_drop hq hm1) ?_ ?_ ?_ ?_
  · intro a ha
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]
      exact hS.base_symm f hfX
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]
      exact inv_mem hhf
    simp at ha
  · intro e
    apply hfH
    have e' : f⁻¹ = ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t))⁻¹⁻¹ :=
      eq_inv_of_mul_eq_one_left e
    rw [inv_inv] at e'
    have hfi : f⁻¹ ∈ D.fam () := by
      rw [e']
      exact hhf
    simpa using inv_mem hfi
  · rw [listVal_drop_eq, listVal_drop_eq, goGamma_listVal hS, goGamma_listVal hS]
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one]
    group
  · intro m' g' hm' hmem
    obtain rfl : m' = 1 := by
      rcases m' with _ | _ | m'' <;> simp at hm' ⊢
    have hv : vertex (1 : G) [RelLetter.base f⁻¹,
        RelLetter.comp () ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ *
          (x * t))⁻¹] 1 = f⁻¹ := by
      show vertex (1 : G) (_ :: _) (0 + 1) = _
      rw [vertex_cons_succ, vertex_zero, one_mul]
      rfl
    rw [hv] at hmem
    apply hfH
    have hfi : f⁻¹ ∈ D.fam () := by
      have e : f⁻¹ = ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
          (x * t * f))⁻¹ *
          ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
            (x * t * f) * f⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem he) hmem
    simpa using inv_mem hfi
  · intro m' g' hm' hmem
    have hk' : (goGamma D (F : Set G) t g)[k + 1 + m']? = some (RelLetter.comp () g') := by
      rwa [List.getElem?_drop] at hm'
    rw [vertex_drop_one] at hmem
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one] at hmem
    apply hnotr (k + 1 + m') g' hk'
    have e : (x * t * f)⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1 + m' + 1)
        = ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
            (x * t * f))⁻¹ *
          ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
            (x * t * f) *
            (f⁻¹ * ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t))⁻¹) *
            ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ *
              vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1 + m'))) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1 + m'))⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1 + m' + 1)) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem he) hmem) (comp_span_mem hr.1 hk')
  · intro m' g' hm' hmem
    exact geodesic_drop_comp_not_connected hq hqm hm' hmem

/-- **Case 2.c, the edge `f`**: as in `go_case2ce`, with `aᵢ` connected to none of `q`; the
edge from `d₊` to `(aᵢ)₊` is short, by the pentagon `f bᵢ e⁻¹ q' (r')⁻¹`. -/
theorem go_case2cf (hS : GOSetting D (F : Set G) t C) {s g x f : G} {k m : ℕ} {g₁ g₂ : G}
    (hf : f ∈ (F : Set G))
    (hrk : (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₁))
    (hconnr : x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∈ D.fam ())
    (hqm : (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₂))
    (hconnq : (x * t * f)⁻¹ *
      (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∈ D.fam ())
    (hnotq : ∀ (m' : ℕ) (g' : G),
      (goGamma D (F : Set G) t (s⁻¹ * g))[m']? = some (RelLetter.comp () g') →
      x⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m') ∉ D.fam ()) :
    (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t)
      ∈ D.relBall () (C * 4) := by
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hk1 : k + 1 ≤ (goGamma D (F : Set G) t g).length := (List.getElem?_eq_some_iff.mp hrk).1
  have hm1 : m + 1 ≤ (goGamma D (F : Set G) t (s⁻¹ * g)).length :=
    (List.getElem?_eq_some_iff.mp hqm).1
  have hfX := hS.F_base f hf
  have hfH := hS.F_not_fam f hf
  have he : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ * (x * t * f)
      ∈ D.fam () := by
    have e : (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ * (x * t * f)
        = ((x * t * f)⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) *
          ((vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m)⁻¹ *
            vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1)))⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem hconnq (comp_span_mem hq.1 hqm))
  have hhf : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) ∈ D.fam () := by
    have e : (vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t)
        = (x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * t := by group
    rw [e]
    exact mul_mem (inv_mem hconnr) hS.t_mem
  refine closing_edge_mem_relBall hS hhf
    (u₁ := [RelLetter.base f,
      RelLetter.comp () ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
        (x * t * f))⁻¹])
    (u₂ := (goGamma D (F : Set G) t (s⁻¹ * g)).drop (m + 1))
    (u₃ := (goGamma D (F : Set G) t g).drop (k + 1)) ?_
    (fun a ha => hq.1 a (List.mem_of_mem_drop ha))
    (fun a ha => hr.1 a (List.mem_of_mem_drop ha))
    (isOneOneSide_pair _ _ ?_) (side_drop hq hm1) (side_drop hr hk1) ?_ ?_ ?_ ?_
  · intro a ha
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]
      exact hfX
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]
      exact inv_mem he
    simp at ha
  · intro e
    apply hfH
    have e' : f = ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
        (x * t * f))⁻¹⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [inv_inv] at e'
    rw [e']
    exact he
  · rw [listVal_drop_eq, listVal_drop_eq, goGamma_listVal hS, goGamma_listVal hS]
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one]
    group
  · intro m' g' hm' hmem
    obtain rfl : m' = 1 := by
      rcases m' with _ | _ | m'' <;> simp at hm' ⊢
    have hv : vertex (1 : G) [RelLetter.base f,
        RelLetter.comp () ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
          (x * t * f))⁻¹] 1 = f := by
      show vertex (1 : G) (_ :: _) (0 + 1) = _
      rw [vertex_cons_succ, vertex_zero, one_mul]
      rfl
    rw [hv] at hmem
    apply hfH
    have e : f = ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t))⁻¹ *
        ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) * f) := by group
    rw [e]
    exact mul_mem (inv_mem hhf) hmem
  · intro m' g' hm' hmem
    have hq' : (goGamma D (F : Set G) t (s⁻¹ * g))[m + 1 + m']? = some (RelLetter.comp () g') := by
      rwa [List.getElem?_drop] at hm'
    rw [vertex_drop_one] at hmem
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one] at hmem
    apply hnotq (m + 1 + m') g' hq'
    have e : x⁻¹ * (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1 + m'))
        = (x⁻¹ * vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1)) *
          ((vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1))⁻¹ * (x * t) *
            (f * ((s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
              (x * t * f))⁻¹) *
            ((vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1))⁻¹ *
              vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) (m + 1 + m'))) := by group
    rw [e]
    exact mul_mem hconnr hmem
  · intro m' g' hm' hmem
    exact geodesic_drop_comp_not_connected hr hrk hm' hmem

end Cases

section Assembly

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Finset G} {t : G} {C : ℕ}
  {hfin : (D.relBall () (5 * C)).Finite}

theorem t_mem_goOmega : t ∈ goOmega D F t C hfin :=
  Finset.mem_insert_self _ _

theorem t_inv_mem_goOmega : t⁻¹ ∈ goOmega D F t C hfin :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem mem_goOmega_of_mem_F {f : G} (hf : f ∈ F) : f ∈ goOmega D F t C hfin :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_union_left _ hf)))

theorem inv_mem_goOmega_of_mem_F {f : G} (hf : f ∈ F) : f⁻¹ ∈ goOmega D F t C hfin :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hf))))

theorem mem_goOmega_of_relBall {x : G} (hx : x ∈ D.relBall () (C * 4)) :
    x ∈ goOmega D F t C hfin :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (hfin.mem_toFinset.mpr (relBall_mono_radius D () (by omega) hx))))

theorem one_mem_goOmega : (1 : G) ∈ goOmega D F t C hfin :=
  mem_goOmega_of_relBall (one_mem_relBall D () (C * 4))

theorem mem_goCone_of_vertex {g x : G} {i : ℕ}
    (hi : i ≤ (goGamma D (F : Set G) t g).length) {ω₁ ω₂ : G}
    (hω₁ : ω₁ ∈ goOmega D F t C hfin) (hω₂ : ω₂ ∈ goOmega D F t C hfin)
    (hx : x = vertex (1 : G) (goGamma D (F : Set G) t g) i * ω₁ * ω₂) :
    x ∈ goCone D F t C hfin g := by
  unfold goCone
  exact ⟨vertex (1 : G) (goGamma D (F : Set G) t g) i, Or.inl ⟨i, hi, rfl⟩, ω₁, hω₁, ω₂, hω₂, hx⟩

theorem mem_goComb_of_vertex {s g x : G} {i : ℕ}
    (hi : i ≤ (goGamma D (F : Set G) t (s⁻¹ * g)).length) {ω₁ ω₂ : G}
    (hω₁ : ω₁ ∈ goOmega D F t C hfin) (hω₂ : ω₂ ∈ goOmega D F t C hfin)
    (hx : x = s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) i * ω₁ * ω₂) :
    x ∈ goComb D F t C hfin s g := by
  unfold goComb
  refine ⟨vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) i * ω₁ * ω₂,
    mem_goCone_of_vertex hi hω₁ hω₂ rfl, ?_⟩
  simp only [hx, mul_assoc]

/-- `aᵢ` is connected to a component of `q`. -/
def goQ (D : RelGenSet G Unit) (F : Finset G) (t s g : G) (fs : List G) (i : ℕ) : Prop :=
  ∃ (m : ℕ) (g₁ : G), (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₁) ∧
    (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
      (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∈ D.fam ()

/-- `aᵢ` is connected to a component of `r`. -/
def goR (D : RelGenSet G Unit) (F : Finset G) (t g : G) (fs : List G) (i : ℕ) : Prop :=
  ∃ (m : ℕ) (g₁ : G), (goGamma D (F : Set G) t g)[m]? = some (RelLetter.comp () g₁) ∧
    (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
      vertex (1 : G) (goGamma D (F : Set G) t g) (m + 1) ∈ D.fam ()

/-- **Gerasimova–Osin, Lemma 4.8**, for `s ∈ S ∖ {1}`. -/
theorem gerasimovaOsinLemma48 (hS : GOSetting D (F : Set G) t C) {s g : G}
    (hsS : ∃ fs : List G, fs ≠ [] ∧ (∀ f ∈ fs, f ∈ (F : Set G)) ∧
      RelLetter.listVal (altWord t fs) = s) :
    (goCone D F t C hfin s ∩ goComb D F t C hfin s g ∩ goCone D F t C hfin g).Nonempty := by
  classical
  obtain ⟨fs, hfsne, hfsF, hs, hγ⟩ := exists_goGamma_eq_altWord (D := D) hsS
  have hn : 0 < fs.length := List.length_pos_iff.mpr hfsne
  have hq := goGamma_isGeodesicWord hS (s⁻¹ * g)
  have hr := goGamma_isGeodesicWord hS g
  have hQR : ∀ i, i < fs.length → goQ D F t s g fs i ∨ goR D F t g fs i :=
    fun i hi => go_triangle_connected hS hfsF hs hi
  have hFf : ∀ i (hi : i < fs.length), fs[i] ∈ F := fun i hi => hfsF _ (List.getElem_mem hi)
  -- a vertex of `p` lies in `C(1,s)`
  have hcone_s : ∀ j, j ≤ 2 * fs.length →
      vertex (1 : G) (altWord t fs) j ∈ goCone D F t C hfin s := by
    intro j hj
    refine mem_goCone_of_vertex (i := j) (by rw [hγ, length_altWord]; exact hj)
      one_mem_goOmega one_mem_goOmega ?_
    rw [hγ, mul_one, mul_one]
  have hendp : vertex (1 : G) (altWord t fs) (2 * fs.length) = s := by
    have e := vertex_length (1 : G) (altWord t fs)
    rwa [length_altWord, one_mul, hs] at e
  by_cases hboth : ∃ i, i < fs.length ∧ goQ D F t s g fs i ∧ goR D F t g fs i
  · -- Case 1
    obtain ⟨i, hi, ⟨m, g₁, hqm, hconnq⟩, ⟨k, g₂, hrk, hconnr⟩⟩ := hboth
    have he := go_case1e hS hfsF hs hi hqm hconnq
    have hf := go_case1f hS hfsF hi hrk hconnr
    refine ⟨vertex (1 : G) (altWord t fs) (2 * i), ⟨hcone_s _ (by omega), ?_⟩, ?_⟩
    · exact mem_goComb_of_vertex (i := m) (List.getElem?_eq_some_iff.mp hqm).1.le
        (mem_goOmega_of_relBall he) t_inv_mem_goOmega (by group)
    · exact mem_goCone_of_vertex (i := k) (List.getElem?_eq_some_iff.mp hrk).1.le
        (mem_goOmega_of_relBall (relBall_inv D () hS.base_symm hf)) one_mem_goOmega (by group)
  by_cases hq0 : goQ D F t s g fs 0
  · -- Case 2.a
    obtain ⟨m, g₁, hqm, hconnq⟩ := hq0
    have hconn : s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m ∈ D.fam () := by
      simpa only [Nat.mul_zero, vertex_zero, inv_one, one_mul] using hconnq
    have hnotr : ∀ (k : ℕ) (g₂ : G),
        (goGamma D (F : Set G) t g)[k]? = some (RelLetter.comp () g₂) →
        vertex (1 : G) (goGamma D (F : Set G) t g) (k + 1) ∉ D.fam () := by
      intro k g₂ hk hmem
      refine hboth ⟨0, hn, ⟨m, g₁, hqm, hconnq⟩, k, g₂, hk, ?_⟩
      simpa only [Nat.mul_zero, vertex_zero, inv_one, one_mul] using hmem
    have he := go_case2a hS hqm hconn hnotr
    refine ⟨1, ⟨?_, ?_⟩, ?_⟩
    · simpa only [vertex_zero] using hcone_s 0 (Nat.zero_le _)
    · exact mem_goComb_of_vertex (i := m + 1) (List.getElem?_eq_some_iff.mp hqm).1
        (mem_goOmega_of_relBall he) one_mem_goOmega (by group)
    · exact mem_goCone_of_vertex (i := 0) (Nat.zero_le _) one_mem_goOmega one_mem_goOmega
        (by rw [vertex_zero, mul_one, mul_one])
  have hr0 : goR D F t g fs 0 := (hQR 0 hn).resolve_left hq0
  have hn1 : fs.length - 1 < fs.length := by omega
  by_cases hrn : goR D F t g fs (fs.length - 1)
  · -- Case 2.b
    obtain ⟨k, g₁, hrk, hconnr⟩ := hrn
    have hxs : vertex (1 : G) (altWord t fs) (2 * (fs.length - 1)) * t * fs[fs.length - 1] = s := by
      have e := vertex_altWord_two_mul_succ (1 : G) t fs hn1
      rw [show fs.length - 1 + 1 = fs.length by omega, hendp] at e
      exact e.symm
    have hnotq : ∀ (m : ℕ) (g₂ : G),
        (goGamma D (F : Set G) t (s⁻¹ * g))[m]? = some (RelLetter.comp () g₂) →
        (vertex (1 : G) (altWord t fs) (2 * (fs.length - 1)))⁻¹ *
          (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m) ∉ D.fam () :=
      fun m g₂ hm hmem => hboth ⟨fs.length - 1, hn1, ⟨m, g₂, hm, hmem⟩, k, g₁, hrk, hconnr⟩
    have hf := go_case2b hS (hFf _ hn1) hxs hrk hconnr hnotq
    refine ⟨vertex (1 : G) (altWord t fs) (2 * (fs.length - 1) + 1), ⟨hcone_s _ (by omega), ?_⟩, ?_⟩
    · refine mem_goComb_of_vertex (i := 0) (Nat.zero_le _) (inv_mem_goOmega_of_mem_F (hFf _ hn1))
        one_mem_goOmega ?_
      rw [vertex_succ_of_getElem? (getElem?_altWord_two_mul hn1), vertex_zero, mul_one, mul_one,
        ← hxs]
      simp only [RelLetter.val]
      group
    · refine mem_goCone_of_vertex (i := k + 1) (List.getElem?_eq_some_iff.mp hrk).1
        (mem_goOmega_of_relBall hf) one_mem_goOmega ?_
      rw [vertex_succ_of_getElem? (getElem?_altWord_two_mul hn1), mul_one]
      simp only [RelLetter.val]
      group
  -- Case 2.c
  have hqn : goQ D F t s g fs (fs.length - 1) := (hQR _ hn1).resolve_right hrn
  have hex : ∃ j, j < fs.length ∧ goQ D F t s g fs j := ⟨fs.length - 1, hn1, hqn⟩
  obtain ⟨j₀, hj₀, hmin⟩ : ∃ j₀, (j₀ < fs.length ∧ goQ D F t s g fs j₀) ∧
      ∀ j, j < j₀ → ¬ (j < fs.length ∧ goQ D F t s g fs j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hj₀0 : j₀ ≠ 0 := by
    intro e
    rw [e] at hj₀
    exact hq0 hj₀.2
  have hi : j₀ - 1 < fs.length := by omega
  have hnotqi : ¬ goQ D F t s g fs (j₀ - 1) := fun h => hmin (j₀ - 1) (by omega) ⟨hi, h⟩
  have hri : goR D F t g fs (j₀ - 1) := (hQR _ hi).resolve_left hnotqi
  have hj₀eq : j₀ - 1 + 1 = j₀ := by omega
  obtain ⟨k, g₁, hrk, hconnr⟩ := hri
  have hqj := hj₀.2
  rw [← hj₀eq] at hqj
  obtain ⟨m, g₂, hqm, hconnq⟩ := hqj
  have hstep := vertex_altWord_two_mul_succ (1 : G) t fs hi
  rw [hstep] at hconnq
  have hnotr' : ∀ (k' : ℕ) (g' : G),
      (goGamma D (F : Set G) t g)[k']? = some (RelLetter.comp () g') →
      (vertex (1 : G) (altWord t fs) (2 * (j₀ - 1)) * t * fs[j₀ - 1])⁻¹ *
        vertex (1 : G) (goGamma D (F : Set G) t g) (k' + 1) ∉ D.fam () := by
    intro k' g' hk' hmem
    refine hboth ⟨j₀, hj₀.1, hj₀.2, k', g', hk', ?_⟩
    rw [← hj₀eq, hstep]
    exact hmem
  have hnotq' : ∀ (m' : ℕ) (g' : G),
      (goGamma D (F : Set G) t (s⁻¹ * g))[m']? = some (RelLetter.comp () g') →
      (vertex (1 : G) (altWord t fs) (2 * (j₀ - 1)))⁻¹ *
        (s * vertex (1 : G) (goGamma D (F : Set G) t (s⁻¹ * g)) m') ∉ D.fam () :=
    fun m' g' hm' hmem => hnotqi ⟨m', g', hm', hmem⟩
  have he := go_case2ce hS (hFf _ hi) hrk hconnr hqm hconnq hnotr'
  have hf := go_case2cf hS (hFf _ hi) hrk hconnr hqm hconnq hnotq'
  refine ⟨vertex (1 : G) (altWord t fs) (2 * (j₀ - 1) + 1), ⟨hcone_s _ (by omega), ?_⟩, ?_⟩
  · refine mem_goComb_of_vertex (i := m + 1) (List.getElem?_eq_some_iff.mp hqm).1
      (mem_goOmega_of_relBall he) (inv_mem_goOmega_of_mem_F (hFf _ hi)) ?_
    rw [vertex_succ_of_getElem? (getElem?_altWord_two_mul hi)]
    simp only [RelLetter.val]
    group
  · refine mem_goCone_of_vertex (i := k + 1) (List.getElem?_eq_some_iff.mp hrk).1
      (mem_goOmega_of_relBall hf) one_mem_goOmega ?_
    rw [vertex_succ_of_getElem? (getElem?_altWord_two_mul hi), mul_one]
    simp only [RelLetter.val]
    group

/-- **Gerasimova–Osin, Lemma 4.8**, for `s = 1`. -/
theorem gerasimovaOsinLemma48_one (hS : GOSetting D (F : Set G) t C) (g : G) :
    (goCone D F t C hfin 1 ∩ goComb D F t C hfin 1 g ∩ goCone D F t C hfin g).Nonempty := by
  refine ⟨1, ⟨?_, ?_⟩, ?_⟩
  · exact mem_goCone_of_vertex (i := 0) (Nat.zero_le _) one_mem_goOmega one_mem_goOmega
      (by rw [vertex_zero, mul_one, mul_one])
  · refine mem_goComb_of_vertex (i := 0) (Nat.zero_le _) one_mem_goOmega one_mem_goOmega ?_
    rw [vertex_zero, mul_one, mul_one, mul_one]
  · exact mem_goCone_of_vertex (i := 0) (Nat.zero_le _) one_mem_goOmega one_mem_goOmega
      (by rw [vertex_zero, mul_one, mul_one])

end Assembly

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation
