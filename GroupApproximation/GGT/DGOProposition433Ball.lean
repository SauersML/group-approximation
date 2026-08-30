import GroupApproximation.GGT.DGOIsolatedComponentBoundFourGon
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepCommIndex
import GroupApproximation.GGT.OsinTheorem54SepComponents
import GroupApproximation.GGT.OsinTheorem54SepFourGon
import GroupApproximation.GGT.OsinTheorem54SepFourGonOpposite
import GroupApproximation.GGT.OsinTheorem54SepFourGonPolygon
import GroupApproximation.GGT.OsinTheorem54SepFourGonSide
import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.OsinTheorem54SepReversal

/-!
# The quadrilateral behind Dahmani--Guirardel--Osin's Proposition 4.33

Their Proposition 4.33 says that a hyperbolically embedded family is almost
malnormal: for `lam` and `mu` distinct, `H_lam^g` meets `H_mu` in a set of
bounded `d_lam`-diameter, and the same holds at `lam = mu` for `g` outside
`H_lam`.  Their proof is one geodesic quadrilateral, read against their
Proposition 4.14 --- the isolated-component bound at `n = 4`, which
`DGOIsolatedComponentBoundFourGon.span_mem_relBall_of_sideZero` proves.

This module is that quadrilateral, and the prefix strip its proof opens with.

## The quadrilateral

Let `h` lie in `H_lam` with `k = f⁻¹ h f` in `H_mu`, and let `u` be a geodesic
word for `f`.  Then

    [comp lam h] ++ u ++ [comp mu k⁻¹] ++ revWord u

is a closed path at `1`: its four sides spell `h`, `f`, `k⁻¹` and `f⁻¹`, whose
product is `h f k⁻¹ f⁻¹ = 1`.  Sides `1` and `3` are geodesic, side `2` is a
single letter, and side `0` --- the one-letter `H_lam`-component --- is the
distinguished side, exempt from the quasi-geodesic clause by
Dahmani--Guirardel--Osin's Definition 4.13.  The polygon is taken at `b = 1`,
not `b = 0`, purely so that side `2` needs no hypothesis: a single letter of
value `1` is not a geodesic side, and `k = 1` is not excluded.

If the component at index `0` is isolated, the bound applies and gives
`h ∈ relBall lam (100 (delta + 2))`.

## Why the component is isolated, and what that costs

A component of the polygon connected to the distinguished one has its initial
vertex in `H_lam`, because the distinguished side starts at `1`.  There are
three places such a component can sit.

* Inside `u`.  If the vertex before its letter lies in `H_lam` and the letter is
  a `lam`-letter, the vertex after it lies in `H_lam` too, so it is an alphabet
  letter at distance `i + 1` from `1` along a geodesic: `i + 1 <= 1`, so `i = 0`
  and the offending letter is the *first* letter of `u`.
* At the corner between `u` and the `mu`-letter.  That letter is a `lam`-letter
  only if `mu = lam`, and its vertex is `h f`, which lies in `H_lam` only if `f`
  does.
* Inside `revWord u`.  The mirror computation gives `j <= 1`, and `j = 0` is the
  end of the word, which starts no component; `j = 1` is the *last* letter of
  `revWord u`, which is the inverse of the first letter of `u`.

So exactly two hypotheses close the argument: `u` does not begin with a
`lam`-letter, and not both `mu = lam` and `f ∈ H_lam`.  The first is not
cosmetic.  With a leading `lam`-letter the component genuinely fails to be
isolated, and at `f ∈ H_lam` with `mu = lam` the conclusion itself is false:
`H_lam^f ∩ H_lam = H_lam` there, which is unbounded in `d_lam` whenever `H_lam`
is.  A ball statement measured through an arbitrary conjugator is not available,
and none is claimed here.

## The prefix strip

`exists_strip_fam_prefix` is the paper's own first move, which is what makes the
first hypothesis harmless: writing a geodesic word for `g` as `w1 w2` with `w1`
its maximal prefix of `lam`-letters and `f` the element `w2` spells, `g = x f`
with `x ∈ H_lam`, `w2` is again geodesic, and `w2` begins with no `lam`-letter.
Conjugation by `x` carries `H_lam^f ∩ H_mu` onto `H_lam^g ∩ H_mu`, so
*finiteness* transports even though the ball does not.  That is the whole reason
Proposition 4.33 carries no hypothesis on `g` in part (a): the proof replaces
`g`, and measures the diameter through the reduced conjugator.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Stripping the maximal prefix of component letters -/

/-- **Dahmani--Guirardel--Osin's reduction, Proposition 4.33, first move.**

Every geodesic word splits as a maximal prefix of `lam`-letters followed by a
geodesic word beginning with none, and the prefix contributes a factor of
`H_lam` on the left.  Both halves of the conclusion are needed: the factor `x`
is what transports finiteness back, and the missing leading letter is what makes
the quadrilateral's component isolated. -/
theorem exists_strip_fam_prefix (D : RelGenSet G Λ) (lam : Λ) :
    ∀ (w : List (RelLetter G Λ)) (g : G), IsGeodesicWord D 1 g w →
      ∃ (x f : G) (v : List (RelLetter G Λ)), x ∈ D.fam lam ∧ g = x * f ∧
        IsGeodesicWord D 1 f v ∧
        ∀ hv : 0 < v.length, ¬ (v[0]'hv).IsCompOf lam := by
  intro w
  induction w with
  | nil =>
      intro g hg
      have hg1 : g = 1 := by
        have hstep := hg.2.1
        rw [RelLetter.listVal_nil, mul_one] at hstep
        exact hstep.symm
      refine ⟨1, 1, [], one_mem _, by rw [hg1, mul_one], ⟨?_, ?_, ?_⟩, ?_⟩
      · intro a ha
        simp at ha
      · rw [RelLetter.listVal_nil, mul_one]
      · rw [List.length_nil, wordDist_self]
      · intro hv
        simp at hv
  | cons a t ih =>
      intro g hg
      by_cases hac : a.IsCompOf lam
      · have ha : D.IsLetter a := hg.1 a List.mem_cons_self
        have haf : a.val ∈ D.fam lam := val_mem_fam_of_isCompOf D ha hac
        have hlett : ∀ c ∈ t, D.IsLetter c := fun c hc =>
          hg.1 c (List.mem_cons_of_mem _ hc)
        have hval : RelLetter.listVal t = a.val⁻¹ * g := by
          have hstep := hg.2.1
          rw [listVal_cons, one_mul] at hstep
          rw [← hstep]
          group
        have hlen : t.length = wordDist D.alphabet.carrier 1 (a.val⁻¹ * g) := by
          have hgl : (a :: t).length = wordDist D.alphabet.carrier 1 g := hg.2.2
          rw [List.length_cons] at hgl
          have hle : wordNorm D.alphabet.carrier (a.val⁻¹ * g) ≤ t.length := by
            have hstep := wordNorm_listVal_le D t hlett
            rwa [hval] at hstep
          have hone : wordNorm D.alphabet.carrier a.val ≤ 1 :=
            wordNorm_le_one_of_mem (val_mem_alphabet D ha)
          have hsplit : wordNorm D.alphabet.carrier g
              ≤ wordNorm D.alphabet.carrier a.val
                + wordNorm D.alphabet.carrier (a.val⁻¹ * g) := by
            have he : a.val * (a.val⁻¹ * g) = g := by group
            have hstep := wordNorm_mul_le D.alphabet.symmetricGenerating a.val
              (a.val⁻¹ * g)
            rwa [he] at hstep
          rw [wordDist_one_left] at hgl ⊢
          omega
        obtain ⟨x, f, v, hx, hgxf, hgeo, hfst⟩ :=
          ih (a.val⁻¹ * g) ⟨hlett, by rw [one_mul, hval], hlen⟩
        refine ⟨a.val * x, f, v, mul_mem haf hx, ?_, hgeo, hfst⟩
        rw [mul_assoc, ← hgxf]
        group
      · refine ⟨1, g, a :: t, one_mem _, (one_mul g).symm, hg, ?_⟩
        intro hv
        rw [List.getElem_cons_zero]
        exact hac

/-! ## The quadrilateral -/

/-- **Dahmani--Guirardel--Osin's Proposition 4.33, ball form, at a geodesic word
with no leading `lam`-letter.**

`h ∈ H_lam` conjugated by `f` into `H_mu` lies in the `d_lam`-ball of radius
`100 (delta + 2)`, provided some geodesic word for `f` does not begin with a
`lam`-letter and `f` does not lie in `H_lam` when `mu = lam`.

Both hypotheses are necessary, not artefacts: see the module docstring. -/
theorem span_mem_relBall_of_geodesicWord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {lam mu : Λ} {f h : G} {u : List (RelLetter G Λ)}
    (hu : IsGeodesicWord D 1 f u)
    (hfst : ∀ hlen : 0 < u.length, ¬ (u[0]'hlen).IsCompOf lam)
    (hmid : ¬ (mu = lam ∧ f ∈ D.fam lam))
    (hh : h ∈ D.fam lam) (hk : f⁻¹ * h * f ∈ D.fam mu) :
    h ∈ D.relBall lam (100 * (δ + 2)) := by
  obtain ⟨p, hp⟩ : ∃ p : List (RelLetter G Λ), p = [RelLetter.comp lam h] :=
    ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : List (RelLetter G Λ),
      r = [RelLetter.comp mu (f⁻¹ * h⁻¹ * f)] := ⟨_, rfl⟩
  have hkinv : f⁻¹ * h⁻¹ * f ∈ D.fam mu := by
    have hinv := inv_mem hk
    have he : (f⁻¹ * h * f)⁻¹ = f⁻¹ * h⁻¹ * f := by group
    rwa [he] at hinv
  have hp1 : p.length = 1 := by simp [hp]
  have hr1 : r.length = 1 := by simp [hr]
  have hpval : RelLetter.listVal p = h := by
    rw [hp]
    exact listVal_singleton _
  have hrval : RelLetter.listVal r = f⁻¹ * h⁻¹ * f := by
    rw [hr]
    exact listVal_singleton _
  have huval : RelLetter.listVal u = f := by
    have hstep := hu.2.1
    rw [one_mul] at hstep
    exact hstep
  have hclose : RelLetter.listVal u
      = RelLetter.listVal p * RelLetter.listVal u * RelLetter.listVal r := by
    rw [hpval, hrval, huval]
    group
  have hlet : ∀ a ∈ p ++ u ++ r ++ revWord u, D.IsLetter a := by
    intro a ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · rcases List.mem_append.mp ha'' with ha3 | ha3
        · rw [hp] at ha3
          rw [List.eq_of_mem_singleton ha3]
          exact hh
        · exact hu.1 a ha3
      · rw [hr] at ha''
        rw [List.eq_of_mem_singleton ha'']
        exact hkinv
    · exact isLetter_of_mem_revWord D hsymm hu.1 a ha'
  have hclosed : RelLetter.listVal (p ++ u ++ r ++ revWord u) = 1 :=
    listVal_fourGon_eq_one p u r u hclose
  have hlenW := length_fourGon p u r u
  have hW1 : 1 < (p ++ u ++ r ++ revWord u).length := by omega
  -- the corner where the geodesic side meets the `mu`-letter
  have hcorner : ∀ n : ℕ, n = p.length + u.length →
      ∀ hn : n < (p ++ u ++ r ++ revWord u).length,
        vertex (1 : G) (p ++ u ++ r ++ revWord u) n ∈ D.fam lam →
          ((p ++ u ++ r ++ revWord u)[n]'hn).IsCompOf lam → False := by
    intro n hne hn hvc hcc
    subst hne
    have hmem := getElem_mem_fourGon_r p u r u (by omega) (by omega) hn
    have hmemeq := List.eq_of_mem_singleton
      (show _ ∈ [RelLetter.comp mu (f⁻¹ * h⁻¹ * f)] by rw [← hr]; exact hmem)
    rw [hmemeq] at hcc
    rw [vertex_fourGon_side p u r u 1 (le_refl u.length), hpval, one_mul,
      hu.vertex_length_eq] at hvc
    have hstep := mul_mem (inv_mem hh) hvc
    rw [inv_mul_cancel_left] at hstep
    exact hmid ⟨hcc, hstep⟩
  -- the component at index `0` is a component
  have hcomp0 : IsComp lam (p ++ u ++ r ++ revWord u) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj0 hj1 hjlt
      have hj : j = 0 := by omega
      subst hj
      have hmem := getElem_mem_fourGon_p p u r u (by omega) hjlt
      have hmemeq := List.eq_of_mem_singleton
        (show _ ∈ [RelLetter.comp lam h] by rw [← hp]; exact hmem)
      rw [hmemeq]
      rfl
    · intro j hj0 hjlt
      exact absurd hj0 (by omega)
    · intro hk1
      rcases Nat.eq_zero_or_pos u.length with hu0 | hu0
      · have hf1 : f = 1 := by
          have hstep := hu.vertex_length_eq
          rw [hu0, vertex_zero] at hstep
          exact hstep.symm
        have hmem := getElem_mem_fourGon_r p u r u (by omega) (by omega) hk1
        have hmemeq := List.eq_of_mem_singleton
          (show _ ∈ [RelLetter.comp mu (f⁻¹ * h⁻¹ * f)] by rw [← hr]; exact hmem)
        rw [hmemeq]
        intro hcc
        refine hmid ⟨hcc, ?_⟩
        rw [hf1]
        exact one_mem _
      · have hq := getElem_fourGon_q p u r u hu0 (by omega) hk1
        rw [hq]
        exact hfst hu0
  -- and it is isolated
  have hiso : IsIsolated D.fam lam 1 (p ++ u ++ r ++ revWord u) 0 := by
    refine ⟨⟨1, hcomp0⟩, ?_⟩
    intro n hn0 hnstart hconn
    have hv : vertex (1 : G) (p ++ u ++ r ++ revWord u) n ∈ D.fam lam := by
      have hc : (vertex (1 : G) (p ++ u ++ r ++ revWord u) 0)⁻¹ *
          vertex (1 : G) (p ++ u ++ r ++ revWord u) n ∈ D.fam lam := hconn
      rwa [vertex_zero, inv_one, one_mul] at hc
    obtain ⟨hnlt, hncomp⟩ := isCompOf_getElem_of_isCompStart hnstart
    rcases fourGon_index_cases p u r u (le_of_lt hnlt) with
      hc1 | ⟨i, hi, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨j, hj, rfl⟩
    · exact hn0 (by omega)
    · have hvi : vertex (1 : G) u i ∈ D.fam lam := by
        have hv' := hv
        rw [vertex_fourGon_side p u r u 1 hi, hpval, one_mul] at hv'
        have hstep := mul_mem (inv_mem hh) hv'
        rwa [inv_mul_cancel_left] at hstep
      rcases Nat.lt_or_ge i u.length with hlt | hge
      · have hq := getElem_fourGon_q p u r u hlt rfl hnlt
        rw [hq] at hncomp
        have hlet0 : D.IsLetter (u[i]'hlt) := hu.1 _ (List.getElem_mem _)
        have hfam : (u[i]'hlt).val ∈ D.fam lam :=
          val_mem_fam_of_isCompOf D hlet0 hncomp
        have hnext : vertex (1 : G) u (i + 1) ∈ D.fam lam := by
          rw [vertex_succ u 1 i hlt]
          exact mul_mem hvi hfam
        have hone : wordNorm D.alphabet.carrier (vertex (1 : G) u (i + 1)) ≤ 1 :=
          wordNorm_le_one_of_mem (RelGenSet.fam_subset_alphabet D lam hnext)
        have hgeo := sub_le_wordDist_vertex D hu 0 (i + 1) (by omega) (by omega)
        rw [vertex_zero, wordDist_one_left] at hgeo
        have hi0 : i = 0 := by omega
        subst hi0
        exact hfst hlt hncomp
      · have hiq : i = u.length := by omega
        subst hiq
        exact hcorner (p.length + u.length) rfl hnlt hv hncomp
    · exact hcorner (p.length + u.length + m) (by omega) hnlt hv hncomp
    · rw [vertex_fourGon_opposite_closed p u r u hclose j] at hv
      have hone : wordNorm D.alphabet.carrier (vertex (1 : G) u j) ≤ 1 :=
        wordNorm_le_one_of_mem (RelGenSet.fam_subset_alphabet D lam hv)
      have hgeo := sub_le_wordDist_vertex D hu 0 j (by omega) hj
      rw [vertex_zero, wordDist_one_left] at hgeo
      have hje : j = 1 := by omega
      subst hje
      have hmlt : u.length - 1 < (revWord u).length := by
        rw [length_revWord]
        omega
      have hgq := getElem_fourGon_revs p u r u hmlt rfl hnlt
      rw [hgq] at hncomp
      rw [isCompOf_getElem_revWord' u lam (t := 0) hmlt (by omega)
        (by omega)] at hncomp
      exact hfst (by omega) hncomp
  -- the quasi-geodesic clause on the three remaining sides, at `b = 1`
  have hcast : ∀ x y d : ℕ, y - x ≤ d + 1 →
      ((y - x : ℕ) : ℝ) / 1 - ((1 : ℕ) : ℝ) ≤ (d : ℝ) := by
    intro x y d hd
    have h1 : ((y - x : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hd
    rw [div_one, Nat.cast_one]
    linarith
  have hcqg : ∀ t : ℕ, t < 4 → t ≠ 0 → ∀ x y : ℕ,
      fourGonCut p u r u t ≤ x → x ≤ y → y ≤ fourGonCut p u r u (t + 1) →
      ((y - x : ℕ) : ℝ) / 1 - ((1 : ℕ) : ℝ)
        ≤ ((wordDist D.alphabet.carrier
            (vertex (1 : G) (p ++ u ++ r ++ revWord u) x)
            (vertex (1 : G) (p ++ u ++ r ++ revWord u) y) : ℕ) : ℝ) := by
    intro t ht4 ht0 x y hx hxy hy
    have ht : t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases ht with rfl | rfl | rfl
    · have e1 : fourGonCut p u r u 1 = p.length := fourGonCut_one p u r u
      have e2 : fourGonCut p u r u (1 + 1) = p.length + u.length :=
        fourGonCut_two p u r u
      obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i ≤ u.length ∧ x = p.length + i :=
        ⟨x - p.length, by omega, by omega⟩
      obtain ⟨i', hi', rfl⟩ : ∃ i' : ℕ, i' ≤ u.length ∧ y = p.length + i' :=
        ⟨y - p.length, by omega, by omega⟩
      rw [vertex_fourGon_side p u r u 1 hi, vertex_fourGon_side p u r u 1 hi',
        wordDist_left_invariant]
      refine hcast _ _ _ ?_
      have hgeo := sub_le_wordDist_vertex D hu i i' (by omega) hi'
      omega
    · have e2 : fourGonCut p u r u 2 = p.length + u.length :=
        fourGonCut_two p u r u
      have e3 : fourGonCut p u r u (2 + 1) = p.length + u.length + r.length :=
        fourGonCut_three p u r u
      refine hcast _ _ _ ?_
      omega
    · have e3 : fourGonCut p u r u 3 = p.length + u.length + r.length :=
        fourGonCut_three p u r u
      have e4 : fourGonCut p u r u (3 + 1)
          = p.length + u.length + r.length + u.length := fourGonCut_four p u r u
      obtain ⟨jx, hjx, rfl⟩ : ∃ j : ℕ, j ≤ u.length ∧
          x = p.length + u.length + r.length + (u.length - j) :=
        ⟨u.length - (x - (p.length + u.length + r.length)), by omega, by omega⟩
      obtain ⟨jy, hjy, rfl⟩ : ∃ j : ℕ, j ≤ u.length ∧
          y = p.length + u.length + r.length + (u.length - j) :=
        ⟨u.length - (y - (p.length + u.length + r.length)), by omega, by omega⟩
      rw [vertex_fourGon_opposite_closed p u r u hclose jx,
        vertex_fourGon_opposite_closed p u r u hclose jy]
      refine hcast _ _ _ ?_
      have hcomm : wordDist D.alphabet.carrier (vertex (1 : G) u jx)
            (vertex (1 : G) u jy)
          = wordDist D.alphabet.carrier (vertex (1 : G) u jy)
            (vertex (1 : G) u jx) :=
        wordDist_comm D.alphabet.symmetricGenerating _ _
      have hgeo := sub_le_wordDist_vertex D hu jy jx (by omega) hjx
      omega
  -- the base case, and the two rewrites that read its conclusion
  have e0 : fourGonCut p u r u 0 = 0 := fourGonCut_zero p u r u
  have e1 : fourGonCut p u r u 1 = 1 := by
    rw [fourGonCut_one]
    exact hp1
  have hcompc : IsComp lam (p ++ u ++ r ++ revWord u)
      (fourGonCut p u r u 0) (fourGonCut p u r u 1) := by
    rw [e0, e1]
    exact hcomp0
  have hisoc : IsIsolated D.fam lam 1 (p ++ u ++ r ++ revWord u)
      (fourGonCut p u r u 0) := by
    rw [e0]
    exact hiso
  have hv1 : vertex (1 : G) (p ++ u ++ r ++ revWord u) 1 = h := by
    have hstep := vertex_fourGon_side p u r u 1 (Nat.zero_le u.length)
    rw [hpval, vertex_zero, one_mul, mul_one] at hstep
    have hidx : p.length + 0 = 1 := by omega
    rw [hidx] at hstep
    exact hstep
  have hmain := span_mem_relBall_of_sideZero (b := 1) D hsymm hδ 1
    (p ++ u ++ r ++ revWord u) (fourGonCut p u r u) hlet hclosed e0
    (fourGonCut_four_length p u r u) (fourGonCut_mono p u r u) hcqg lam hcompc
    hisoc
  rw [e0, e1, vertex_zero, hv1, inv_one, one_mul] at hmain
  have hrad : 100 * (δ + 1 + 1) = 100 * (δ + 2) := by ring
  rwa [hrad] at hmain

end OsinComponents
end GGT
end GroupApproximation
