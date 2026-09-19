import GroupApproximation.CharClass.LerayHirschSquares
import GroupApproximation.CharClass.LerayHirschAlgebra

/-!
# The Leray–Hirsch ladder: the Mayer–Vietoris step

File 3 of the three that prove Leray–Hirsch.  The rows and the squares are in
`LerayHirschSquares`; here the five lemma is applied to them, giving the
inductive step: if `1, ξ, …, ξ^{r-1}` is a basis over each of `U`, `V` and
`U ∩ V`, it is a basis over `U ∪ V`.

## The two cases

The five lemma computes degree `m+1` from the two Mayer–Vietoris sequences
around it, so degree `0` is not one of its cases and is done separately in
`bijective_lhSum_zero`.  That is not a defect of the method: at the left end
both sequences begin, and the argument there is the *four* lemma, which is short
enough to write out.  Injectivity uses only that the pair of restrictions is
injective on the column, which is `MVFacts.exactZero` for the base; surjectivity
matches restrictions and then uses `MVFacts.exactZero` for the total space.

## Main declarations

* `bijective_prodMap` — a product of bijections is a bijection.
* `lhSum_pair`, `lhSum_delta'` — the squares in the exact shape the ladder takes.
* `bijective_lhSum_zero`, `bijective_lhSum_succ` — the two cases.
* `bijective_lhSum` — **the Mayer–Vietoris step of Leray–Hirsch**, in all degrees.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X U V W P UP VP WP : TopCat.{0}}

/-! ## 0. Products -/

theorem prod_eq_zero_iff {M N : Type*} [AddGroup M] [AddGroup N] (a : M) (b : N) :
    ((a, b) : M × N) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem bijective_prodMap {M M' N N' : Type*} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N'] (f : M →+ M') (g : N →+ N')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (f.prodMap g) := by
  constructor
  · intro x y hxy
    have h1 : f x.1 = f y.1 := congrArg Prod.fst hxy
    have h2 : g x.2 = g y.2 := congrArg Prod.snd hxy
    have e1 : x.1 = y.1 := hf.1 h1
    have e2 : x.2 = y.2 := hg.1 h2
    calc x = (x.1, x.2) := rfl
      _ = (y.1, y.2) := by rw [e1, e2]
      _ = y := rfl
  · intro z
    obtain ⟨a, ha⟩ := hf.2 z.1
    obtain ⟨b, hb⟩ := hg.2 z.2
    refine ⟨(a, b), ?_⟩
    calc (f.prodMap g) (a, b) = (f a, g b) := rfl
      _ = (z.1, z.2) := by rw [ha, hb]
      _ = z := rfl

/-! ## 1. The squares in the shape the ladder takes -/

variable {mvX : MVSequence X U V W} {mvP : MVSequence P UP VP WP}

/-- The class on the intersection is the double restriction, and also the
pullback along the composed inclusion.  Both spellings are needed: the ladder's
hypotheses use the first, `lhSum_delta` uses the second. -/
theorem xiW_eq (pP : MVPulls mvP) (ξ : Hmod2 P 2) :
    mvP.resWU 2 (mvP.resU 2 ξ) = pull (pP.jU ≫ pP.iU) 2 ξ := by
  rw [pP.resWU_eq, pP.resU_eq, pull_comp]

/-- **The two restriction squares to the intersection, combined.**  This is the
ladder's outer square, at both ends. -/
theorem lhSum_pair (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (ξ : Hmod2 P 2) (r n : ℕ) (a : lhDomain U r n) (b : lhDomain V r n) :
    lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r n
        (colResWU mvX r n a + colResWV mvX r n b)
      = mvP.resWU n (lhSum L.πU (mvP.resU 2 ξ) r n a)
        + mvP.resWV n (lhSum L.πV (mvP.resV 2 ξ) r n b) := by
  rw [map_add, lhSum_resWU pX pP L, lhSum_resWV pX pP L, ← resW_compat]

/-- **The connecting square**, with the class on the intersection written as the
double restriction. -/
theorem lhSum_delta' (pX : MVPulls mvX) (pP : MVPulls mvP) (L : MVLadder pX pP)
    (hP : MVFacts mvP) (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain W r n) :
    lhSum L.π ξ r (n + 1) (colDelta mvX r n c)
      = mvP.δ n (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r n c) := by
  rw [xiW_eq pP, lhSum_delta pX pP L hP]

/-! ## 2. Degree zero -/

/-- **The four lemma at the left end.**  In degree `0` both Mayer–Vietoris
sequences begin, so the five lemma has no room; the argument is written out. -/
theorem bijective_lhSum_zero (pX : MVPulls mvX) (pP : MVPulls mvP)
    (L : MVLadder pX pP) (hX : MVFacts mvX) (hP : MVFacts mvP) (ξ : Hmod2 P 2)
    (r : ℕ)
    (hU : ∀ n : ℕ, Function.Bijective (lhSum L.πU (mvP.resU 2 ξ) r n))
    (hV : ∀ n : ℕ, Function.Bijective (lhSum L.πV (mvP.resV 2 ξ) r n))
    (hW : ∀ n : ℕ, Function.Bijective (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r n)) :
    Function.Bijective (lhSum L.π ξ r 0) := by
  have key : ∀ c : lhDomain X r 0, lhSum L.π ξ r 0 c = 0 → c = 0 := by
    intro c hc
    have h1 : colResU mvX r 0 c = 0 := by
      apply (hU 0).1
      rw [← lhSum_resU pX pP L, hc, map_zero, map_zero]
    have h2 : colResV mvX r 0 c = 0 := by
      apply (hV 0).1
      rw [← lhSum_resV pX pP L, hc, map_zero, map_zero]
    refine lhDomain_ext fun i => ?_
    have hu := lhDomain_apply_eq h1 i
    have hv := lhDomain_apply_eq h2 i
    rw [colResU_apply, lhDomain_zero_apply] at hu
    rw [colResV_apply, lhDomain_zero_apply] at hv
    rw [lhDomain_zero_apply]
    have he : 0 - 2 * (i : ℕ) = 0 := Nat.zero_sub _
    have h0 : cohCast he
        ((c : (j : Fin r) → Hmod2 X (0 - 2 * (j : ℕ))) i) = 0 :=
      hX.exactZero _ (by rw [resU_cohCast, hu, cohCast_zero])
        (by rw [resV_cohCast, hv, cohCast_zero])
    exact (cohCast_eq_zero_iff _ _).mp h0
  constructor
  · intro c c' h
    have := key (c - c') (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  · intro b
    obtain ⟨a, ha⟩ := (hU 0).2 (mvP.resU 0 b)
    obtain ⟨a', ha'⟩ := (hV 0).2 (mvP.resV 0 b)
    have hcompat : colResWU mvX r 0 a + colResWV mvX r 0 a' = 0 := by
      apply (hW 0).1
      rw [map_zero, lhSum_pair pX pP L, ha, ha', ← resW_compat, add_self]
    obtain ⟨c, hc1, hc2⟩ := (colExactSum mvX r 0 a a').mp hcompat
    refine ⟨c, ?_⟩
    have h1 : mvP.resU 0 (lhSum L.π ξ r 0 c) = mvP.resU 0 b := by
      rw [lhSum_resU pX pP L, hc1, ha]
    have h2 : mvP.resV 0 (lhSum L.π ξ r 0 c) = mvP.resV 0 b := by
      rw [lhSum_resV pX pP L, hc2, ha']
    have h3 : lhSum L.π ξ r 0 c - b = 0 :=
      hP.exactZero _ (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
    exact sub_eq_zero.mp h3

/-! ## 3. The five lemma -/

/-- **The Mayer–Vietoris step in positive degrees**, by the five lemma applied to
the column and the sequence of the total space. -/
theorem bijective_lhSum_succ (pX : MVPulls mvX) (pP : MVPulls mvP)
    (L : MVLadder pX pP) (hX : MVFacts mvX) (hP : MVFacts mvP) (ξ : Hmod2 P 2)
    (r : ℕ)
    (hU : ∀ n : ℕ, Function.Bijective (lhSum L.πU (mvP.resU 2 ξ) r n))
    (hV : ∀ n : ℕ, Function.Bijective (lhSum L.πV (mvP.resV 2 ξ) r n))
    (hW : ∀ n : ℕ, Function.Bijective (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r n))
    (m : ℕ) : Function.Bijective (lhSum L.π ξ r (m + 1)) := by
  refine bijective_of_ladder
    (AddMonoidHom.coprod (colResWU mvX r m) (colResWV mvX r m))
    (colDelta mvX r m)
    (AddMonoidHom.prod (colResU mvX r (m + 1)) (colResV mvX r (m + 1)))
    (AddMonoidHom.coprod (colResWU mvX r (m + 1)) (colResWV mvX r (m + 1)))
    (AddMonoidHom.coprod (mvP.resWU m) (mvP.resWV m))
    (mvP.δ m)
    (AddMonoidHom.prod (mvP.resU (m + 1)) (mvP.resV (m + 1)))
    (AddMonoidHom.coprod (mvP.resWU (m + 1)) (mvP.resWV (m + 1)))
    (AddMonoidHom.prodMap (lhSum L.πU (mvP.resU 2 ξ) r m)
      (lhSum L.πV (mvP.resV 2 ξ) r m))
    (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r m)
    (lhSum L.π ξ r (m + 1))
    (AddMonoidHom.prodMap (lhSum L.πU (mvP.resU 2 ξ) r (m + 1))
      (lhSum L.πV (mvP.resV 2 ξ) r (m + 1)))
    (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r (m + 1))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    exact lhSum_pair pX pP L ξ r m a.1 a.2
  · intro a
    exact lhSum_delta' pX pP L hP ξ r m a
  · intro a
    have h1 := (lhSum_resU pX pP L ξ r (m + 1) a).symm
    have h2 := (lhSum_resV pX pP L ξ r (m + 1) a).symm
    show ((lhSum L.πU (mvP.resU 2 ξ) r (m + 1)) (colResU mvX r (m + 1) a),
        (lhSum L.πV (mvP.resV 2 ξ) r (m + 1)) (colResV mvX r (m + 1) a))
      = (mvP.resU (m + 1) (lhSum L.π ξ r (m + 1) a),
        mvP.resV (m + 1) (lhSum L.π ξ r (m + 1) a))
    rw [h1, h2]
  · intro a
    exact lhSum_pair pX pP L ξ r (m + 1) a.1 a.2
  · intro x
    rw [colExactW mvX r m x]
    constructor
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), hab⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.1, y.2, hy⟩
  · intro x
    rw [← colExactX mvX hX r m x]
    exact prod_eq_zero_iff _ _
  · intro x
    have h := colExactSum mvX r (m + 1) x.1 x.2
    constructor
    · intro hx
      obtain ⟨c, hc1, hc2⟩ := h.mp hx
      refine ⟨c, ?_⟩
      show (colResU mvX r (m + 1) c, colResV mvX r (m + 1) c) = x
      rw [hc1, hc2]
    · rintro ⟨c, hc⟩
      exact h.mpr ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  · intro x
    rw [mvP.exact_W m x]
    constructor
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), hab⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.1, y.2, hy⟩
  · intro x
    rw [← mvP.exact_X m x]
    exact prod_eq_zero_iff _ _
  · intro x
    have h : mvP.resWU (m + 1) x.1 + mvP.resWV (m + 1) x.2 = 0
        ↔ mvP.resWU (m + 1) x.1 = mvP.resWV (m + 1) x.2 := add_eq_zero_iff_eq _ _
    constructor
    · intro hx
      obtain ⟨y, hy1, hy2⟩ := (mvP.exact_sum (m + 1) x.1 x.2).mp (h.mp hx)
      refine ⟨y, ?_⟩
      show (mvP.resU (m + 1) y, mvP.resV (m + 1) y) = x
      rw [hy1, hy2]
    · rintro ⟨y, hy⟩
      exact h.mpr ((mvP.exact_sum (m + 1) x.1 x.2).mpr
        ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩)
  · exact (bijective_prodMap _ _ (hU m) (hV m)).2
  · exact hW m
  · exact bijective_prodMap _ _ (hU (m + 1)) (hV (m + 1))
  · exact (hW (m + 1)).1

/-- **The Mayer–Vietoris step of Leray–Hirsch.**  If `1, ξ, …, ξ^{r-1}` is a
basis of the cohomology of the part of the total space over each of `U`, `V` and
`U ∩ V`, it is a basis over the whole base. -/
theorem bijective_lhSum (pX : MVPulls mvX) (pP : MVPulls mvP)
    (L : MVLadder pX pP) (hX : MVFacts mvX) (hP : MVFacts mvP) (ξ : Hmod2 P 2)
    (r : ℕ)
    (hU : ∀ n : ℕ, Function.Bijective (lhSum L.πU (mvP.resU 2 ξ) r n))
    (hV : ∀ n : ℕ, Function.Bijective (lhSum L.πV (mvP.resV 2 ξ) r n))
    (hW : ∀ n : ℕ, Function.Bijective (lhSum L.πW (mvP.resWU 2 (mvP.resU 2 ξ)) r n))
    (n : ℕ) : Function.Bijective (lhSum L.π ξ r n) := by
  cases n with
  | zero => exact bijective_lhSum_zero pX pP L hX hP ξ r hU hV hW
  | succ m => exact bijective_lhSum_succ pX pP L hX hP ξ r hU hV hW m

end

end LH
end CharClass
end GroupApproximation
