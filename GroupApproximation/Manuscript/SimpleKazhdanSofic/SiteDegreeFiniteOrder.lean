import GroupApproximation.Manuscript.SimpleKazhdanSofic.CrossedProductSiteAction
import GroupApproximation.Algebra.WordMetric
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Distorted elements with bounded `u`-degrees have finite order

`simple_kazhdan_sofic_group.tex` at 696c4b602, "LEF groups" (l.485–491):

> If the generators of a subgroup of $\GL_m$ involve only $u^j$ with $|j|\le w$, where $w\ge1$,
> and $|g^n|/n\to0$, then for $v$ supported at one $(x,t)$ the $g^nv$, $n<N$, span fewer than $N$
> dimensions for large $N$, uniformly in $v$. So each such $v$ is killed by a polynomial over
> $\F_2$ of degree below $N$; there are finitely many of these, their product kills $g$, and $g$
> has finite order.

With `E = ρ(g)` on `(F₂^{(X × ℤ)})^m` (`CrossedProductSiteAction`):

* **Span.** A word of length `L` in generators involving only `u^j` with `|j| ≤ w` moves
  vectors near a site at most `L w` levels (`hasDisplacement_listProd`). If `|g^n| ≤ L(n)` with
  `L(n)/n → 0`, then for large `N` all `E^n v`, `n < N`, lie in the window of `m(2D+1) < N`
  coordinates at the site of `v` (`isOfFinOrder_of_sublinear`, `PrintedSiteSpanFewerDimensions`).
* **Killing polynomial.** Over `F₂` the `2^N` subset sums of `E^n v` fall into
  `2^{m(2D+1)} < 2^N` window values. Two different subsets `A ≠ B` give the same vector, so
  `∑_A X^n - ∑_B X^n`, a nonzero polynomial of degree below `N`, kills `v` (`exists_poly_kill`).
* **Product.** These polynomials form the finite set `killers N`. Their product `P` is monic
  (`monic_of_ne_zero_zmodTwo`) and kills every site vector, hence `P(E) = 0`
  (`aeval_killers_eq_zero`).
* **Finite order.** `E` is integral over `F₂`, so `F₂[E]` is finite. Two powers of `E` agree, and
  faithfulness makes two powers of `g` agree (`isOfFinOrder_of_hasDisplacement`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SiteAction

open Finsupp Filter Topology

section Generic

variable {Z : Type*} {m : ℕ}

/-- The coordinates of `v` on the `2D + 1` levels around `t` at the base point `x0`. -/
def window (x0 : Z) (t : ℤ) (D : ℕ) (v : Fin m → (Z × ℤ →₀ ZMod 2)) :
    Fin m → Fin (2 * D + 1) → ZMod 2 :=
  fun i j => v i (x0, t - (D : ℤ) + ((j : ℕ) : ℤ))

/-- Vectors near a site are determined by their window. -/
theorem eq_of_window_eq {x0 : Z} {t : ℤ} {D : ℕ} {v v' : Fin m → (Z × ℤ →₀ ZMod 2)}
    (hv : NearSite x0 t D v) (hv' : NearSite x0 t D v')
    (h : window x0 t D v = window x0 t D v') : v = v' := by
  funext i
  refine Finsupp.ext fun p => ?_
  obtain ⟨y, l⟩ := p
  by_cases hw : y = x0 ∧ |l - t| ≤ (D : ℤ)
  · obtain ⟨hy, hl⟩ := hw
    rw [abs_le] at hl
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, (j0 : ℤ) = l - (t - D) :=
      ⟨(l - (t - D)).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hj : j0 < 2 * D + 1 := by omega
    have e : (y, l) = (x0, t - (D : ℤ) + (((⟨j0, hj⟩ : Fin (2 * D + 1)) : ℕ) : ℤ)) :=
      Prod.ext hy (by show l = t - (D : ℤ) + (j0 : ℤ); omega)
    rw [e]
    exact congrFun (congrFun h i) ⟨j0, hj⟩
  · have h1 : (v i) (y, l) = 0 := by
      by_contra hne
      exact hw (hv i (y, l) (Finsupp.mem_support_iff.2 hne))
    have h2 : (v' i) (y, l) = 0 := by
      by_contra hne
      exact hw (hv' i (y, l) (Finsupp.mem_support_iff.2 hne))
    rw [h1, h2]

/-- A vector supported at one site. -/
theorem nearSite_single (i : Fin m) (x0 : Z) (t : ℤ) (c : ZMod 2) :
    NearSite x0 t 0 (Pi.single i (Finsupp.single (x0, t) c) : Fin m → (Z × ℤ →₀ ZMod 2)) := by
  classical
  intro j p hp
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same] at hp
    have hp' := Finset.mem_singleton.1 (Finsupp.support_single_subset hp)
    subst hp'
    simp
  · rw [Pi.single_eq_of_ne hj] at hp
    simp at hp

/-- **The pigeonhole step** (tex l.488): a nonzero polynomial of degree below `N` kills `v`. -/
theorem exists_poly_kill {E : Module.End (ZMod 2) (Fin m → (Z × ℤ →₀ ZMod 2))} {N D : ℕ}
    (hE : ∀ n < N, HasDisplacement D (E ^ n)) (hN : m * (2 * D + 1) < N) {x0 : Z} {t : ℤ}
    {v : Fin m → (Z × ℤ →₀ ZMod 2)} (hv : NearSite x0 t 0 v) :
    ∃ A B : Finset ℕ, A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧ A ≠ B ∧
      Polynomial.aeval E (∑ n ∈ A, (Polynomial.X : Polynomial (ZMod 2)) ^ n -
        ∑ n ∈ B, Polynomial.X ^ n) v = 0 := by
  classical
  have hnear : ∀ C : Finset ℕ, C ⊆ Finset.range N → NearSite x0 t D (∑ n ∈ C, (E ^ n) v) := by
    intro C hC i p hp
    rw [Finset.sum_apply] at hp
    obtain ⟨n, hn, hpn⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hp)
    have h := hE n (Finset.mem_range.1 (hC hn)) x0 t 0 v hv i p hpn
    rwa [zero_add] at h
  let f : ↥((Finset.range N).powerset) → Fin m → Fin (2 * D + 1) → ZMod 2 :=
    fun A => window x0 t D (∑ n ∈ (A : Finset ℕ), (E ^ n) v)
  have hcard : Fintype.card (Fin m → Fin (2 * D + 1) → ZMod 2) <
      Fintype.card ↥((Finset.range N).powerset) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card,
      Fintype.card_coe, Finset.card_powerset, Finset.card_range, ← pow_mul]
    exact pow_lt_pow_right₀ (by norm_num) (by rw [mul_comm]; exact hN)
  obtain ⟨A, B, hAB, hfAB⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hA : (A : Finset ℕ) ⊆ Finset.range N := Finset.mem_powerset.1 A.2
  have hB : (B : Finset ℕ) ⊆ Finset.range N := Finset.mem_powerset.1 B.2
  have heq : ∑ n ∈ (A : Finset ℕ), (E ^ n) v = ∑ n ∈ (B : Finset ℕ), (E ^ n) v :=
    eq_of_window_eq (hnear _ hA) (hnear _ hB) hfAB
  refine ⟨A, B, hA, hB, fun h => hAB (Subtype.ext h), ?_⟩
  simp only [map_sub, map_sum, Polynomial.aeval_X_pow, LinearMap.sub_apply, LinearMap.sum_apply,
    heq, sub_self]

open Classical in
/-- The finitely many polynomials `∑_{n ∈ A} X^n - ∑_{n ∈ B} X^n` with `A ≠ B ⊆ {0, …, N-1}`. -/
noncomputable def killers (N : ℕ) : Finset (Polynomial (ZMod 2)) :=
  (((Finset.range N).powerset ×ˢ (Finset.range N).powerset).filter fun AB => AB.1 ≠ AB.2).image
    fun AB => ∑ n ∈ AB.1, (Polynomial.X : Polynomial (ZMod 2)) ^ n - ∑ n ∈ AB.2, Polynomial.X ^ n

theorem mem_killers {N : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N)
    (hAB : A ≠ B) :
    (∑ n ∈ A, (Polynomial.X : Polynomial (ZMod 2)) ^ n - ∑ n ∈ B, Polynomial.X ^ n) ∈
      killers N := by
  classical
  unfold killers
  exact Finset.mem_image.2 ⟨(A, B), Finset.mem_filter.2 ⟨Finset.mem_product.2
    ⟨Finset.mem_powerset.2 hA, Finset.mem_powerset.2 hB⟩, hAB⟩, rfl⟩

theorem sum_X_pow_sub_ne_zero {A B : Finset ℕ} (h : A ≠ B) :
    (∑ n ∈ A, (Polynomial.X : Polynomial (ZMod 2)) ^ n - ∑ n ∈ B, Polynomial.X ^ n) ≠ 0 := by
  classical
  intro h0
  apply h
  ext n
  have hc := congrArg (Polynomial.lcoeff (ZMod 2) n) h0
  simp only [map_sub, map_sum, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow, map_zero,
    Finset.sum_ite_eq] at hc
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB] at hc ⊢

/-- **Degree below `N`** (tex l.488): the coefficients from `N` on vanish. -/
theorem coeff_sum_X_pow_sub_eq_zero {N j : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.range N)
    (hB : B ⊆ Finset.range N) (hj : N ≤ j) :
    (∑ n ∈ A, (Polynomial.X : Polynomial (ZMod 2)) ^ n - ∑ n ∈ B, Polynomial.X ^ n).coeff j = 0 := by
  classical
  have hjA : j ∉ A := fun h => by
    have := Finset.mem_range.1 (hA h)
    omega
  have hjB : j ∉ B := fun h => by
    have := Finset.mem_range.1 (hB h)
    omega
  rw [← Polynomial.lcoeff_apply]
  simp only [map_sub, map_sum, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow, Finset.sum_ite_eq,
    hjA, hjB, if_false, sub_zero]

theorem killers_ne_zero {N : ℕ} {p : Polynomial (ZMod 2)} (hp : p ∈ killers N) : p ≠ 0 := by
  classical
  unfold killers at hp
  obtain ⟨AB, hAB, rfl⟩ := Finset.mem_image.1 hp
  exact sum_X_pow_sub_ne_zero (Finset.mem_filter.1 hAB).2

/-- A nonzero polynomial over `F₂` is monic. -/
theorem monic_of_ne_zero_zmodTwo {p : Polynomial (ZMod 2)} (hp : p ≠ 0) : p.Monic := by
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  exact key _ (Polynomial.leadingCoeff_ne_zero.2 hp)

theorem aeval_prod_apply_eq_zero {E : Module.End (ZMod 2) (Fin m → (Z × ℤ →₀ ZMod 2))}
    {s : Finset (Polynomial (ZMod 2))} {p : Polynomial (ZMod 2)} (hp : p ∈ s)
    {v : Fin m → (Z × ℤ →₀ ZMod 2)} (hv : Polynomial.aeval E p v = 0) :
    Polynomial.aeval E (∏ q ∈ s, q) v = 0 := by
  classical
  rw [← Finset.prod_erase_mul s (fun q => q) hp, map_mul, Module.End.mul_apply, hv, map_zero]

/-- An endomorphism killing every vector at a site is zero. -/
theorem eq_zero_of_forall_site {F : Module.End (ZMod 2) (Fin m → (Z × ℤ →₀ ZMod 2))}
    (h : ∀ (i : Fin m) (x0 : Z) (t : ℤ) (c : ZMod 2),
      F (Pi.single i (Finsupp.single (x0, t) c)) = 0) : F = 0 := by
  classical
  refine LinearMap.pi_ext' fun i => Finsupp.lhom_ext fun p c => ?_
  obtain ⟨x0, t⟩ := p
  simpa [LinearMap.single_apply] using h i x0 t c

/-- **Their product kills `E`** (tex l.488–490). -/
theorem aeval_killers_eq_zero {E : Module.End (ZMod 2) (Fin m → (Z × ℤ →₀ ZMod 2))} {N D : ℕ}
    (hE : ∀ n < N, HasDisplacement D (E ^ n)) (hN : m * (2 * D + 1) < N) :
    Polynomial.aeval E (∏ q ∈ killers N, q) = 0 := by
  refine eq_zero_of_forall_site fun i x0 t c => ?_
  obtain ⟨A, B, hA, hB, hAB, hkill⟩ := exists_poly_kill hE hN (nearSite_single i x0 t c)
  exact aeval_prod_apply_eq_zero (mem_killers hA hB hAB) hkill

/-- A sublinear length function eventually leaves room for any affine bound. -/
theorem exists_large_N_of_tendsto {L : ℕ → ℕ}
    (hL : Tendsto (fun n => (L n : ℝ) / n) atTop (𝓝 0)) (a b N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧ ∀ n < N, a * L n + b < N := by
  have hε : (0 : ℝ) < 1 / (2 * (a : ℝ) + 2) := by positivity
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 (hL.eventually (Iio_mem_nhds hε))
  have hbig : ∀ n, max n0 1 ≤ n → 2 * (a * L n) < n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h : (L n : ℝ) / n < 1 / (2 * (a : ℝ) + 2) :=
      Set.mem_Iio.1 (hn0 n (le_trans (le_max_left _ _) hn))
    rw [div_lt_iff₀ hnpos] at h
    have hpos : (0 : ℝ) < 2 * (a : ℝ) + 2 := by positivity
    have hne : (2 * (a : ℝ) + 2) ≠ 0 := hpos.ne'
    have h3 : (L n : ℝ) * (2 * a + 2) < n := by
      calc (L n : ℝ) * (2 * a + 2) < 1 / (2 * (a : ℝ) + 2) * n * (2 * a + 2) :=
            mul_lt_mul_of_pos_right h hpos
        _ = n := by field_simp [hne]
    have hL0 : (0 : ℝ) ≤ L n := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have h2 : ((2 * (a * L n) : ℕ) : ℝ) < n := by
      push_cast
      nlinarith [hL0, ha0, h3]
    exact_mod_cast h2
  refine ⟨2 * ((∑ n ∈ Finset.range (max n0 1), a * L n) + b) + max n0 1 + N0 + 1, by omega,
    fun n hn => ?_⟩
  by_cases hsmall : n < max n0 1
  · have hle : a * L n ≤ ∑ n ∈ Finset.range (max n0 1), a * L n :=
      Finset.single_le_sum (f := fun n => a * L n) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hsmall)
    generalize a * L n = z at hle ⊢
    generalize ∑ n ∈ Finset.range (max n0 1), a * L n = C at hle hn
    omega
  · have h := hbig n (not_lt.1 hsmall)
    generalize a * L n = z at h ⊢
    generalize ∑ n ∈ Finset.range (max n0 1), a * L n = C at hn
    omega

end Generic

section Dynamics

variable {Z : Type*} [TopologicalSpace Z] {T : Z ≃ₜ Z} {m : ℕ}

/-- `M_m(LC(Z, F₂) ⋊_T ℤ)`. -/
abbrev Mat2 (T : Z ≃ₜ Z) (m : ℕ) : Type _ :=
  Matrix (Fin m) (Fin m) (ClopenCrossedProduct T (ZMod 2))

/-- **Finite order** (tex l.488–491): if the powers `g^n`, `n < N`, move site vectors at most `D`
levels and `m(2D+1) < N`, then `g` has finite order. -/
theorem isOfFinOrder_of_hasDisplacement (g : (Mat2 T m)ˣ) {N D : ℕ}
    (hg : ∀ n < N, HasDisplacement D (rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m)))
    (hN : m * (2 * D + 1) < N) : IsOfFinOrder g := by
  classical
  have hpow : ∀ n : ℕ, rhoMat T (ZMod 2) m (g : Mat2 T m) ^ n =
      rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m) := fun n => by
    rw [← map_pow, Units.val_pow_eq_pow_val]
  have hE : ∀ n < N, HasDisplacement D (rhoMat T (ZMod 2) m (g : Mat2 T m) ^ n) :=
    fun n hn => by
      rw [hpow]
      exact hg n hn
  have hP := aeval_killers_eq_zero hE hN
  have hint : IsIntegral (ZMod 2) (rhoMat T (ZMod 2) m (g : Mat2 T m)) :=
    ⟨∏ q ∈ killers N, q, Polynomial.monic_prod_of_monic _ _ fun q hq =>
      monic_of_ne_zero_zmodTwo (killers_ne_zero hq), by rw [← Polynomial.aeval_def]; exact hP⟩
  haveI : Module.Finite (ZMod 2)
      (Subalgebra.toSubmodule (Algebra.adjoin (ZMod 2) {rhoMat T (ZMod 2) m (g : Mat2 T m)})) :=
    Module.Finite.iff_fg.2 hint.fg_adjoin_singleton
  haveI : Finite
      (Subalgebra.toSubmodule (Algebra.adjoin (ZMod 2) {rhoMat T (ZMod 2) m (g : Mat2 T m)})) :=
    Module.finite_of_finite (ZMod 2)
  obtain ⟨a, b, hab, hpowab⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨rhoMat T (ZMod 2) m (g : Mat2 T m) ^ n, (Subalgebra.mem_toSubmodule _).2
      (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) n)⟩ :
        Subalgebra.toSubmodule
          (Algebra.adjoin (ZMod 2) {rhoMat T (ZMod 2) m (g : Mat2 T m)})))
  have hEab : rhoMat T (ZMod 2) m (g : Mat2 T m) ^ a = rhoMat T (ZMod 2) m (g : Mat2 T m) ^ b :=
    congrArg Subtype.val hpowab
  rw [hpow, hpow] at hEab
  have hgab : g ^ a = g ^ b := Units.ext (rhoMat_injective T (ZMod 2) m hEab)
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨b - a, by omega, mul_left_cancel (a := g ^ a) ?_⟩
    rw [← pow_add, Nat.add_sub_of_le h.le, mul_one]
    exact hgab.symm
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨a - b, by omega, mul_left_cancel (a := g ^ b) ?_⟩
    rw [← pow_add, Nat.add_sub_of_le h.le, mul_one]
    exact hgab

/-- A word of length `L` in generators involving only `u^j` with `|j| ≤ w` moves site vectors at
most `L w` levels. -/
theorem hasDisplacement_listProd {S : Set (Mat2 T m)ˣ} {w : ℕ}
    (hS : ∀ s ∈ S, ∀ i j, UDegreeLE w ((s : Mat2 T m) i j)) :
    ∀ l : List (Mat2 T m)ˣ, (∀ s ∈ l, s ∈ S) →
      HasDisplacement (l.length * w) (rhoMat T (ZMod 2) m ((l.prod : (Mat2 T m)ˣ) : Mat2 T m))
  | [], _ => by
      rw [List.length_nil, zero_mul, List.prod_nil, Units.val_one, map_one]
      exact hasDisplacement_one
  | s :: l, hl => by
      rw [List.length_cons, List.prod_cons, Units.val_mul, map_mul, add_mul, one_mul, add_comm]
      exact (hasDisplacement_rhoMat (hS s (hl s (by simp)))).mul
        (hasDisplacement_listProd hS l fun x hx => hl x (by simp [hx]))

/-- **Span** (tex l.485–488): for large `N` the powers `g^n`, `n < N`, move site vectors at most
`D` levels, with `m(2D+1) < N`. -/
theorem isOfFinOrder_of_sublinear {S : Set (Mat2 T m)ˣ} {w : ℕ}
    (hS : ∀ s ∈ S, ∀ i j, UDegreeLE w ((s : Mat2 T m) i j)) (g : (Mat2 T m)ˣ) (L : ℕ → ℕ)
    (hword : ∀ n, ∃ l : List (Mat2 T m)ˣ, WordMetric.IsWord S l (g ^ n) ∧ l.length ≤ L n)
    (hL : Tendsto (fun n => (L n : ℝ) / n) atTop (𝓝 0)) (N0 : ℕ) :
    ∃ N D : ℕ, N0 ≤ N ∧ m * (2 * D + 1) < N ∧
      ∀ n < N, HasDisplacement D (rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m)) := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_large_N_of_tendsto hL (2 * m * w) m (N0 + 1)
  obtain ⟨nstar, hnstar, hmax⟩ := Finset.exists_max_image (Finset.range N) (fun n => L n * w)
    ⟨0, Finset.mem_range.2 (by omega)⟩
  refine ⟨N, L nstar * w, by omega, ?_, fun n hn => ?_⟩
  · have h := hN nstar (Finset.mem_range.1 hnstar)
    calc m * (2 * (L nstar * w) + 1) = 2 * m * w * L nstar + m := by ring
      _ < N := h
  · obtain ⟨l, hl, hlen⟩ := hword n
    have h := hasDisplacement_listProd hS l hl.letters
    rw [hl.prod_eq] at h
    exact h.mono ((Nat.mul_le_mul_right w hlen).trans (hmax n (Finset.mem_range.2 hn)))

/-- **tex l.485–491**, the finite order conclusion. -/
theorem isOfFinOrder_of_sublinear_wordLength {S : Set (Mat2 T m)ˣ} {w : ℕ}
    (hS : ∀ s ∈ S, ∀ i j, UDegreeLE w ((s : Mat2 T m) i j)) (g : (Mat2 T m)ˣ) (L : ℕ → ℕ)
    (hword : ∀ n, ∃ l : List (Mat2 T m)ˣ, WordMetric.IsWord S l (g ^ n) ∧ l.length ≤ L n)
    (hL : Tendsto (fun n => (L n : ℝ) / n) atTop (𝓝 0)) : IsOfFinOrder g := by
  obtain ⟨N, D, -, hN, hD⟩ := isOfFinOrder_of_sublinear hS g L hword hL 0
  exact isOfFinOrder_of_hasDisplacement g hD hN

end Dynamics

/-! ## The printed sentences -/

/-- **tex l.485–488**: generators involving only `u^j` with `|j| ≤ w` and `|g^n|/n → 0` give, for
large `N` and uniformly in `v` at one site, `g^n v ∈` a window of `m(2D+1) < N` coordinates. -/
def PrintedSiteSpanFewerDimensions : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (T : Z ≃ₜ Z) (m w : ℕ) (S : Set (Mat2 T m)ˣ),
    (∀ s ∈ S, ∀ i j, UDegreeLE w ((s : Mat2 T m) i j)) →
    ∀ (g : (Mat2 T m)ˣ) (L : ℕ → ℕ),
      (∀ n, ∃ l : List (Mat2 T m)ˣ, WordMetric.IsWord S l (g ^ n) ∧ l.length ≤ L n) →
      Tendsto (fun n => (L n : ℝ) / n) atTop (𝓝 0) →
      ∀ N0 : ℕ, ∃ N D : ℕ, N0 ≤ N ∧ m * (2 * D + 1) < N ∧
        ∀ (x0 : Z) (t : ℤ) (v : Fin m → (Z × ℤ →₀ ZMod 2)), NearSite x0 t 0 v → ∀ n < N,
          NearSite x0 t D (rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m) v)

theorem printedSiteSpanFewerDimensions : PrintedSiteSpanFewerDimensions := by
  intro _ _ _ _ _ _ hS g L hword hL N0
  obtain ⟨N, D, hN0, hN, hD⟩ := isOfFinOrder_of_sublinear hS g L hword hL N0
  refine ⟨N, D, hN0, hN, fun x0 t v hv n hn => ?_⟩
  have h := hD n hn x0 t 0 v hv
  rwa [zero_add] at h

/-- **tex l.488–491**: under the span bound, each site vector is killed by a nonzero polynomial of
degree below `N`, the product of these finitely many polynomials kills `g`, and `g` has finite
order. -/
def PrintedKillingPolynomialsFiniteOrder : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (T : Z ≃ₜ Z) (m : ℕ) (g : (Mat2 T m)ˣ) (N D : ℕ),
    (∀ n < N, HasDisplacement D (rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m))) →
    m * (2 * D + 1) < N →
      (∀ (x0 : Z) (t : ℤ) (v : Fin m → (Z × ℤ →₀ ZMod 2)), NearSite x0 t 0 v →
        ∃ p ∈ killers N, p ≠ 0 ∧ (∀ j, N ≤ j → p.coeff j = 0) ∧
          Polynomial.aeval (rhoMat T (ZMod 2) m (g : Mat2 T m)) p v = 0) ∧
      Polynomial.aeval (rhoMat T (ZMod 2) m (g : Mat2 T m)) (∏ q ∈ killers N, q) = 0 ∧
      IsOfFinOrder g

theorem printedKillingPolynomialsFiniteOrder : PrintedKillingPolynomialsFiniteOrder := by
  intro _ _ T m g N D hg hN
  have hpow : ∀ n : ℕ, rhoMat T (ZMod 2) m (g : Mat2 T m) ^ n =
      rhoMat T (ZMod 2) m ((g ^ n : (Mat2 T m)ˣ) : Mat2 T m) := fun n => by
    rw [← map_pow, Units.val_pow_eq_pow_val]
  have hE : ∀ n < N, HasDisplacement D (rhoMat T (ZMod 2) m (g : Mat2 T m) ^ n) :=
    fun n hn => by
      rw [hpow]
      exact hg n hn
  refine ⟨fun x0 t v hv => ?_, aeval_killers_eq_zero hE hN, isOfFinOrder_of_hasDisplacement g hg hN⟩
  obtain ⟨A, B, hA, hB, hAB, hkill⟩ := exists_poly_kill hE hN hv
  exact ⟨_, mem_killers hA hB hAB, sum_X_pow_sub_ne_zero hAB,
    fun j hj => coeff_sum_X_pow_sub_eq_zero hA hB hj, hkill⟩

#audit_closed_axioms printedSiteSpanFewerDimensions
#audit_closed_axioms printedKillingPolynomialsFiniteOrder

end SiteAction
end SimpleKazhdanSofic
end GroupApproximation
