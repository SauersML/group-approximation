import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Hom
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 3.3 in the form an action consumes (lane pal-q111, H.L2)

Lavrenov–Sinchuk (arXiv:1909.02637, §5.4) define an action of `St_N(B)`, `B = A[X⁻¹] + 𝔄[X]`,
by two kinds of operators:
* those of `t`-degree `≤ 0`, i.e. of `B₀ = A + 𝔄 X A[X]` (`horrB0`), given together as a
  homomorphism `φ₀ : St_N(B₀) → G` (their formula (5.19));
* those of degree one, `T_ij(a)` for `x_ij(a X⁻¹)` (their formula (5.17)).

`exists_hom_of_degOne` turns such data into a homomorphism `St_N(B) → G`, provided the relations of
degree `≤ 1` that mix the two kinds hold (L–S Lemmas 5.34–5.38): additivity of `T`, the commutator
formulas `R2_{0,1}`, `R2_{1,0}`, `R2_{d,1}` (`d < 0`), the commutations `R3_{d,1}` (`d ≤ 0`) and the
commutations `R3^∠_{1,1}` of two degree-one operators with a common index.  The commutation of two
degree-one operators on four distinct indices is then automatic (L–S Lemma 5.2,
`degOne_perp`).

The degree-`≤ 0` generators are written `xMono 𝔄 i j hij n c` for `x_ij(c Xⁿ)`, `n : ℕ`
(`c ∈ 𝔄` when `n ≥ 1`; the value is `1` otherwise).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace Graded

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section Ring

variable {A : Type} [CommRing A] {𝔄 : Ideal A}

/-- No coefficients in negative degree. -/
def NoNeg (f : LaurentPolynomial A) : Prop :=
  ∀ n : ℤ, n < 0 → f.coeff n = 0

theorem noNeg_mul {f g : LaurentPolynomial A} (hf : NoNeg f) (hg : NoNeg g) : NoNeg (f * g) := by
  intro n hn
  rw [AddMonoidAlgebra.coeff_mul]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  refine ite_eq_right_iff.mpr fun hab => ?_
  by_cases ha : a < 0
  · rw [hf a ha, zero_mul]
  · rw [hg b (by omega), mul_zero]

variable (𝔄) in
/-- **`B₀ = A + 𝔄 X A[X]`**, the part of `B` of `t`-degree `≤ 0`. -/
def horrB0 : Subring (LaurentPolynomial A) where
  carrier := {f | f ∈ horrB 𝔄 ∧ NoNeg f}
  mul_mem' := fun hf hg => ⟨(horrB 𝔄).mul_mem hf.1 hg.1, noNeg_mul hf.2 hg.2⟩
  one_mem' := ⟨(horrB 𝔄).one_mem, fun n hn => by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact if_neg (by omega)⟩
  add_mem' := fun hf hg => ⟨(horrB 𝔄).add_mem hf.1 hg.1, fun n hn => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf.2 n hn, hg.2 n hn, add_zero]⟩
  zero_mem' := ⟨(horrB 𝔄).zero_mem, fun n _ => by
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]⟩
  neg_mem' := fun hf => ⟨(horrB 𝔄).neg_mem hf.1, fun n hn => by
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hf.2 n hn, neg_zero]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB0

theorem horrB0_le : horrB0 𝔄 ≤ horrB 𝔄 := fun _ hf => hf.1

theorem single_mem_horrB0 {n : ℕ} {c : A} (hc : n = 0 ∨ c ∈ 𝔄) :
    AddMonoidAlgebra.single (n : ℤ) c ∈ horrB0 𝔄 := by
  refine ⟨single_mem_horrB fun h => ?_, fun k hk => ?_⟩
  · rcases hc with rfl | hc
    · simp at h
    · exact hc
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact if_neg (by omega)

variable (𝔄) in
/-- `x_ij(c Xⁿ)` in `St_N(B₀)`, and `1` when `c Xⁿ ∉ B₀`. -/
noncomputable def xMono {N : ℕ} (i j : Fin N) (hij : i ≠ j) (n : ℕ) (c : A) :
    SteinbergGroup (Fin N) (horrB0 𝔄) := by
  classical
  exact if hc : n = 0 ∨ c ∈ 𝔄 then x i j hij ⟨_, single_mem_horrB0 hc⟩ else 1

theorem xMono_of {N : ℕ} {i j : Fin N} (hij : i ≠ j) {n : ℕ} {c : A} (hc : n = 0 ∨ c ∈ 𝔄) :
    xMono 𝔄 i j hij n c = x i j hij ⟨_, single_mem_horrB0 hc⟩ := by
  unfold xMono
  rw [dif_pos hc]

theorem xMono_add {N : ℕ} {i j : Fin N} (hij : i ≠ j) {n : ℕ} {c c' : A} (hc : n = 0 ∨ c ∈ 𝔄)
    (hc' : n = 0 ∨ c' ∈ 𝔄) : xMono 𝔄 i j hij n c * xMono 𝔄 i j hij n c' = xMono 𝔄 i j hij n (c + c') := by
  have hcc : n = 0 ∨ c + c' ∈ 𝔄 := by
    rcases hc with h | h
    · exact Or.inl h
    · rcases hc' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (𝔄.add_mem h h')
  rw [xMono_of hij hc, xMono_of hij hc', xMono_of hij hcc, x_mul]
  congr 1
  exact Subtype.ext (AddMonoidAlgebra.single_add _ _ _).symm

theorem xMono_comm {N : ℕ} {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {n n' : ℕ}
    {c c' : A} (hc : n = 0 ∨ c ∈ 𝔄) (hc' : n' = 0 ∨ c' ∈ 𝔄) :
    ⁅xMono 𝔄 i j hij n c, xMono 𝔄 j k hjk n' c'⁆ = xMono 𝔄 i k hik (n + n') (c * c') := by
  have hcc : n + n' = 0 ∨ c * c' ∈ 𝔄 := by
    rcases hc with h | h
    · rcases hc' with h' | h'
      · exact Or.inl (by omega)
      · exact Or.inr (𝔄.mul_mem_left c h')
    · exact Or.inr (𝔄.mul_mem_right c' h)
  rw [xMono_of hij hc, xMono_of hjk hc', xMono_of hik hcc, x_commutator]
  congr 1
  apply Subtype.ext
  change AddMonoidAlgebra.single (n : ℤ) c * AddMonoidAlgebra.single (n' : ℤ) c' =
    AddMonoidAlgebra.single ((n + n' : ℕ) : ℤ) (c * c')
  rw [AddMonoidAlgebra.single_mul_single, Nat.cast_add]

theorem xMono_commute {N : ℕ} {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hil : i ≠ l) (n n' : ℕ) (c c' : A) :
    Commute (xMono 𝔄 i j hij n c) (xMono 𝔄 k l hkl n' c') := by
  unfold xMono
  split_ifs
  · exact x_commute_of_ne i j k l hij hkl hjk hil.symm _ _
  · exact Commute.one_right _
  · exact Commute.one_left _
  · exact Commute.one_left _

/-- Induction over the monomials of an element of `B₀`. -/
theorem horrB0_induction {motive : (f : LaurentPolynomial A) → f ∈ horrB0 𝔄 → Prop}
    (zero : motive 0 (horrB0 𝔄).zero_mem)
    (monomial : ∀ (n : ℕ) (c : A) (hc : n = 0 ∨ c ∈ 𝔄),
      motive (AddMonoidAlgebra.single (n : ℤ) c) (single_mem_horrB0 hc))
    (add : ∀ (f g : LaurentPolynomial A) (hf : f ∈ horrB0 𝔄) (hg : g ∈ horrB0 𝔄),
      motive f hf → motive g hg → motive (f + g) ((horrB0 𝔄).add_mem hf hg))
    {f : LaurentPolynomial A} (hf : f ∈ horrB0 𝔄) : motive f hf := by
  classical
  have transport : ∀ (g g' : LaurentPolynomial A), g = g' → ∀ (hg : g ∈ horrB0 𝔄)
      (hg' : g' ∈ horrB0 𝔄), motive g hg → motive g' hg' := by
    rintro g _ rfl hg hg' hm
    exact hm
  have hmono : ∀ a ∈ f.coeff.support, ∃ h : AddMonoidAlgebra.single a (f.coeff a) ∈ horrB0 𝔄,
      motive _ h := by
    intro a ha
    have ha0 : 0 ≤ a := by
      by_contra hneg
      exact (Finsupp.mem_support_iff.mp ha) (hf.2 a (by omega))
    have hc : a.toNat = 0 ∨ f.coeff a ∈ 𝔄 := by
      rcases eq_or_lt_of_le ha0 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (hf.1 a h)
    have heq : AddMonoidAlgebra.single ((a.toNat : ℕ) : ℤ) (f.coeff a) =
        AddMonoidAlgebra.single a (f.coeff a) := by
      rw [Int.toNat_of_nonneg ha0]
    have hmem : AddMonoidAlgebra.single a (f.coeff a) ∈ horrB0 𝔄 := heq ▸ single_mem_horrB0 hc
    exact ⟨hmem, transport _ _ heq _ hmem (monomial a.toNat (f.coeff a) hc)⟩
  have key : ∀ s : Finset ℤ, s ⊆ f.coeff.support →
      ∃ h : (∑ n ∈ s, AddMonoidAlgebra.single n (f.coeff n)) ∈ horrB0 𝔄, motive _ h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty]
      exact ⟨_, zero⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨h, hm⟩ := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      obtain ⟨h1, hm1⟩ := hmono a (hs (Finset.mem_insert_self a s))
      rw [Finset.sum_insert ha]
      exact ⟨_, add _ _ h1 h hm1 hm⟩
  obtain ⟨h, hm⟩ := key f.coeff.support le_rfl
  exact transport _ _ (sum_single_eq f).symm h hf hm

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB0_induction

end Ring

section Main

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {G : Type*} [Group G] {N : ℕ}

/-- The family of candidate images: `x_ij(c t^d) ↦ φ₀(x_ij(c X^{-d}))` for `d ≤ 0`, and `T_ij(c)`
for `d ≥ 1` (only `d = 1` matters). -/
noncomputable def degOneFam (φ₀ : SteinbergGroup (Fin N) (horrB0 𝔄) →* G)
    (T : ∀ i j : Fin N, i ≠ j → A → G) : Fam G A N := by
  classical
  exact fun i j hij d c => if d ≤ 0 then φ₀ (xMono 𝔄 i j hij (-d).toNat c) else T i j hij c

/-- **The data of an action of `St_N(B)` by degree-`≤ 1` operators**, with the mixed relations of
degree `≤ 1` (Lavrenov–Sinchuk, Lemmas 5.34–5.38). -/
structure DegOneData (𝔄 : Ideal A) (G : Type*) [Group G] (N : ℕ) where
  /-- The operators of degree `≤ 0`. -/
  φ₀ : SteinbergGroup (Fin N) (horrB0 𝔄) →* G
  /-- `T i j hij a` is the operator of `x_ij(a X⁻¹)`. -/
  T : ∀ i j : Fin N, i ≠ j → A → G
  /-- `R1_1` (L–S Lemma 5.34). -/
  add : ∀ (i j : Fin N) (hij : i ≠ j) (a a' : A), T i j hij a * T i j hij a' = T i j hij (a + a')
  /-- `R2_{0,1}`. -/
  r2L0 : ∀ (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (c a : A),
    ⁅φ₀ (xMono 𝔄 i j hij 0 c), T j k hjk a⁆ = T i k hik (c * a)
  /-- `R2_{d,1}`, `d < 0` (L–S Lemma 5.36). -/
  r2Lpos : ∀ (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (n : ℕ) (c a : A),
    c ∈ 𝔄 → ⁅φ₀ (xMono 𝔄 i j hij (n + 1) c), T j k hjk a⁆ = φ₀ (xMono 𝔄 i k hik n (c * a))
  /-- `R2_{1,0}` (L–S Lemma 5.38). -/
  r2R0 : ∀ (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a c : A),
    ⁅T i j hij a, φ₀ (xMono 𝔄 j k hjk 0 c)⁆ = T i k hik (a * c)
  /-- `R2_{1,d}`, `d < 0`. -/
  r2Rpos : ∀ (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (n : ℕ) (a c : A),
    c ∈ 𝔄 → ⁅T i j hij a, φ₀ (xMono 𝔄 j k hjk (n + 1) c)⁆ = φ₀ (xMono 𝔄 i k hik n (a * c))
  /-- `R3_{d,1}`, `d ≤ 0` (L–S Lemma 5.35). -/
  r3 : ∀ (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → i ≠ l → ∀ (n : ℕ) (c a : A),
    ⁅φ₀ (xMono 𝔄 i j hij n c), T k l hkl a⁆ = 1
  /-- `R3^∠_{1,1}` (L–S Lemma 5.37): two degree-one operators with a common index commute. -/
  angle : ∀ (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → i ≠ l → (i = k ∨ j = l) →
    ∀ a a' : A, ⁅T i j hij a, T k l hkl a'⁆ = 1

namespace DegOneData

variable (D : DegOneData 𝔄 G N)

theorem T_zero (i j : Fin N) (hij : i ≠ j) : D.T i j hij 0 = 1 := by
  have h0 := D.add i j hij 0 0
  rw [add_zero] at h0
  exact mul_left_cancel (h0.trans (mul_one _).symm)

theorem T_neg (i j : Fin N) (hij : i ≠ j) (a : A) : D.T i j hij (-a) = (D.T i j hij a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [D.add, neg_add_cancel, D.T_zero]

theorem commute_T_T_angle {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hil : i ≠ l) (hs : i = k ∨ j = l) (a a' : A) : Commute (D.T i j hij a) (D.T k l hkl a') :=
  commute_of_comm_eq_one (D.angle i j k l hij hkl hjk hil hs a a')

/-- **Lavrenov–Sinchuk, Lemma 5.2** (the case `R3^⊥_{1,1}`): two degree-one operators on four
distinct indices commute. -/
theorem degOne_perp {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
    (hik : i ≠ k) (hjl : j ≠ l) (a b : A) : ⁅D.T i j hij a, D.T k l hkl b⁆ = 1 := by
  have hxz : Commute (D.φ₀ (xMono 𝔄 j l hjl 0 b)) (D.φ₀ (xMono 𝔄 i k hik 0 a)) :=
    (xMono_commute hjl hik hil.symm hjk 0 0 b a).map D.φ₀
  have hyz : ⁅D.T k j hjk.symm 1, D.φ₀ (xMono 𝔄 i k hik 0 a)⁆ = (D.T i j hij a)⁻¹ := by
    rw [← commutatorElement_inv (D.φ₀ (xMono 𝔄 i k hik 0 a)) (D.T k j hjk.symm 1),
      D.r2L0 i k j hik hjk.symm hij a 1, mul_one]
  have hG1 := comm_comm_of_commute _ (D.T k j hjk.symm 1) _ hxz
  have hL : ⁅D.φ₀ (xMono 𝔄 j l hjl 0 b), ⁅D.T k j hjk.symm 1, D.φ₀ (xMono 𝔄 i k hik 0 a)⁆⁆ =
      D.T i l hil (a * b) := by
    rw [hyz, ← D.T_neg, ← commutatorElement_inv (D.T i j hij (-a)) _,
      D.r2R0 i j l hij hjl hil (-a) b, ← D.T_neg, neg_mul, neg_neg]
  have hVW : Commute (D.T i j hij a)⁻¹ (D.T i l hil (a * b)) :=
    (D.commute_T_T_angle hij hil hij.symm hil (Or.inl rfl) a (a * b)).inv_left
  have hR : ⁅⁅D.φ₀ (xMono 𝔄 j l hjl 0 b), D.T k j hjk.symm 1⁆,
      D.T k j hjk.symm 1 * D.φ₀ (xMono 𝔄 i k hik 0 a) * (D.T k j hjk.symm 1)⁻¹⁆ =
      ⁅(D.T k l hkl b)⁻¹, (D.T i j hij a)⁻¹⁆ * D.T i l hil (a * b) := by
    rw [← commutatorElement_inv (D.T k j hjk.symm 1) (D.φ₀ (xMono 𝔄 j l hjl 0 b)),
      D.r2R0 k j l hjk.symm hjl hkl 1 b, one_mul,
      conj_eq_comm_mul (D.T k j hjk.symm 1) (D.φ₀ (xMono 𝔄 i k hik 0 a)), hyz, comm_mul_right',
      commutatorElement_inv_left (D.T k l hkl b) (D.φ₀ (xMono 𝔄 i k hik 0 a)),
      D.r2L0 i k l hik hkl hil a b,
      (D.commute_T_T_angle hkl hil hil.symm hkl (Or.inr rfl) b (a * b)).inv_left.eq,
      inv_mul_cancel_right]
    simp only [mul_assoc]
    rw [← mul_assoc (D.T i j hij a)⁻¹ (D.T i l hil (a * b)), conj_eq_of_commute hVW]
  have heq : ⁅(D.T k l hkl b)⁻¹, (D.T i j hij a)⁻¹⁆ * D.T i l hil (a * b) =
      1 * D.T i l hil (a * b) := by
    rw [← hR, ← hG1, hL, one_mul]
  have hc : Commute (D.T k l hkl b) (D.T i j hij a) :=
    Commute.inv_inv_iff.mp (commute_of_comm_eq_one (mul_right_cancel heq))
  exact comm_eq_one_of_commute hc.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.DegOneData.degOne_perp

theorem fam_nonpos {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : d ≤ 0) (c : A) :
    degOneFam D.φ₀ D.T i j hij d c = D.φ₀ (xMono 𝔄 i j hij (-d).toNat c) :=
  if_pos hd

theorem fam_pos {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : 0 < d) (c : A) :
    degOneFam D.φ₀ D.T i j hij d c = D.T i j hij c :=
  if_neg (by omega)

theorem allowed_mono {d : ℤ} (hd : d ≤ 0) {c : A} (hc : Allowed 𝔄 d c) :
    (-d).toNat = 0 ∨ c ∈ 𝔄 := by
  rcases eq_or_lt_of_le hd with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (hc h)

/-- **The degree-`≤ 1` relations** for the family of an action datum. -/
theorem rels (D : DegOneData 𝔄 G N) : Rels 𝔄 (degOneFam D.φ₀ D.T) 1 where
  add i j hij d c c' hd hc hc' := by
    by_cases h0 : d ≤ 0
    · rw [D.fam_nonpos hij h0, D.fam_nonpos hij h0, D.fam_nonpos hij h0, ← map_mul,
        xMono_add hij (D.allowed_mono h0 hc) (D.allowed_mono h0 hc')]
    · rw [D.fam_pos hij (d := d) (by omega), D.fam_pos hij (d := d) (by omega),
        D.fam_pos hij (d := d) (by omega), D.add]
  r2 i j k hij hjk hik d e c c' hd he hde hc hc' := by
    by_cases hd0 : d ≤ 0 <;> by_cases he0 : e ≤ 0
    · rw [D.fam_nonpos hij hd0, D.fam_nonpos hjk he0, D.fam_nonpos hik (d := d + e) (by omega),
        ← map_commutatorElement, xMono_comm hij hjk hik (D.allowed_mono hd0 hc)
          (D.allowed_mono he0 hc'), show (-d).toNat + (-e).toNat = (-(d + e)).toNat by omega]
    · rw [D.fam_nonpos hij hd0, D.fam_pos hjk (d := e) (by omega)]
      rcases eq_or_lt_of_le hd0 with hd00 | hdlt
      · subst hd00
        rw [D.fam_pos hik (d := 0 + e) (by omega), show (-(0 : ℤ)).toNat = 0 by rfl]
        exact D.r2L0 i j k hij hjk hik c c'
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (-d).toNat = n + 1 := ⟨(-d).toNat - 1, by omega⟩
        rw [D.fam_nonpos hik (d := d + e) (by omega), hn, show (-(d + e)).toNat = n by omega]
        exact D.r2Lpos i j k hij hjk hik n c c' (hc hdlt)
    · rw [D.fam_pos hij (d := d) (by omega), D.fam_nonpos hjk he0]
      rcases eq_or_lt_of_le he0 with he00 | helt
      · subst he00
        rw [D.fam_pos hik (d := d + 0) (by omega), show (-(0 : ℤ)).toNat = 0 by rfl]
        exact D.r2R0 i j k hij hjk hik c c'
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (-e).toNat = n + 1 := ⟨(-e).toNat - 1, by omega⟩
        rw [D.fam_nonpos hik (d := d + e) (by omega), hn, show (-(d + e)).toNat = n by omega]
        exact D.r2Rpos i j k hij hjk hik n c c' (hc' helt)
    · omega
  r3 i j k l hij hkl hjk hil d e c c' hd he hc hc' := by
    by_cases hd0 : d ≤ 0 <;> by_cases he0 : e ≤ 0
    · rw [D.fam_nonpos hij hd0, D.fam_nonpos hkl he0, ← map_commutatorElement,
        comm_eq_one_of_commute (xMono_commute hij hkl hjk hil _ _ c c'), map_one]
    · rw [D.fam_nonpos hij hd0, D.fam_pos hkl (d := e) (by omega)]
      exact D.r3 i j k l hij hkl hjk hil _ c c'
    · rw [D.fam_pos hij (d := d) (by omega), D.fam_nonpos hkl he0, ← commutatorElement_inv,
        D.r3 k l i j hkl hij hil.symm hjk.symm _ c' c, inv_one]
    · rw [D.fam_pos hij (d := d) (by omega), D.fam_pos hkl (d := e) (by omega)]
      by_cases hs : i = k ∨ j = l
      · exact D.angle i j k l hij hkl hjk hil hs c c'
      · simp only [not_or] at hs
        exact D.degOne_perp hij hkl hjk hil hs.1 hs.2 c c'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.DegOneData.rels

end DegOneData

/-- **Tulenbaev, Lemma 3.3, in the form an action consumes.**  For `N ≥ 5`, an action datum `D`
(degree-`≤ 0` operators `φ₀` and degree-one operators `T`, with the mixed relations of degree
`≤ 1`) extends to a homomorphism `St_N(B) → G` that restricts to `φ₀` on `St_N(B₀)` and sends
`x_ij(a X⁻¹)` to `T_ij(a)`. -/
theorem exists_hom_of_degOne (D : DegOneData 𝔄 G N) (hN5 : 5 ≤ N) :
    ∃ φ : SteinbergGroup (Fin N) (horrB 𝔄) →* G,
      φ.comp (ringMap (I := Fin N) (Subring.inclusion (horrB0_le (𝔄 := 𝔄)))) = D.φ₀ ∧
      ∀ (i j : Fin N) (hij : i ≠ j) (a : A),
        φ (x i j hij ⟨AddMonoidAlgebra.single (-1) a,
          single_mem_horrB (allowed_of_nonneg (by norm_num) a)⟩) = D.T i j hij a := by
  obtain ⟨φ, hφ⟩ := exists_hom_of_rels_one D.rels hN5
  refine ⟨φ, ?_, fun i j hij a => ?_⟩
  · apply PresentedGroup.ext
    rintro ⟨i, j, hij, ⟨f, hf⟩⟩
    change φ (ringMap _ (x i j hij ⟨f, hf⟩)) = D.φ₀ (x i j hij ⟨f, hf⟩)
    rw [ringMap_x]
    have hincl : Subring.inclusion (horrB0_le (𝔄 := 𝔄)) ⟨f, hf⟩ = ⟨f, horrB0_le hf⟩ :=
      Subtype.ext (Subring.coe_inclusion _ _)
    rw [hincl]
    clear hincl
    induction f, hf using horrB0_induction with
    | zero =>
      have h0 : (⟨0, horrB0_le (horrB0 𝔄).zero_mem⟩ : horrB 𝔄) = 0 := rfl
      have h0' : (⟨0, (horrB0 𝔄).zero_mem⟩ : horrB0 𝔄) = 0 := rfl
      rw [h0, h0', x_zero, x_zero, map_one, map_one]
    | monomial n c hc =>
      have hall : Allowed 𝔄 (-(n : ℤ)) c := fun h => by
        rcases hc with rfl | hc
        · simp at h
        · exact hc
      rw [hφ i j hij n c hall (by omega), D.fam_nonpos hij (d := -(n : ℤ)) (by omega),
        show (-(-(n : ℤ))).toNat = n by omega, xMono_of hij hc]
    | add f g hf hg ihf ihg =>
      have e1 : (⟨f + g, horrB0_le ((horrB0 𝔄).add_mem hf hg)⟩ : horrB 𝔄) =
          ⟨f, horrB0_le hf⟩ + ⟨g, horrB0_le hg⟩ := rfl
      have e2 : (⟨f + g, (horrB0 𝔄).add_mem hf hg⟩ : horrB0 𝔄) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [e1, e2, ← x_mul, ← x_mul, map_mul, map_mul, ihf, ihg]
  · rw [hφ i j hij (-1) a (allowed_of_nonneg (by norm_num) a) (by norm_num),
      D.fam_pos hij (d := -(-1)) (by norm_num)]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.exists_hom_of_degOne

end Main

end Graded
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
