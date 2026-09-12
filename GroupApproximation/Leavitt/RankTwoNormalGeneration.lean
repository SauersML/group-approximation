import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Leavitt.ElementaryWeylMonomial

/-!
# Rank-two normal generation

`notes/rank-two-descent-note-2026-09-07.md`, §2.

> **Lemma.**  `wv = 1`, `ba = 1`, `bv = 0`.  Then
> `D = diag(1+vb, 1) = [e₁₂(v), e₂₁(b)]` normally generates `EL₂(R)`.

This is the engine of the rank descent: it needs no property `(T)`, no
countability, no simplicity and no normal-structure theorem, only three
one-sided relations in the coefficient ring.

The printed proof, zero-based:

1. the commutator is `diag(1+vb, 1)`, using only `bv = 0`;
2. `[D, e₀₁(ar)] = e₀₁(vr)`, using `ba = 1`, so every `e₀₁(vR)` is in the
   normal closure `N`;
3. `f = 1 - vw` is idempotent with `fv = wf = 0`, `g = vfw` is an orthogonal
   idempotent, and `z = vf + fw + 1 - f - g` satisfies `z² = 1` and `zf = vf`;
4. `diag(z, z⁻¹)` is a six-transvection word, so `h = diag(z,z) ∈ EL₂(R)`;
5. `h e₀₁(fr) h⁻¹ = e₀₁(zfrz) = e₀₁(v(frz)) ∈ N`, whence `e₀₁(fr) ∈ N`;
6. `e₀₁(r) = e₀₁(v(wr)) e₀₁(fr) ∈ N`; and
7. the Weyl element carries the upper roots onto the lower ones.

Since `z² = 1` the unit `z` is its own inverse, so the Whitehead word is
written here directly in terms of an element with `zz = 1` rather than through
`Rˣ`; that keeps every step an identity of matrices over `R`.
-/

namespace GroupApproximation
namespace RankDescent

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-! ## The two rank-two roots -/

/-- The upper elementary root `e₁₂(r)` of `EL₂(R)`, zero-based `e₀₁(r)`. -/
def upperRoot (r : R) : elementaryGroup (Fin 2) R :=
  elementaryRoot 0 1 (by decide) r

/-- The lower elementary root `e₂₁(r)` of `EL₂(R)`, zero-based `e₁₀(r)`. -/
def lowerRoot (r : R) : elementaryGroup (Fin 2) R :=
  elementaryRoot 1 0 (by decide) r

theorem upperRoot_mul (r₁ r₂ : R) :
    upperRoot r₁ * upperRoot r₂ = upperRoot (r₁ + r₂) :=
  elementaryRoot_mul _ _ _ _ _

theorem lowerRoot_mul (r₁ r₂ : R) :
    lowerRoot r₁ * lowerRoot r₂ = lowerRoot (r₁ + r₂) :=
  elementaryRoot_mul _ _ _ _ _

theorem upperRoot_neg (r : R) : upperRoot (-r) = (upperRoot r)⁻¹ :=
  elementaryRoot_neg _ _ _ _

theorem lowerRoot_neg (r : R) : lowerRoot (-r) = (lowerRoot r)⁻¹ :=
  elementaryRoot_neg _ _ _ _

/-! ## The printed generator `D = [e₁₂(v), e₂₁(b)]` -/

/-- **The printed rank-two normal generator.** -/
def gen (v b : R) : elementaryGroup (Fin 2) R := ⁅upperRoot v, lowerRoot b⁆

theorem gen_eq_word (v b : R) :
    gen v b = upperRoot v * lowerRoot b * upperRoot (-v) * lowerRoot (-b) := by
  show ⁅upperRoot v, lowerRoot b⁆ = _
  rw [commutatorElement_def, ← upperRoot_neg, ← lowerRoot_neg]

/-- **§2(3).**  `[e₁₂(v), e₂₁(b)] = diag(1+vb, 1)`, using only `bv = 0`. -/
theorem gen_val (v b : R) (hbv : b * v = 0) :
    ((gen v b : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
      = 1 + Matrix.single 0 0 (v * b) := by
  have hbv' : ∀ x : R, b * (v * x) = 0 := by
    intro x
    rw [← mul_assoc, hbv, zero_mul]
  rw [gen_eq_word]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [upperRoot, lowerRoot, elementaryRoot, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Matrix.single_apply, hbv, hbv', mul_add, add_mul, mul_assoc]

/-- Moving the generator past an upper root multiplies the coefficient by
`1 + vb` on the left. -/
theorem gen_mul_upperRoot (v b : R) (hbv : b * v = 0) (x : R) :
    gen v b * upperRoot x = upperRoot ((1 + v * b) * x) * gen v b := by
  have hd := gen_val v b hbv
  apply Subtype.ext
  apply Units.ext
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [hd, upperRoot, elementaryRoot, elementaryUnit, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.single_apply, add_mul,
      mul_add, mul_assoc]

theorem gen_conj_upperRoot (v b : R) (hbv : b * v = 0) (x : R) :
    gen v b * upperRoot x * (gen v b)⁻¹ = upperRoot ((1 + v * b) * x) := by
  have h := gen_mul_upperRoot v b hbv x
  calc gen v b * upperRoot x * (gen v b)⁻¹
      = gen v b * upperRoot x * (gen v b)⁻¹ := rfl
    _ = upperRoot ((1 + v * b) * x) * gen v b * (gen v b)⁻¹ := by rw [h]
    _ = upperRoot ((1 + v * b) * x) := by group

/-- **§2(4), first half.**  `[D, e₁₂(x)] = e₁₂(vbx)`. -/
theorem gen_commutator_upperRoot (v b : R) (hbv : b * v = 0) (x : R) :
    ⁅gen v b, upperRoot x⁆ = upperRoot (v * b * x) := by
  have h := gen_conj_upperRoot v b hbv x
  calc ⁅gen v b, upperRoot x⁆
      = gen v b * upperRoot x * (gen v b)⁻¹ * (upperRoot x)⁻¹ :=
        commutatorElement_def _ _
    _ = upperRoot ((1 + v * b) * x) * (upperRoot x)⁻¹ := by rw [h]
    _ = upperRoot ((1 + v * b) * x) * upperRoot (-x) := by rw [upperRoot_neg]
    _ = upperRoot ((1 + v * b) * x + -x) := upperRoot_mul _ _
    _ = upperRoot (v * b * x) := by congr 1; noncomm_ring

/-- **§2(4).**  `[D, e₁₂(ar)] = e₁₂(vr)`, so the normal closure of `D`
contains every `e₁₂(vr)`. -/
theorem gen_commutator_upperRoot_mul (v a b : R) (hbv : b * v = 0)
    (hba : b * a = 1) (r : R) :
    ⁅gen v b, upperRoot (a * r)⁆ = upperRoot (v * r) := by
  rw [gen_commutator_upperRoot v b hbv (a * r)]
  congr 1
  calc v * b * (a * r) = v * (b * a) * r := by noncomm_ring
    _ = v * r := by rw [hba, mul_one]

/-! ## §2(5): the involution -/

/-- The idempotent `f = 1 - vw`. -/
def fIdem (v w : R) : R := 1 - v * w

/-- The orthogonal idempotent `g = vfw`. -/
def gIdem (v w : R) : R := v * fIdem v w * w

/-- The involution `z = vf + fw + 1 - f - g`. -/
def zElt (v w : R) : R :=
  v * fIdem v w + fIdem v w * w + 1 - fIdem v w - gIdem v w

theorem zElt_eq (v w : R) :
    zElt v w =
      v * fIdem v w + fIdem v w * w + (1 - fIdem v w - gIdem v w) := by
  show v * fIdem v w + fIdem v w * w + 1 - fIdem v w - gIdem v w = _
  abel

section Idempotents

variable (v w : R)

theorem f_mul_v (hwv : w * v = 1) : fIdem v w * v = 0 := by
  show (1 - v * w) * v = 0
  calc (1 - v * w) * v = v - v * (w * v) := by noncomm_ring
    _ = 0 := by rw [hwv, mul_one, sub_self]

theorem w_mul_f (hwv : w * v = 1) : w * fIdem v w = 0 := by
  show w * (1 - v * w) = 0
  calc w * (1 - v * w) = w - w * v * w := by noncomm_ring
    _ = 0 := by rw [hwv, one_mul, sub_self]

theorem f_mul_f (hwv : w * v = 1) : fIdem v w * fIdem v w = fIdem v w := by
  have h : v * w * (v * w) = v * w := by
    calc v * w * (v * w) = v * (w * v) * w := by noncomm_ring
      _ = v * w := by rw [hwv, mul_one]
  show (1 - v * w) * (1 - v * w) = 1 - v * w
  calc (1 - v * w) * (1 - v * w) = 1 - v * w - v * w + v * w * (v * w) := by
        noncomm_ring
    _ = 1 - v * w := by rw [h]; abel

theorem gIdem_eq : gIdem v w = v * fIdem v w * w := rfl

theorem w_mul_g (hwv : w * v = 1) : w * gIdem v w = fIdem v w * w := by
  rw [gIdem_eq]
  calc w * (v * fIdem v w * w) = w * v * fIdem v w * w := by noncomm_ring
    _ = fIdem v w * w := by rw [hwv, one_mul]

theorem g_mul_v (hwv : w * v = 1) : gIdem v w * v = v * fIdem v w := by
  rw [gIdem_eq]
  calc v * fIdem v w * w * v = v * fIdem v w * (w * v) := by noncomm_ring
    _ = v * fIdem v w := by rw [hwv, mul_one]

theorem f_mul_g (hwv : w * v = 1) : fIdem v w * gIdem v w = 0 := by
  have hfv := f_mul_v v w hwv
  rw [gIdem_eq]
  calc fIdem v w * (v * fIdem v w * w) = fIdem v w * v * (fIdem v w * w) := by
        noncomm_ring
    _ = 0 := by rw [hfv, zero_mul]

theorem g_mul_f (hwv : w * v = 1) : gIdem v w * fIdem v w = 0 := by
  have hwf := w_mul_f v w hwv
  rw [gIdem_eq]
  calc v * fIdem v w * w * fIdem v w = v * fIdem v w * (w * fIdem v w) := by
        noncomm_ring
    _ = 0 := by rw [hwf, mul_zero]

theorem g_mul_g (hwv : w * v = 1) : gIdem v w * gIdem v w = gIdem v w := by
  have hwg := w_mul_g v w hwv
  have hff := f_mul_f v w hwv
  rw [gIdem_eq]
  calc v * fIdem v w * w * (v * fIdem v w * w)
      = v * fIdem v w * (w * v) * fIdem v w * w := by noncomm_ring
    _ = v * (fIdem v w * fIdem v w) * w := by rw [hwv]; noncomm_ring
    _ = v * fIdem v w * w := by rw [hff]

end Idempotents

/-- The multiplication table of §2(5), assembled: three elements whose
pairwise products are those of a `2 × 2` matrix unit system plus a
complementary idempotent square to `1` when summed. -/
theorem sq_eq_one_of_table {S : Type*} [Ring S] {p q c f g : S}
    (hpp : p * p = 0) (hpq : p * q = g) (hpc : p * c = 0)
    (hqp : q * p = f) (hqq : q * q = 0) (hqc : q * c = 0)
    (hcp : c * p = 0) (hcq : c * q = 0) (hcc : c * c = c)
    (hc : c = 1 - f - g) :
    (p + q + c) * (p + q + c) = 1 := by
  calc (p + q + c) * (p + q + c)
      = p * p + p * q + p * c + q * p + q * q + q * c
        + c * p + c * q + c * c := by noncomm_ring
    _ = 0 + g + 0 + f + 0 + 0 + 0 + 0 + c := by
        rw [hpp, hpq, hpc, hqp, hqq, hqc, hcp, hcq, hcc]
    _ = 1 := by rw [hc]; abel

section Involution

variable (v w : R)

/-- **§2(5).**  `z² = 1`. -/
theorem zElt_mul_zElt (hwv : w * v = 1) : zElt v w * zElt v w = 1 := by
  have hfv := f_mul_v v w hwv
  have hwf := w_mul_f v w hwv
  have hff := f_mul_f v w hwv
  have hfg := f_mul_g v w hwv
  have hgf := g_mul_f v w hwv
  have hwg := w_mul_g v w hwv
  have hgv := g_mul_v v w hwv
  have hpp : v * fIdem v w * (v * fIdem v w) = 0 := by
    calc v * fIdem v w * (v * fIdem v w)
        = v * (fIdem v w * v) * fIdem v w := by noncomm_ring
      _ = 0 := by rw [hfv]; noncomm_ring
  have hpq : v * fIdem v w * (fIdem v w * w) = gIdem v w := by
    rw [gIdem_eq]
    calc v * fIdem v w * (fIdem v w * w)
        = v * (fIdem v w * fIdem v w) * w := by noncomm_ring
      _ = v * fIdem v w * w := by rw [hff]
  have hqp : fIdem v w * w * (v * fIdem v w) = fIdem v w := by
    calc fIdem v w * w * (v * fIdem v w)
        = fIdem v w * (w * v) * fIdem v w := by noncomm_ring
      _ = fIdem v w * fIdem v w := by rw [hwv, mul_one]
      _ = fIdem v w := hff
  have hqq : fIdem v w * w * (fIdem v w * w) = 0 := by
    calc fIdem v w * w * (fIdem v w * w)
        = fIdem v w * (w * fIdem v w) * w := by noncomm_ring
      _ = 0 := by rw [hwf]; noncomm_ring
  have hpc : v * fIdem v w * (1 - fIdem v w - gIdem v w) = 0 := by
    calc v * fIdem v w * (1 - fIdem v w - gIdem v w)
        = v * fIdem v w - v * (fIdem v w * fIdem v w)
          - v * (fIdem v w * gIdem v w) := by noncomm_ring
      _ = 0 := by rw [hff, hfg]; noncomm_ring
  have hqc : fIdem v w * w * (1 - fIdem v w - gIdem v w) = 0 := by
    calc fIdem v w * w * (1 - fIdem v w - gIdem v w)
        = fIdem v w * w - fIdem v w * (w * fIdem v w)
          - fIdem v w * (w * gIdem v w) := by noncomm_ring
      _ = fIdem v w * w - fIdem v w * 0 - fIdem v w * (fIdem v w * w) := by
          rw [hwf, hwg]
      _ = fIdem v w * w - fIdem v w * fIdem v w * w := by noncomm_ring
      _ = 0 := by rw [hff]; noncomm_ring
  have hcp : (1 - fIdem v w - gIdem v w) * (v * fIdem v w) = 0 := by
    calc (1 - fIdem v w - gIdem v w) * (v * fIdem v w)
        = v * fIdem v w - fIdem v w * v * fIdem v w
          - gIdem v w * v * fIdem v w := by noncomm_ring
      _ = v * fIdem v w - 0 * fIdem v w - v * fIdem v w * fIdem v w := by
          rw [hfv, hgv]
      _ = v * (fIdem v w - fIdem v w * fIdem v w) := by noncomm_ring
      _ = 0 := by rw [hff]; noncomm_ring
  have hcq : (1 - fIdem v w - gIdem v w) * (fIdem v w * w) = 0 := by
    calc (1 - fIdem v w - gIdem v w) * (fIdem v w * w)
        = fIdem v w * w - fIdem v w * fIdem v w * w
          - gIdem v w * fIdem v w * w := by noncomm_ring
      _ = fIdem v w * w - fIdem v w * w - 0 * w := by rw [hff, hgf]
      _ = 0 := by noncomm_ring
  have hcc : (1 - fIdem v w - gIdem v w) * (1 - fIdem v w - gIdem v w)
      = 1 - fIdem v w - gIdem v w := by
    have hgg := g_mul_g v w hwv
    calc (1 - fIdem v w - gIdem v w) * (1 - fIdem v w - gIdem v w)
        = 1 - fIdem v w - gIdem v w - fIdem v w + fIdem v w * fIdem v w
          + fIdem v w * gIdem v w - gIdem v w + gIdem v w * fIdem v w
          + gIdem v w * gIdem v w := by noncomm_ring
      _ = 1 - fIdem v w - gIdem v w := by rw [hff, hfg, hgf, hgg]; abel
  rw [zElt_eq]
  exact sq_eq_one_of_table hpp hpq hpc hqp hqq hqc hcp hcq hcc rfl

/-- **§2(5).**  `zf = vf`. -/
theorem zElt_mul_fIdem (hwv : w * v = 1) :
    zElt v w * fIdem v w = v * fIdem v w := by
  have hwf := w_mul_f v w hwv
  have hff := f_mul_f v w hwv
  have hgf := g_mul_f v w hwv
  rw [zElt_eq]
  calc (v * fIdem v w + fIdem v w * w + (1 - fIdem v w - gIdem v w))
        * fIdem v w
      = v * (fIdem v w * fIdem v w) + fIdem v w * (w * fIdem v w)
        + fIdem v w - fIdem v w * fIdem v w
        - gIdem v w * fIdem v w := by noncomm_ring
    _ = v * fIdem v w + fIdem v w * 0 + fIdem v w - fIdem v w - 0 := by
        rw [hff, hwf, hgf]
    _ = v * fIdem v w := by noncomm_ring

end Involution

/-! ## §2(6): the Whitehead diagonal of an involution -/

/-- The three-transvection Whitehead word at an element with `zz = 1`. -/
def whiteheadThree (z : R) : elementaryGroup (Fin 2) R :=
  upperRoot z * lowerRoot (-z) * upperRoot z

theorem whiteheadThree_val (z : R) (hz : z * z = 1) :
    ((whiteheadThree z : (Matrix (Fin 2) (Fin 2) R)ˣ) :
        Matrix (Fin 2) (Fin 2) R) = !![0, z; -z, 0] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [whiteheadThree, upperRoot, lowerRoot, elementaryRoot, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Matrix.single_apply, hz, mul_add, add_mul, mul_assoc]

/-- **§2(6).**  `diag(z, z⁻¹) = diag(z, z)` as a six-transvection word, so it
lies in `EL₂(R)` by construction. -/
def involutionDiag (z : R) : elementaryGroup (Fin 2) R :=
  whiteheadThree z * whiteheadThree (-1)

theorem involutionDiag_val (z : R) (hz : z * z = 1) :
    ((involutionDiag z : (Matrix (Fin 2) (Fin 2) R)ˣ) :
        Matrix (Fin 2) (Fin 2) R) = !![z, 0; 0, z] := by
  have h1 := whiteheadThree_val z hz
  have h2 := whiteheadThree_val (-1 : R) (by noncomm_ring)
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [involutionDiag, h1, h2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem involutionDiag_mul_upperRoot (z : R) (hz : z * z = 1) (x : R) :
    involutionDiag z * upperRoot x = upperRoot (z * x * z) * involutionDiag z := by
  have hd := involutionDiag_val z hz
  apply Subtype.ext
  apply Units.ext
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [hd, upperRoot, elementaryRoot, elementaryUnit, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.single_apply, hz, mul_assoc]

/-- **§2(7).**  `h e₁₂(x) h⁻¹ = e₁₂(zxz)`. -/
theorem involutionDiag_conj_upperRoot (z : R) (hz : z * z = 1) (x : R) :
    involutionDiag z * upperRoot x * (involutionDiag z)⁻¹
      = upperRoot (z * x * z) := by
  have h := involutionDiag_mul_upperRoot z hz x
  calc involutionDiag z * upperRoot x * (involutionDiag z)⁻¹
      = upperRoot (z * x * z) * involutionDiag z * (involutionDiag z)⁻¹ := by
        rw [h]
    _ = upperRoot (z * x * z) := by group

/-! ## The rank-two normal generation lemma -/

/-- **§2, the Lemma.**  With `wv = 1`, `ba = 1` and `bv = 0`, the printed
generator `D = [e₁₂(v), e₂₁(b)]` normally generates `EL₂(R)`.

No property `(T)`, no countability, no simplicity, and no normal-structure
theorem is used; the whole proof is the seven displayed steps of the note. -/
theorem normalClosure_gen_eq_top (v w a b : R)
    (hwv : w * v = 1) (hba : b * a = 1) (hbv : b * v = 0) :
    Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R)) = ⊤ := by
  set N := Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R))
    with hNdef
  haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
  have hDmem : gen v b ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  -- every commutator with the generator stays in the normal closure
  have hcomm_mem : ∀ x : elementaryGroup (Fin 2) R, ⁅gen v b, x⁆ ∈ N := by
    intro x
    have h1 : x * (gen v b)⁻¹ * x⁻¹ ∈ N :=
      hNnormal.conj_mem _ (N.inv_mem hDmem) x
    have h2 : gen v b * (x * (gen v b)⁻¹ * x⁻¹) ∈ N := N.mul_mem hDmem h1
    have h3 : ⁅gen v b, x⁆ = gen v b * (x * (gen v b)⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rwa [h3]
  -- §2(4)
  have hup_v : ∀ r : R, upperRoot (v * r) ∈ N := by
    intro r
    have h := hcomm_mem (upperRoot (a * r))
    rwa [gen_commutator_upperRoot_mul v a b hbv hba r] at h
  -- §2(5)-(7)
  have hz : zElt v w * zElt v w = 1 := zElt_mul_zElt v w hwv
  have hzf : zElt v w * fIdem v w = v * fIdem v w := zElt_mul_fIdem v w hwv
  have hup_f : ∀ r : R, upperRoot (fIdem v w * r) ∈ N := by
    intro r
    have hval : zElt v w * (fIdem v w * r) * zElt v w
        = v * (fIdem v w * r * zElt v w) := by
      calc zElt v w * (fIdem v w * r) * zElt v w
          = zElt v w * fIdem v w * (r * zElt v w) := by noncomm_ring
        _ = v * fIdem v w * (r * zElt v w) := by rw [hzf]
        _ = v * (fIdem v w * r * zElt v w) := by noncomm_ring
    have hmem : involutionDiag (zElt v w) * upperRoot (fIdem v w * r) *
        (involutionDiag (zElt v w))⁻¹ ∈ N := by
      rw [involutionDiag_conj_upperRoot _ hz, hval]
      exact hup_v _
    have hback := hNnormal.conj_mem _ hmem (involutionDiag (zElt v w))⁻¹
    have hsimp : (involutionDiag (zElt v w))⁻¹ *
        (involutionDiag (zElt v w) * upperRoot (fIdem v w * r) *
          (involutionDiag (zElt v w))⁻¹) *
        ((involutionDiag (zElt v w))⁻¹)⁻¹ = upperRoot (fIdem v w * r) := by
      group
    rwa [hsimp] at hback
  have hup : ∀ r : R, upperRoot r ∈ N := by
    intro r
    have hsplit : upperRoot (v * (w * r)) * upperRoot (fIdem v w * r)
        = upperRoot r := by
      rw [upperRoot_mul]
      congr 1
      show v * (w * r) + (1 - v * w) * r = r
      noncomm_ring
    rw [← hsplit]
    exact N.mul_mem (hup_v _) (hup_f r)
  -- §2(7), the Weyl conjugation onto the lower roots
  have hlo : ∀ r : R, lowerRoot r ∈ N := by
    intro r
    have hmemconj : ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) * upperRoot r *
        (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ ∈ N :=
      hNnormal.conj_mem _ (hup r) _
    rcases ElementaryWeyl.weyl_conj_elGen (S := R) (0 : Fin 2) 1 (by decide)
      (p := 0) (q := 1) (by decide)
      (Equiv.swap_apply_left (0 : Fin 2) 1)
      (Equiv.swap_apply_right (0 : Fin 2) 1) (by decide) r with h | h
    · rw [show lowerRoot r = ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) *
        upperRoot r * (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ from h.symm]
      exact hmemconj
    · have hneg : lowerRoot (-r) ∈ N := by
        rw [show lowerRoot (-r) = ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) *
          upperRoot r * (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ from h.symm]
        exact hmemconj
      have hinv : lowerRoot r = (lowerRoot (-r))⁻¹ := by
        rw [lowerRoot_neg, inv_inv]
      rw [hinv]
      exact N.inv_mem hneg
  -- the roots generate
  have hle : Subgroup.closure (elementaryRootSet (Fin 2) R) ≤ N := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, j, hij, hx⟩
    obtain ⟨r, rfl⟩ := (mem_elementaryRootSubgroup_iff i j hij x).mp hx
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hup r
    · exact hlo r
    · exact absurd rfl hij
  have htop : Subgroup.closure (elementaryRootSet (Fin 2) R) = ⊤ :=
    elementaryRootSet_generate
  apply top_unique
  rw [← htop]
  exact hle

end RankDescent
end GroupApproximation
