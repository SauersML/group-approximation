import GroupApproximation.CharClass.OddPShuffle
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Multiplication by a unit mod `p` normalises the cyclic rotation of the tensor power

For `r` coprime to `p`, `mulPerm p r hr : Equiv.Perm (Fin p)` is `i ↦ r·i mod p`.  The rotation
`finRotate p` is `i ↦ i + 1`, so `r·(i + s) = r·i + r·s`:

* `mulPerm_mul_finRotate_pow` — `mulPerm r * finRotate ^ s = finRotate ^ (r·s) * mulPerm r`;
* `mulPerm_mul_finRotate` — `mulPerm r * finRotate = finRotate ^ r * mulPerm r`;
* `mulPerm_inv_mul_finRotate_pow` — `(mulPerm r)⁻¹ * finRotate ^ r = finRotate * (mulPerm r)⁻¹`;
* `mulPerm_mul_finRotate_pow_of_mul_mod_eq_one` — `mulPerm r * finRotate ^ s = finRotate * mulPerm r`
  when `r·s ≡ 1 (mod p)`.

On the tensor power, `tupPermAll π * tupPermAll ρ = tupPermAll (ρ * π)` and
`tupTAll = tupPermAll (finRotate p)` (`OddPShuffle.lean`).  Since the identities above are identities
of permutations, they transfer with their signs:

* `tupTAll_mul_tupPermAll_mulPerm` — `T * P(mulPerm r) = P(mulPerm r) * T ^ r`;
* `tupTAll_pow_mul_tupPermAll_mulPerm_inv` — `T ^ r * P((mulPerm r)⁻¹) = P((mulPerm r)⁻¹) * T`, where
  `P((mulPerm r)⁻¹)` is the slot action `t ↦ t ∘ (mulPerm r)⁻¹` (σ_r of the vanishing lemma);
* `tupTAll_pow_mul_tupPermAll_mulPerm` — `T ^ s * P(mulPerm r) = P(mulPerm r) * T` when `r·s ≡ 1`;
* the degree-`k` twins `tupT_mul_tupPerm_mulPerm`, `tupT_pow_mul_tupPerm_mulPerm_inv`.

Every identity of this file was model-tested on MSI (`notes/lix-strong-swarm/tools/redpow_mulperm_test.py`),
for every `p ≤ 13` and every unit `r`, at the level of permutations and of slot actions on tuples.  The
tempting form `T ^ r * P(mulPerm r) = P(mulPerm r) * T` is the control: it says `M * R ^ r = R * M`, which
holds only when `r² ≡ 1 (mod p)`.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Multiplication by a unit, and powers of the rotation -/

section Perms

/-- The map `i ↦ r·i mod p` on `Fin p`. -/
def mulPermFun (p r : ℕ) (i : Fin p) : Fin p :=
  ⟨r * i.val % p, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

theorem mulPermFun_injective (p r : ℕ) (hr : Nat.Coprime r p) :
    Function.Injective (mulPermFun p r) := by
  intro a b h
  have h1 : r * a.val % p = r * b.val % p := congrArg Fin.val h
  have h2 : Nat.ModEq p a.val b.val := Nat.ModEq.cancel_left_of_coprime hr.symm h1
  have h3 : a.val % p = b.val % p := h2
  rw [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h3
  exact Fin.ext h3

/-- **Multiplication by `r` coprime to `p`**, as a permutation of `Fin p`. -/
def mulPerm (p r : ℕ) (hr : Nat.Coprime r p) : Equiv.Perm (Fin p) :=
  Equiv.ofBijective (mulPermFun p r)
    (Finite.injective_iff_bijective.mp (mulPermFun_injective p r hr))

@[simp] theorem mulPerm_val (p r : ℕ) (hr : Nat.Coprime r p) (i : Fin p) :
    ((mulPerm p r hr i : Fin p) : ℕ) = r * i.val % p :=
  rfl

/-- The powers of the rotation: `finRotate p ^ k` is `i ↦ i + k mod p`. -/
theorem finRotate_pow_val {p : ℕ} (k : ℕ) (i : Fin p) :
    (((finRotate p ^ k) i : Fin p) : ℕ) = (i.val + k) % p := by
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply, Nat.add_zero, Nat.mod_eq_of_lt i.2]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_val_eq, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Two powers of the rotation agree when their exponents agree mod `p`. -/
theorem finRotate_pow_eq_of_mod_eq {p k l : ℕ} (h : k % p = l % p) :
    finRotate p ^ k = finRotate p ^ l := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [finRotate_pow_val, finRotate_pow_val, Nat.add_mod, h, ← Nat.add_mod]

/-- **Multiplication by `r` turns a rotation by `s` into a rotation by `r·s`.** -/
theorem mulPerm_mul_finRotate_pow (p r : ℕ) (hr : Nat.Coprime r p) (s : ℕ) :
    mulPerm p r hr * finRotate p ^ s = finRotate p ^ (r * s) * mulPerm p r hr := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, mulPerm_val, finRotate_pow_val,
    finRotate_pow_val, mulPerm_val, Nat.mul_mod_mod, Nat.mod_add_mod, Nat.mul_add]

/-- **`mulPerm r * finRotate = finRotate ^ r * mulPerm r`.** -/
theorem mulPerm_mul_finRotate (p r : ℕ) (hr : Nat.Coprime r p) :
    mulPerm p r hr * finRotate p = finRotate p ^ r * mulPerm p r hr := by
  have h := mulPerm_mul_finRotate_pow p r hr 1
  rwa [pow_one, Nat.mul_one] at h

/-- **The inverse form**: `(mulPerm r)⁻¹ * finRotate ^ r = finRotate * (mulPerm r)⁻¹`. -/
theorem mulPerm_inv_mul_finRotate_pow (p r : ℕ) (hr : Nat.Coprime r p) :
    (mulPerm p r hr)⁻¹ * finRotate p ^ r = finRotate p * (mulPerm p r hr)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, mulPerm_mul_finRotate, mul_assoc, mul_inv_cancel,
    mul_one]

/-- With `r·s ≡ 1 (mod p)`, multiplication by `r` carries the rotation by `s` to the rotation by one. -/
theorem mulPerm_mul_finRotate_pow_of_mul_mod_eq_one {p r s : ℕ} (hr : Nat.Coprime r p)
    (hrs : r * s % p = 1 % p) :
    mulPerm p r hr * finRotate p ^ s = finRotate p * mulPerm p r hr := by
  rw [mulPerm_mul_finRotate_pow, finRotate_pow_eq_of_mod_eq hrs, pow_one]

/-- Multiplications compose by multiplying the residues. -/
theorem mulPerm_mul_mulPerm (p r s : ℕ) (hr : Nat.Coprime r p) (hs : Nat.Coprime s p) :
    mulPerm p r hr * mulPerm p s hs = mulPerm p (r * s) (Nat.Coprime.mul_left hr hs) := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, mulPerm_val, mulPerm_val, mulPerm_val, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Multiplication by a residue `≡ 1` is the identity. -/
theorem mulPerm_eq_one_of_mod_eq_one {p r : ℕ} (hr : Nat.Coprime r p) (h : r % p = 1 % p) :
    mulPerm p r hr = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [mulPerm_val, Equiv.Perm.one_apply, Nat.mul_mod, h, ← Nat.mul_mod, Nat.one_mul,
    Nat.mod_eq_of_lt i.2]

/-- The inverse of multiplication by `r` is multiplication by an inverse residue. -/
theorem mulPerm_inv_eq {p r s : ℕ} (hr : Nat.Coprime r p) (hs : Nat.Coprime s p)
    (hrs : r * s % p = 1 % p) : (mulPerm p r hr)⁻¹ = mulPerm p s hs := by
  apply Eq.symm
  apply eq_inv_of_mul_eq_one_left
  rw [mulPerm_mul_mulPerm]
  exact mulPerm_eq_one_of_mod_eq_one _ (by rw [Nat.mul_comm]; exact hrs)

end Perms

/-! ## 2. The tensor power -/

section FullModel

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- Powers of a signed slot permutation are the slot permutations of the powers. -/
theorem tupPermAll_pow {r : ℕ} (π : Equiv.Perm (Fin r)) (m : ℕ) :
    tupPermAll K X r π ^ m = tupPermAll K X r (π ^ m) := by
  induction m with
  | zero => simp only [pow_zero, tupPermAll_one]
  | succ m ih => rw [pow_succ' (tupPermAll K X r π) m, ih, tupPermAll_mul, ← pow_succ π m]

/-- **`T * P(mulPerm r) = P(mulPerm r) * T ^ r`** on the full model. -/
theorem tupTAll_mul_tupPermAll_mulPerm {p : ℕ} (r : ℕ) (hr : Nat.Coprime r p) :
    tupTAll K X p * tupPermAll K X p (mulPerm p r hr)
      = tupPermAll K X p (mulPerm p r hr) * tupTAll K X p ^ r := by
  rw [tupTAll_eq_tupPermAll, tupPermAll_pow, tupPermAll_mul, tupPermAll_mul, mulPerm_mul_finRotate]

/-- **`T ^ r * σ_r = σ_r * T`** for the slot action `σ_r = P((mulPerm r)⁻¹)`, `t ↦ t ∘ (mulPerm r)⁻¹`. -/
theorem tupTAll_pow_mul_tupPermAll_mulPerm_inv {p : ℕ} (r : ℕ) (hr : Nat.Coprime r p) :
    tupTAll K X p ^ r * tupPermAll K X p (mulPerm p r hr)⁻¹
      = tupPermAll K X p (mulPerm p r hr)⁻¹ * tupTAll K X p := by
  rw [tupTAll_eq_tupPermAll, tupPermAll_pow, tupPermAll_mul, tupPermAll_mul,
    mulPerm_inv_mul_finRotate_pow]

/-- **`T ^ s * P(mulPerm r) = P(mulPerm r) * T`** when `r·s ≡ 1 (mod p)`. -/
theorem tupTAll_pow_mul_tupPermAll_mulPerm {p : ℕ} (r s : ℕ) (hr : Nat.Coprime r p)
    (hrs : r * s % p = 1 % p) :
    tupTAll K X p ^ s * tupPermAll K X p (mulPerm p r hr)
      = tupPermAll K X p (mulPerm p r hr) * tupTAll K X p := by
  rw [tupTAll_eq_tupPermAll, tupPermAll_pow, tupPermAll_mul, tupPermAll_mul,
    mulPerm_mul_finRotate_pow_of_mul_mod_eq_one hr hrs]

/-! ## 3. Degree `k` -/

/-- The trivial slot permutation in degree `k`. -/
theorem tupPerm_one {r : ℕ} (k : ℕ) : tupPerm K X r k 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply tupIncl_injective K X k
  have h := LinearMap.congr_fun (tupIncl_comp_tupPerm K X k (1 : Equiv.Perm (Fin r))) x
  simp only [LinearMap.comp_apply] at h
  rw [h, tupPermAll_one, Module.End.one_apply, Module.End.one_apply]

/-- Powers of a slot permutation in degree `k`. -/
theorem tupPerm_pow {r : ℕ} (k : ℕ) (π : Equiv.Perm (Fin r)) (m : ℕ) :
    tupPerm K X r k π ^ m = tupPerm K X r k (π ^ m) := by
  induction m with
  | zero => simp only [pow_zero, tupPerm_one]
  | succ m ih => rw [pow_succ' (tupPerm K X r k π) m, ih, tupPerm_mul, ← pow_succ π m]

/-- **`T * P(mulPerm r) = P(mulPerm r) * T ^ r`** in degree `k`. -/
theorem tupT_mul_tupPerm_mulPerm {p : ℕ} (k r : ℕ) (hr : Nat.Coprime r p) :
    tupT K X p k * tupPerm K X p k (mulPerm p r hr)
      = tupPerm K X p k (mulPerm p r hr) * tupT K X p k ^ r := by
  rw [tupT_eq_tupPerm, tupPerm_pow, tupPerm_mul, tupPerm_mul, mulPerm_mul_finRotate]

/-- **`T ^ r * σ_r = σ_r * T`** in degree `k`. -/
theorem tupT_pow_mul_tupPerm_mulPerm_inv {p : ℕ} (k r : ℕ) (hr : Nat.Coprime r p) :
    tupT K X p k ^ r * tupPerm K X p k (mulPerm p r hr)⁻¹
      = tupPerm K X p k (mulPerm p r hr)⁻¹ * tupT K X p k := by
  rw [tupT_eq_tupPerm, tupPerm_pow, tupPerm_mul, tupPerm_mul, mulPerm_inv_mul_finRotate_pow]

end FullModel

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms mulPerm
#audit_axioms finRotate_pow_val
#audit_axioms mulPerm_mul_finRotate_pow
#audit_axioms mulPerm_mul_finRotate
#audit_axioms mulPerm_inv_mul_finRotate_pow
#audit_axioms mulPerm_mul_finRotate_pow_of_mul_mod_eq_one
#audit_axioms mulPerm_mul_mulPerm
#audit_axioms mulPerm_inv_eq
#audit_axioms tupPermAll_pow
#audit_axioms tupTAll_mul_tupPermAll_mulPerm
#audit_axioms tupTAll_pow_mul_tupPermAll_mulPerm_inv
#audit_axioms tupTAll_pow_mul_tupPermAll_mulPerm
#audit_axioms tupPerm_one
#audit_axioms tupPerm_pow
#audit_axioms tupT_mul_tupPerm_mulPerm
#audit_axioms tupT_pow_mul_tupPerm_mulPerm_inv
