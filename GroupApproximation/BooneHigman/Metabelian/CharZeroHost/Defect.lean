import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Action

/-!
# The `p`-adic defect of a fixing affine map (lane bh-met-09)

Research claim (faithfulness, first half): if `x = (g, b)` acts trivially on `X^*`, then for all
natural parameters `s ∈ ℕ^k` and digit vectors `e ∈ ℕ^n`, the defect
`Zv x e (s) = g(s) e + b(s) - e ∈ A^n` is divisible by every power of `p`.

**Route.** Write `e = (e mod p) + p e'`, `s = (s mod p) + p s'` and let `ℓ` be the letter of
the residues.  Since `x` fixes `ℓ`, the output digit is `e mod p`, so
`Zv x e = z x ℓ + p (g e' - e')` (`Zv_eq`).  Applying `σ_ℓ` gives
`σ_ℓ (Zv x e) = p · Zv (stateG x ℓ) e'` (`sigma_Zv`), and `evalN s' ∘ σ_ℓ = evalN s`
(`evalN_sigma`, from `s mod p + p (s / p) = s`).  The state also fixes `X^*` (`fix_cons`), so
induction on the exponent closes `pow_dvd_evalN_Zv`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial
open scoped Matrix

variable {A : Type*} [CommRing A] {n k : ℕ}

/-- Natural-number vectors as constant polynomial vectors. -/
def natVec (e : Fin n → ℕ) : Fin n → MvPolynomial (Fin k) A :=
  fun j => ((e j : ℕ) : MvPolynomial (Fin k) A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.natVec

/-- The defect vector `g e + b - e`. -/
def Zv (x : Aff n (MvPolynomial (Fin k) A)) (e : Fin n → ℕ) : Fin n → MvPolynomial (Fin k) A :=
  mat x *ᵥ natVec e + vec x - natVec e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Zv

theorem natVec_zero : (natVec (0 : Fin n → ℕ) : Fin n → MvPolynomial (Fin k) A) = 0 :=
  funext fun _ => Nat.cast_zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.natVec_zero

theorem natVec_single (j0 : Fin n) :
    (natVec (Pi.single j0 1) : Fin n → MvPolynomial (Fin k) A) = Pi.single j0 1 := by
  funext j
  have h := Pi.apply_single (fun _ (m : ℕ) => ((m : ℕ) : MvPolynomial (Fin k) A))
    (fun _ => Nat.cast_zero) j0 1 j
  rw [Nat.cast_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.natVec_single

theorem apply_natVec (f : MvPolynomial (Fin k) A →+* MvPolynomial (Fin k) A)
    (e : Fin n → ℕ) (j : Fin n) : f (natVec e j) = natVec e j :=
  map_natCast f (e j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.apply_natVec

theorem comp_natVec (f : MvPolynomial (Fin k) A →+* MvPolynomial (Fin k) A) (e : Fin n → ℕ) :
    ⇑f ∘ natVec e = natVec e :=
  funext (apply_natVec f e)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.comp_natVec

variable (p : ℕ)

/-- The letter of residues `(e mod p, s mod p)`. -/
def digL (e : Fin n → ℕ) (s : Fin k → ℕ) : Letter p n k :=
  (fun j => ((e j : ℕ) : ZMod p), fun i => ((s i : ℕ) : ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.digL

theorem castVec_digL (e : Fin n → ℕ) (s : Fin k → ℕ) :
    (castVec (digL p e s).1 : Fin n → MvPolynomial (Fin k) A) = natVec fun j => e j % p :=
  funext fun j => congrArg (Nat.cast : ℕ → MvPolynomial (Fin k) A) (ZMod.val_natCast p (e j))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.castVec_digL

theorem sigmaZ_digL (e : Fin n → ℕ) (s : Fin k → ℕ) :
    (sigmaZ p (digL p e s).2 : MvPolynomial (Fin k) A →+* MvPolynomial (Fin k) A) =
      sigma p fun i => s i % p :=
  congrArg (sigma p) (funext fun i => ZMod.val_natCast p (s i))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigmaZ_digL

theorem natVec_split (e : Fin n → ℕ) :
    (natVec e : Fin n → MvPolynomial (Fin k) A) =
      natVec (fun j => e j % p) + (p : MvPolynomial (Fin k) A) • natVec fun j => e j / p := by
  funext j
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  show ((e j : ℕ) : MvPolynomial (Fin k) A) = ((e j % p : ℕ) : MvPolynomial (Fin k) A) +
    (p : MvPolynomial (Fin k) A) * ((e j / p : ℕ) : MvPolynomial (Fin k) A)
  rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.natVec_split

/-- `evalN (s / p) ∘ σ_{s mod p} = evalN s`. -/
theorem evalN_sigma (s : Fin k → ℕ) (P : MvPolynomial (Fin k) A) :
    evalN (fun i => s i / p) (sigma p (fun i => s i % p) P) = evalN s P := by
  have h : (evalN fun i => s i / p).comp (sigma p fun i => s i % p) =
      (evalN s : MvPolynomial (Fin k) A →+* A) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, sigma_C, evalN_C, evalN_C]
    · rw [RingHom.comp_apply, sigma_X, map_add, map_mul, map_natCast, map_natCast, evalN_X,
        evalN_X, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  exact RingHom.congr_fun h P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.evalN_sigma

variable {p} (D : DigitData A p)

/-- A map fixing `X^*` fixes each letter, and its states fix `X^*`. -/
theorem fix_cons {x : Aff n (MvPolynomial (Fin k) A)} (hx : ∀ w, act D x w = w)
    (ℓ : Letter p n k) : letter D x ℓ = ℓ ∧ ∀ w, act D (stateG D x ℓ) w = w :=
  ⟨(List.cons.inj ((act_cons D x ℓ []).symm.trans (hx [ℓ]))).1,
    fun w => (List.cons.inj ((act_cons D x ℓ w).symm.trans (hx (ℓ :: w)))).2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.fix_cons

theorem Zv_eq (x : Aff n (MvPolynomial (Fin k) A)) (e : Fin n → ℕ) (s : Fin k → ℕ)
    (hfix : outDigit D x (digL p e s) = (digL p e s).1) :
    Zv x e = z D x (digL p e s) + (p : MvPolynomial (Fin k) A) •
      (mat x *ᵥ natVec (fun j => e j / p) - natVec fun j => e j / p) := by
  rw [Zv, z, hfix, castVec_digL, natVec_split p e, Matrix.mulVec_add, Matrix.mulVec_smul,
    smul_sub]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Zv_eq

variable [NeZero p]

theorem sigma_Zv (x : Aff n (MvPolynomial (Fin k) A)) (e : Fin n → ℕ) (s : Fin k → ℕ)
    (hfix : outDigit D x (digL p e s) = (digL p e s).1) :
    ⇑(sigmaZ p (digL p e s).2) ∘ Zv x e =
      (p : MvPolynomial (Fin k) A) • Zv (stateG D x (digL p e s)) fun j => e j / p := by
  funext j
  have hz := sigmaZ_z D x (digL p e s) j
  rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Zv_eq D x e s hfix, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_natCast, hz, ← mul_add]
  congr 1
  have hW : sigmaZ p (digL p e s).2
      ((mat x *ᵥ natVec (fun j => e j / p) - natVec fun j => e j / p) j) =
      ((mat x).map (sigmaZ p (digL p e s).2) *ᵥ natVec (fun j => e j / p) -
        natVec fun j => e j / p) j := by
    rw [Pi.sub_apply, Pi.sub_apply, map_sub, RingHom.map_mulVec, comp_natVec, apply_natVec]
  have hm : mat (stateG D x (digL p e s)) = (mat x).map (sigmaZ p (digL p e s).2) := rfl
  have hv : vec (stateG D x (digL p e s)) = stateVec D x (digL p e s) := rfl
  rw [hW, Zv, hm, hv]
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigma_Zv

/-- **Defect divisibility**: the defect of a map fixing `X^*` is divisible by all `p ^ N`. -/
theorem pow_dvd_evalN_Zv (N : ℕ) : ∀ x : Aff n (MvPolynomial (Fin k) A),
    (∀ w, act D x w = w) → ∀ (s : Fin k → ℕ) (e : Fin n → ℕ) (j : Fin n),
      (p : A) ^ N ∣ evalN s (Zv x e j) := by
  induction N with
  | zero => intro x _ s e j; rw [pow_zero]; exact one_dvd _
  | succ N ih =>
    intro x hx s e j
    obtain ⟨hl, hs⟩ := fix_cons D hx (digL p e s)
    have h1 := congrFun (sigma_Zv D x e s (congrArg Prod.fst hl)) j
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
    obtain ⟨c, hc⟩ := ih _ hs (fun i => s i / p) (fun j => e j / p) j
    refine ⟨c, ?_⟩
    rw [← evalN_sigma p s (Zv x e j), ← sigmaZ_digL p e s, h1, map_mul, map_natCast, hc]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.pow_dvd_evalN_Zv

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
