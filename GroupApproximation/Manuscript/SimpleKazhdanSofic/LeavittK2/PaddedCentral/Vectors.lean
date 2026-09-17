import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.GroupTheory.NoncommPiCoprod
import GroupApproximation.Meta.AxiomGuard

/-!
# Last-column and last-row vectors in `St_{n+1}(R)` (lane sk-leavitt-03, group side)

Carto `sk-leavitt` lane 03 (Khanh Lemma 5.6), over an arbitrary unital ring `R`.
The roots `x_{p,last}(a)` for `p : Fin n` pairwise commute, as do the roots `x_{last,p}(a)`.
So `MonoidHom.noncommPiCoprod` bundles them into homomorphisms out of `Fin n → Multiplicative R`:

* `padCol v = ∏_p x_{p,last}(v p)`, additive in `v`, with `padCol (e_p(a)) = x_{p,last}(a)`;
* `padRow v = ∏_p x_{last,p}(v p)`, additive in `v`, with `padRow (e_p(a)) = x_{last,p}(a)`;
* `padMat : St_n(R) →* M_n(R)`, the elementary matrix of a Steinberg element.

Lane 02 (`LeavittK2.RowColumn`, `colVec` / `rowVec`) was not complete on disk when this lane was
authored.  The vectors are therefore local to this namespace and use the distinct names
`padCol` / `padRow` to avoid clashes.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

variable {R : Type*} [Ring R] {n : ℕ}

/-- The root `x_{p,last}` as a homomorphism out of `Multiplicative R`. -/
def colHom (p : Fin n) : Multiplicative R →* St (n + 1) R where
  toFun a := x p.castSucc (Fin.last n) (Fin.castSucc_lt_last p).ne (Multiplicative.toAdd a)
  map_one' := by simp only [toAdd_one, x_zero]
  map_mul' a b := by simp only [toAdd_mul, x_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.colHom

/-- The root `x_{last,p}` as a homomorphism out of `Multiplicative R`. -/
def rowHom (p : Fin n) : Multiplicative R →* St (n + 1) R where
  toFun a := x (Fin.last n) p.castSucc (Fin.castSucc_lt_last p).ne' (Multiplicative.toAdd a)
  map_one' := by simp only [toAdd_one, x_zero]
  map_mul' a b := by simp only [toAdd_mul, x_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.rowHom

theorem colHom_commute :
    Pairwise fun p q : Fin n => ∀ a b, Commute (colHom (R := R) p a) (colHom q b) :=
  fun p q _ a b => x_commute_of_ne p.castSucc (Fin.last n) q.castSucc (Fin.last n)
    (Fin.castSucc_lt_last p).ne (Fin.castSucc_lt_last q).ne (Fin.castSucc_lt_last q).ne'
    (Fin.castSucc_lt_last p).ne' (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.colHom_commute

theorem rowHom_commute :
    Pairwise fun p q : Fin n => ∀ a b, Commute (rowHom (R := R) p a) (rowHom q b) :=
  fun p q _ a b => x_commute_of_ne (Fin.last n) p.castSucc (Fin.last n) q.castSucc
    (Fin.castSucc_lt_last p).ne' (Fin.castSucc_lt_last q).ne' (Fin.castSucc_lt_last p).ne
    (Fin.castSucc_lt_last q).ne (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.rowHom_commute

/-- All last-column roots at once. -/
noncomputable def colPi : (Fin n → Multiplicative R) →* St (n + 1) R :=
  MonoidHom.noncommPiCoprod colHom colHom_commute

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.colPi

/-- All last-row roots at once. -/
noncomputable def rowPi : (Fin n → Multiplicative R) →* St (n + 1) R :=
  MonoidHom.noncommPiCoprod rowHom rowHom_commute

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.rowPi

/-- The last-column vector `∏_p x_{p,last}(v p)`. -/
noncomputable def padCol (v : Fin n → R) : St (n + 1) R :=
  colPi (fun p => Multiplicative.ofAdd (v p))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padCol

/-- The last-row vector `∏_p x_{last,p}(v p)`. -/
noncomputable def padRow (v : Fin n → R) : St (n + 1) R :=
  rowPi (fun p => Multiplicative.ofAdd (v p))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padRow

theorem padCol_add (v w : Fin n → R) : padCol (v + w) = padCol v * padCol w :=
  map_mul colPi (fun p => Multiplicative.ofAdd (v p)) (fun p => Multiplicative.ofAdd (w p))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padCol_add

theorem padRow_add (v w : Fin n → R) : padRow (v + w) = padRow v * padRow w :=
  map_mul rowPi (fun p => Multiplicative.ofAdd (v p)) (fun p => Multiplicative.ofAdd (w p))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padRow_add

theorem padCol_zero : padCol (0 : Fin n → R) = 1 :=
  map_one colPi

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padCol_zero

theorem padRow_zero : padRow (0 : Fin n → R) = 1 :=
  map_one rowPi

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padRow_zero

theorem ofAdd_single (p : Fin n) (a : R) :
    (fun q => Multiplicative.ofAdd ((Pi.single p a : Fin n → R) q)) =
      (Pi.mulSingle p (Multiplicative.ofAdd a) : Fin n → Multiplicative R) := by
  funext q
  by_cases hq : q = p
  · rw [hq, Pi.single_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne hq, Pi.mulSingle_eq_of_ne hq, ofAdd_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ofAdd_single

theorem padCol_single (p : Fin n) (a : R) :
    padCol (Pi.single p a) = x p.castSucc (Fin.last n) (Fin.castSucc_lt_last p).ne a := by
  show colPi (fun q => Multiplicative.ofAdd ((Pi.single p a : Fin n → R) q)) = _
  rw [ofAdd_single p a]
  exact MonoidHom.noncommPiCoprod_mulSingle _ p (Multiplicative.ofAdd a)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padCol_single

theorem padRow_single (p : Fin n) (a : R) :
    padRow (Pi.single p a) = x (Fin.last n) p.castSucc (Fin.castSucc_lt_last p).ne' a := by
  show rowPi (fun q => Multiplicative.ofAdd ((Pi.single p a : Fin n → R) q)) = _
  rw [ofAdd_single p a]
  exact MonoidHom.noncommPiCoprod_mulSingle _ p (Multiplicative.ofAdd a)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padRow_single

/-- The elementary matrix of a Steinberg element. -/
def padMat : St n R →* Matrix (Fin n) (Fin n) R :=
  (Units.coeHom _).comp ((elementaryGroup (Fin n) R).subtype.comp projection)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padMat

theorem padMat_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    padMat (x i j hij b) = 1 + Matrix.single i j b := by
  have e : ((projection (x i j hij b) : elementaryGroup (Fin n) R) :
      (Matrix (Fin n) (Fin n) R)ˣ) = elementaryUnit i j hij b := by
    rw [projection_x, elementaryRoot_val]
  exact congrArg Units.val e

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padMat_x

/-- A `K₂` element has trivial elementary matrix. -/
theorem padMat_of_mem_K2 {k : St n R} (hk : k ∈ K2 (Fin n) R) : padMat k = 1 := by
  have e := congrArg (fun u : elementaryGroup (Fin n) R =>
    ((u : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)) ((mem_K2_iff k).mp hk)
  exact e

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.padMat_of_mem_K2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
