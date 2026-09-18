import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarIndMat
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateSt
import GroupApproximation.Meta.AxiomGuard

/-!
# Two conjugates of root elements with trivial matrix die after one stabilization

Lane `bh-met-93e`, pair module.  Let `R` be a ring with no zero divisors and `1 ≠ 0`.  Write
`G = padMat g`, `H = padMat g⁻¹`, `V = G *ᵥ e_i(b)` and `W = e_j(1) ᵥ* H`.

* `k2KarInd_stab_conj_x`: `stab (g x_ij(b) g⁻¹) = ⁅padCol V, padRow W⁆` in `St(n + 1, R)`.
  This is `x_ij(b) = ⁅x_{i,n}(b), x_{n,j}(1)⁆` conjugated by `stab g`, using the column and
  row conjugation formulas of `PaddedCentral`.
* `k2KarInd_stab_pair`: if `padMat (g x_ij(b) g⁻¹ x_kl(c)) = 1`, then
  `stab (g x_ij(b) g⁻¹ x_kl(c)) = 1`.  Indeed `V_p W_q = e_kl(-c)_pq`, and `W ≠ 0`, so by
  `k2KarInd_vec_dichotomy` either `V = 0, c = 0`, or `V = v e_k`, `W = w e_l`, `v w = -c`; then
  `⁅padCol V, padRow W⁆ = x_kl(v w) = x_kl(-c)`.
* `k2KarInd_stDies_of_stab`: `stab y = 1` gives `cubeDiagDilate_StDies y`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarIndPair

variable {R : Type*} [Ring R] {n : ℕ}

/-- `stab (g x_ij(b) g⁻¹) = ⁅padCol (G *ᵥ e_i(b)), padRow (e_j(1) ᵥ* H)⁆`. -/
theorem k2KarInd_stab_conj_x (g : St n R) (i j : Fin n) (hij : i ≠ j) (b : R) :
    stab n R (g * x i j hij b * g⁻¹) =
      ⁅padCol (padMat g *ᵥ Pi.single i b), padRow (Pi.single j (1 : R) ᵥ* padMat g⁻¹)⁆ := by
  have hx : stab n R (x i j hij b) =
      ⁅padCol (Pi.single i b), padRow (Pi.single j (1 : R))⁆ := by
    rw [stab_x, padCol_single, padRow_single,
      x_commutator i.castSucc (Fin.last n) j.castSucc (Fin.castSucc_lt_last i).ne
        (Fin.castSucc_lt_last j).ne' (fun h ↦ hij (Fin.castSucc_inj.mp h)), mul_one]
  have hcol := stab_conj_padCol g (Pi.single i b)
  have hrow := stab_conj_padRow g⁻¹ (Pi.single j (1 : R))
  rw [map_inv (stab n R) g, inv_inv] at hrow
  rw [map_mul (stab n R) (g * x i j hij b) g⁻¹, map_mul (stab n R) g (x i j hij b),
    map_inv (stab n R) g, hx, conjugate_commutatorElement, hcol, hrow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_stab_conj_x

/-- The entries of `g x_ij(b) g⁻¹` when `padMat (g x_ij(b) g⁻¹ x_kl(c)) = 1`. -/
theorem k2KarInd_pair_entries (g : St n R) (i j : Fin n) (hij : i ≠ j) (b : R) (k l : Fin n)
    (hkl : k ≠ l) (c : R) (h : padMat (g * x i j hij b * g⁻¹ * x k l hkl c) = 1) (p q : Fin n) :
    (padMat g *ᵥ Pi.single i b) p * (Pi.single j (1 : R) ᵥ* padMat g⁻¹) q =
      Matrix.single k l (-c) p q := by
  have hconj : g * x i j hij b * g⁻¹ =
      g * x i j hij b * g⁻¹ * x k l hkl c * x k l hkl (-c) := by
    rw [mul_assoc _ (x k l hkl c), x_mul, add_neg_cancel, x_zero, mul_one]
  have e := k2KarInd_padMat_conj_apply g i j hij b p q
  rw [hconj, map_mul padMat _ (x k l hkl (-c)), h, one_mul, padMat_x, Matrix.add_apply,
    add_right_inj] at e
  rw [k2KarInd_mulVec_single_apply, single_vecMul_apply, one_mul]
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_pair_entries

/-- **Pair lemma.**  Over a ring without zero divisors, a product `g x_ij(b) g⁻¹ · x_kl(c)` with
trivial elementary matrix dies after one stabilization. -/
theorem k2KarInd_stab_pair (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) (h10 : (1 : R) ≠ 0)
    (g : St n R) (i j : Fin n) (hij : i ≠ j) (b : R) (k l : Fin n) (hkl : k ≠ l) (c : R)
    (h : padMat (g * x i j hij b * g⁻¹ * x k l hkl c) = 1) :
    stab n R (g * x i j hij b * g⁻¹ * x k l hkl c) = 1 := by
  rw [map_mul (stab n R) (g * x i j hij b * g⁻¹), k2KarInd_stab_conj_x, stab_x]
  rcases k2KarInd_vec_dichotomy (V := padMat g *ᵥ Pi.single i b)
      (W := Pi.single j (1 : R) ᵥ* padMat g⁻¹) hR (k2KarInd_row_ne_zero h10 g j)
      (k2KarInd_pair_entries g i j hij b k l hkl c h) with ⟨hV, hc⟩ | ⟨hV, hW, hvw⟩
  · rw [hV, padCol_zero, commutatorElement_one_left, one_mul, hc, x_zero]
  · rw [hV, hW, padCol_single, padRow_single,
      x_commutator k.castSucc (Fin.last n) l.castSucc (Fin.castSucc_lt_last k).ne
        (Fin.castSucc_lt_last l).ne' (fun h ↦ hkl (Fin.castSucc_inj.mp h)), x_mul, hvw, x_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_stab_pair

/-- One stabilization killing `y` means `y` dies after padding. -/
theorem k2KarInd_stDies_of_stab {y : St n R} (h : stab n R y = 1) : cubeDiagDilate_StDies y := by
  refine ⟨n + 1, Nat.le_add_right n 1, ?_⟩
  have hemb : (Fin.castLEEmb (Nat.le_add_right n 1) : Fin n ↪ Fin (n + 1)) = Fin.castSuccEmb :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  rw [hemb]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_stDies_of_stab

end KarIndPair

end GroupApproximation.BooneHigman.Metabelian.ElemFP
