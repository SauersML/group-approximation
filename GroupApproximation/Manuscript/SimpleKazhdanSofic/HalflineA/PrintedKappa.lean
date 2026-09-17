import GroupApproximation.GroupTheory.ShiftTransversalBijection
import GroupApproximation.GroupTheory.LevelShiftDelta
import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline`: `ψ`, `θ`, the printed bijection `κ`, and `ζ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline`:

* tex l.625–630, sentence ef4082fc740e:
  > Let ψ map the ball of radius 2λ of Γ injectively into a finite group Q, preserving the products that stay in it, and
  > let θ be the isomorphism from {v ∈ Q^{[−3λ,3λ]} : v_{3λ−1} = v_{3λ}} onto {v ∈ Q^{[−3λ,3λ]} : v_{−3λ} = 1} given by
  > θ(v)_{−3λ} = 1 and θ(v)_m = v_{m−1} for m > −3λ.
* tex l.630–635, sentence 419672af4c27:
  > The bijection κ of Q^{[−3λ,3λ]} given by κ(x)_{−3λ} = x_{3λ−1}^{−1} x_{3λ} and κ(x)_m = x_{m−1} for m > −3λ
  > satisfies κ(vx) = θ(v)κ(x) for v in the domain of θ, as v_{3λ−1} = v_{3λ} cancels in the coordinate −3λ.
* tex l.635–639, sentence 5043611f4d0d:
  > Let each v ∈ Q^{[−3λ,3λ]} act on Q^{[−3λ,3λ]} × ℤ/5λ by left multiplication on the first coordinate, and put
  > ζ(x,i) = (κ(x), i+1), so that ζvζ⁻¹ = θ(v) on the domain of θ.

## Conventions

The radius is `λ = s + 1` (so `λ ≥ 1` is built in). The window `Q^{[−3λ,3λ]}` is `Fin (6s + 5 + 2) → Q`, position `k`
standing for the level `k − 3λ`: position `0` is the level `−3λ`, and the positions `castSucc (last (6s+5))` and
`last (6s+6)` are the levels `3λ − 1` and `3λ`. For a general window `Fin (M + 2)` the lemmas hold for every `M`.

## Proof route

* `ψ`: the textbook form of LEF (`isLEF_iff_textbook`) applied to the finite ball `wordBall E (2λ)` (`wordBall_finite`).
* `θ` is `ShiftTransversalBijection.theta`, a homomorphism, injective on `dom` and onto `ran` (`theta_injOn`,
  `theta_surjOn`). `thetaEquiv` is the resulting isomorphism `dom ≃* ran`.
* `printedKappaFun` is the printed formula for `κ`. Its inverse `printedKappaInv` puts back `x_{3λ} = y_{3λ} y_{−3λ}`
  (as `κ(x)_{3λ} = x_{3λ−1}`). `printedKappa_mul_left` is `κ(vx) = θ(v)κ(x)`: in the coordinate `−3λ`,
  `(v_{3λ−1} x_{3λ−1})⁻¹ v_{3λ} x_{3λ} = x_{3λ−1}⁻¹ x_{3λ}` as `v_{3λ−1} = v_{3λ}`.
* `printedZeta = κ × (i ↦ i + 1)`, and `printedZeta_mul_lmul_mul_printedZeta_inv` is `ζ v ζ⁻¹ = θ(v)`, evaluated
  pointwise.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HalflineA

universe v

open Equiv ShiftTransversalBijection LevelShiftDelta

section Theta

variable (Q : Type*) [Group Q] (M : ℕ)

/-- **`θ` as an isomorphism** of `{v : v_{3λ−1} = v_{3λ}}` onto `{v : v_{−3λ} = 1}` (tex l.627–630). -/
noncomputable def thetaEquiv : dom Q M ≃* ran Q M :=
  MulEquiv.ofBijective (((theta Q M).comp (dom Q M).subtype).codRestrict (ran Q M) fun v => theta_mem_ran Q M v)
    ⟨fun v w h => Subtype.ext (theta_injOn Q M v.2 w.2 (congrArg Subtype.val h)),
      fun u => by
        obtain ⟨v, hv, hvu⟩ := theta_surjOn Q M u.2
        exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩⟩

theorem thetaEquiv_apply (v : dom Q M) : (thetaEquiv Q M v : Fin (M + 2) → Q) = theta Q M v :=
  rfl

end Theta

section Kappa

variable (Q : Type*) [Group Q] (M : ℕ)

/-- **The printed `κ`**: `κ(x)_{−3λ} = x_{3λ−1}⁻¹ x_{3λ}` and `κ(x)_m = x_{m−1}` for `m > −3λ` (tex l.631–632). -/
def printedKappaFun (x : Fin (M + 2) → Q) : Fin (M + 2) → Q :=
  Fin.cons ((x (Fin.castSucc (Fin.last M)))⁻¹ * x (Fin.last (M + 1))) fun k : Fin (M + 1) => x (Fin.castSucc k)

theorem printedKappaFun_zero (x : Fin (M + 2) → Q) :
    printedKappaFun Q M x 0 = (x (Fin.castSucc (Fin.last M)))⁻¹ * x (Fin.last (M + 1)) := by
  show Fin.cons (α := fun _ : Fin (M + 2) => Q) ((x (Fin.castSucc (Fin.last M)))⁻¹ * x (Fin.last (M + 1)))
    (fun k : Fin (M + 1) => x (Fin.castSucc k)) 0 = (x (Fin.castSucc (Fin.last M)))⁻¹ * x (Fin.last (M + 1))
  exact Fin.cons_zero _ _

theorem printedKappaFun_succ (x : Fin (M + 2) → Q) (k : Fin (M + 1)) :
    printedKappaFun Q M x k.succ = x (Fin.castSucc k) := by
  show Fin.cons (α := fun _ : Fin (M + 2) => Q) ((x (Fin.castSucc (Fin.last M)))⁻¹ * x (Fin.last (M + 1)))
    (fun k : Fin (M + 1) => x (Fin.castSucc k)) k.succ = x (Fin.castSucc k)
  exact Fin.cons_succ _ _ _

theorem printedKappaFun_last (x : Fin (M + 2) → Q) :
    printedKappaFun Q M x (Fin.last (M + 1)) = x (Fin.castSucc (Fin.last M)) :=
  printedKappaFun_succ Q M x (Fin.last M)

/-- The inverse of `κ`: `x_m = y_{m+1}` for `m < 3λ` and `x_{3λ} = y_{3λ} y_{−3λ}`. -/
def printedKappaInv (y : Fin (M + 2) → Q) : Fin (M + 2) → Q :=
  Fin.lastCases (motive := fun _ => Q) (y (Fin.last (M + 1)) * y 0) fun k : Fin (M + 1) => y k.succ

theorem printedKappaInv_last (y : Fin (M + 2) → Q) :
    printedKappaInv Q M y (Fin.last (M + 1)) = y (Fin.last (M + 1)) * y 0 := by
  show Fin.lastCases (motive := fun _ : Fin (M + 2) => Q) (y (Fin.last (M + 1)) * y 0)
    (fun k : Fin (M + 1) => y k.succ) (Fin.last (M + 1)) = y (Fin.last (M + 1)) * y 0
  exact Fin.lastCases_last

theorem printedKappaInv_castSucc (y : Fin (M + 2) → Q) (k : Fin (M + 1)) :
    printedKappaInv Q M y (Fin.castSucc k) = y k.succ := by
  show Fin.lastCases (motive := fun _ : Fin (M + 2) => Q) (y (Fin.last (M + 1)) * y 0)
    (fun k : Fin (M + 1) => y k.succ) (Fin.castSucc k) = y k.succ
  exact Fin.lastCases_castSucc k

theorem printedKappaInv_printedKappaFun (x : Fin (M + 2) → Q) :
    printedKappaInv Q M (printedKappaFun Q M x) = x := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [printedKappaInv_last, printedKappaFun_last, printedKappaFun_zero]
    exact mul_inv_cancel_left _ _
  | cast k =>
    rw [printedKappaInv_castSucc]
    exact printedKappaFun_succ Q M x k

theorem printedKappaFun_printedKappaInv (y : Fin (M + 2) → Q) :
    printedKappaFun Q M (printedKappaInv Q M y) = y := by
  funext i
  induction i using Fin.cases with
  | zero =>
    rw [printedKappaFun_zero, printedKappaInv_castSucc, printedKappaInv_last]
    exact inv_mul_cancel_left (y (Fin.last (M + 1))) (y 0)
  | succ k =>
    rw [printedKappaFun_succ]
    exact printedKappaInv_castSucc Q M y k

/-- **The bijection `κ`** of `Q^{[−3λ,3λ]}` (tex l.630–632). -/
def printedKappa : Perm (Fin (M + 2) → Q) where
  toFun := printedKappaFun Q M
  invFun := printedKappaInv Q M
  left_inv := printedKappaInv_printedKappaFun Q M
  right_inv := printedKappaFun_printedKappaInv Q M

theorem printedKappa_apply (x : Fin (M + 2) → Q) : printedKappa Q M x = printedKappaFun Q M x :=
  rfl

theorem printedKappaFun_mul_left {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) (x : Fin (M + 2) → Q) :
    printedKappaFun Q M (v * x) = theta Q M v * printedKappaFun Q M x := by
  have hv' : v (Fin.castSucc (Fin.last M)) = v (Fin.last (M + 1)) := hv
  funext i
  induction i using Fin.cases with
  | zero =>
    rw [Pi.mul_apply, printedKappaFun_zero, printedKappaFun_zero, theta_zero, one_mul, Pi.mul_apply, Pi.mul_apply,
      hv', mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  | succ k =>
    rw [Pi.mul_apply, printedKappaFun_succ, printedKappaFun_succ, theta_succ, Pi.mul_apply]

/-- **`κ(vx) = θ(v)κ(x)` for `v` in the domain of `θ`** (tex l.632–635). -/
theorem printedKappa_mul_left {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) (x : Fin (M + 2) → Q) :
    printedKappa Q M (v * x) = theta Q M v * printedKappa Q M x :=
  printedKappaFun_mul_left Q M hv x

end Kappa

section Zeta

variable (Q : Type*) [Group Q] (M L : ℕ)

/-- **`ζ(x, i) = (κ(x), i + 1)`** on `Q^{[−3λ,3λ]} × ℤ/L` (tex l.637–638), for the printed `κ`. -/
def printedZeta : Perm ((Fin (M + 2) → Q) × ZMod L) :=
  Equiv.prodCongr (printedKappa Q M) (Equiv.addRight 1)

theorem printedZeta_apply (z : (Fin (M + 2) → Q) × ZMod L) :
    printedZeta Q M L z = (printedKappa Q M z.1, z.2 + 1) :=
  rfl

/-- **`ζ v ζ⁻¹ = θ(v)` on the domain of `θ`** (tex l.638–639). -/
theorem printedZeta_mul_lmul_mul_printedZeta_inv {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) :
    printedZeta Q M L * lmul Q M L v * (printedZeta Q M L)⁻¹ = lmul Q M L (theta Q M v) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun z => Prod.ext ?_ rfl
  simp only [Perm.mul_apply, printedZeta_apply, lmul_apply, printedKappa_mul_left Q M hv]

theorem printedZeta_inv_mul_lmul_theta_mul_printedZeta {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) :
    (printedZeta Q M L)⁻¹ * lmul Q M L (theta Q M v) * printedZeta Q M L = lmul Q M L v := by
  rw [← printedZeta_mul_lmul_mul_printedZeta_inv Q M L hv]
  group

end Zeta

/-- **`ψ` and `θ`** (tex l.625–630). Let `Γ` be LEF, `E` a finite set and `λ = s + 1`. There is a map `ψ` of `Γ` into a
finite group `Q`, injective on the ball of radius `2λ` in `E` and preserving the products that stay in it. For every
group `Q`, `θ` is an isomorphism from `{v ∈ Q^{[−3λ,3λ]} : v_{3λ−1} = v_{3λ}}` onto `{v : v_{−3λ} = 1}`, with
`θ(v)_{−3λ} = 1` and `θ(v)_m = v_{m−1}` for `m > −3λ`. -/
theorem manuscriptSentence_halflinePsiTheta {Γ : Type*} [Group Γ] (hLEF : IsLEF Γ) (E : Finset Γ) (s : ℕ) :
    (∃ (Q : Type) (_ : Group Q) (_ : Fintype Q) (ψ : Γ → Q),
      Set.InjOn ψ (wordBall (E : Set Γ) (2 * (s + 1))) ∧
      ∀ a ∈ wordBall (E : Set Γ) (2 * (s + 1)), ∀ b ∈ wordBall (E : Set Γ) (2 * (s + 1)),
        a * b ∈ wordBall (E : Set Γ) (2 * (s + 1)) → ψ (a * b) = ψ a * ψ b) ∧
    ∀ (Q : Type v) [Group Q],
      (∀ w : Fin (6 * s + 5 + 2) → Q,
        w ∈ dom Q (6 * s + 5) ↔ w (Fin.castSucc (Fin.last (6 * s + 5))) = w (Fin.last (6 * s + 5 + 1))) ∧
      (∀ w : Fin (6 * s + 5 + 2) → Q, w ∈ ran Q (6 * s + 5) ↔ w 0 = 1) ∧
      ∃ θ : dom Q (6 * s + 5) ≃* ran Q (6 * s + 5),
        (∀ w : dom Q (6 * s + 5), (θ w : Fin (6 * s + 5 + 2) → Q) 0 = 1) ∧
        ∀ (w : dom Q (6 * s + 5)) (k : Fin (6 * s + 5 + 1)),
          (θ w : Fin (6 * s + 5 + 2) → Q) k.succ = (w : Fin (6 * s + 5 + 2) → Q) (Fin.castSucc k) := by
  have hfin : (wordBall (E : Set Γ) (2 * (s + 1))).Finite := wordBall_finite E.finite_toSet _
  obtain ⟨H, ψ, hψinj, hψmul⟩ := (isLEF_iff_textbook Γ).1 hLEF hfin.toFinset
  refine ⟨⟨(H : Type), inferInstance, inferInstance, ψ, ?_, ?_⟩, ?_⟩
  · rw [Set.Finite.coe_toFinset] at hψinj
    exact hψinj
  · exact fun a ha b hb hab =>
      hψmul a (hfin.mem_toFinset.2 ha) b (hfin.mem_toFinset.2 hb) (hfin.mem_toFinset.2 hab)
  · intro Q _
    refine ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, thetaEquiv Q (6 * s + 5), fun w => ?_, fun w k => ?_⟩
    · rw [thetaEquiv_apply]
      exact theta_zero Q (6 * s + 5) w
    · rw [thetaEquiv_apply]
      exact theta_succ Q (6 * s + 5) w k

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflinePsiTheta

/-- **The printed bijection `κ`** (tex l.630–635), at `λ = s + 1`: `κ` is a bijection of `Q^{[−3λ,3λ]}` with
`κ(x)_{−3λ} = x_{3λ−1}⁻¹ x_{3λ}` and `κ(x)_m = x_{m−1}` for `m > −3λ`, and `κ(vx) = θ(v)κ(x)` for `v` in the domain of
`θ`. -/
theorem manuscriptSentence_halflinePrintedKappa (Q : Type*) [Group Q] (s : ℕ) :
    ∃ κ : Perm (Fin (6 * s + 5 + 2) → Q),
      (∀ x : Fin (6 * s + 5 + 2) → Q,
        κ x 0 = (x (Fin.castSucc (Fin.last (6 * s + 5))))⁻¹ * x (Fin.last (6 * s + 5 + 1))) ∧
      (∀ (x : Fin (6 * s + 5 + 2) → Q) (k : Fin (6 * s + 5 + 1)), κ x k.succ = x (Fin.castSucc k)) ∧
      ∀ v ∈ dom Q (6 * s + 5), ∀ x, κ (v * x) = theta Q (6 * s + 5) v * κ x :=
  ⟨printedKappa Q (6 * s + 5), printedKappaFun_zero Q (6 * s + 5), printedKappaFun_succ Q (6 * s + 5),
    fun _ hv x => printedKappa_mul_left Q (6 * s + 5) hv x⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflinePrintedKappa

/-- **`ζ`** (tex l.635–639), at `λ = s + 1`: each `v ∈ Q^{[−3λ,3λ]}` acts on `Q^{[−3λ,3λ]} × ℤ/5λ` by left
multiplication on the first coordinate (a homomorphism `lmul`), `ζ(x, i) = (κ(x), i + 1)` for the printed `κ`, and
`ζ v ζ⁻¹ = θ(v)` for `v` in the domain of `θ`. -/
theorem manuscriptSentence_halflinePrintedZeta (Q : Type*) [Group Q] (s : ℕ) :
    (∀ (w : Fin (6 * s + 5 + 2) → Q) (z : (Fin (6 * s + 5 + 2) → Q) × ZMod (5 * (s + 1))),
      lmul Q (6 * s + 5) (5 * (s + 1)) w z = (w * z.1, z.2)) ∧
    (∀ z : (Fin (6 * s + 5 + 2) → Q) × ZMod (5 * (s + 1)),
      printedZeta Q (6 * s + 5) (5 * (s + 1)) z = (printedKappa Q (6 * s + 5) z.1, z.2 + 1)) ∧
    ∀ w ∈ dom Q (6 * s + 5),
      printedZeta Q (6 * s + 5) (5 * (s + 1)) * lmul Q (6 * s + 5) (5 * (s + 1)) w *
          (printedZeta Q (6 * s + 5) (5 * (s + 1)))⁻¹ =
        lmul Q (6 * s + 5) (5 * (s + 1)) (theta Q (6 * s + 5) w) :=
  ⟨lmul_apply Q (6 * s + 5) (5 * (s + 1)), printedZeta_apply Q (6 * s + 5) (5 * (s + 1)),
    fun _ hw => printedZeta_mul_lmul_mul_printedZeta_inv Q (6 * s + 5) (5 * (s + 1)) hw⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflinePrintedZeta

end HalflineA
end SimpleKazhdanSofic
end GroupApproximation
