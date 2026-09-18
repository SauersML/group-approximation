import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionVanishExt
import Mathlib.Algebra.DirectSum.Basic

/-!
# `lim¹` of a tower of `Hom(-, D)` vanishes for divisible `D`

Lane `TWWSch3d3c`, work order `WO-TWWSchafhauser-3d3-3` (Rosenberg–Schochet injectivity half).
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.

The Rosenberg–Schochet comparison of `Ext(C(X), J)` with the cohomology of a compact metrizable
space `X = lim Xₖ` uses a Milnor `lim¹` sequence (J. Rosenberg, C. Schochet, Duke Math. J. 55
(1987), Prop. 1.8 and Thm. 1.17; C. Schochet, Pacific J. Math. 114 (1984); J. Milnor, Pacific
J. Math. 12 (1962)). The `lim¹` term is the cokernel of `1 - shift` on `∏ₖ Hom(Gₖ, D)` for a
direct system `Gₖ → Gₖ₊₁`. When `D` is divisible this cokernel is zero, which is the algebraic
input used here.

Proof: `1 - shift : ⊕ₖ Gₖ → ⊕ₖ Gₖ` is injective (compare components by induction on `k`), and a
divisible group is injective (`IsDivisibleGroup.exists_extension`). Extending `⊕ₖ hₖ` along
`1 - shift` gives the solution.

* `LimOne.shift`, `LimOne.shift_of`, `LimOne.shift_apply_zero`, `LimOne.shift_apply_succ`;
* `LimOne.sub_shift_injective`: `1 - shift` is injective;
* `IsDivisibleGroup.exists_telescope_solution`: every `(hₖ) ∈ ∏ Hom(Gₖ, D)` is of the form
  `fₖ - fₖ₊₁ ∘ gₖ`, i.e. `lim¹ Hom(Gₖ, D) = 0`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u v

namespace LimOne

variable {G : ℕ → Type v} [∀ k, AddCommGroup (G k)] (g : ∀ k, G k →+ G (k + 1))

/-- The **shift** of a direct system on `⊕ₖ Gₖ`: `y ∈ Gₖ` goes to `gₖ y ∈ Gₖ₊₁`. -/
def shift : DirectSum ℕ G →+ DirectSum ℕ G :=
  DirectSum.toAddMonoid fun k => (DirectSum.of G (k + 1)).comp (g k)

theorem shift_of (k : ℕ) (y : G k) :
    shift g (DirectSum.of G k y) = DirectSum.of G (k + 1) (g k y) :=
  DirectSum.toAddMonoid_of (fun k => (DirectSum.of G (k + 1)).comp (g k)) k y

/-- Nothing is shifted into degree `0`. -/
theorem shift_apply_zero (x : DirectSum ℕ G) : shift g x 0 = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact congrArg (fun z : DirectSum ℕ G => z 0) (map_zero (shift g))
  | of k y =>
    rw [shift_of]
    exact DirectSum.of_eq_of_ne (k + 1) 0 (g k y) (Nat.succ_ne_zero k).symm
  | add x y hx hy =>
    rw [map_add (shift g) x y, DirectSum.add_apply, hx, hy, add_zero]

/-- The degree-`k+1` component of the shift is `gₖ` of the degree-`k` component. -/
theorem shift_apply_succ (x : DirectSum ℕ G) (k : ℕ) : shift g x (k + 1) = g k (x k) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero]
    exact (map_zero (g k)).symm
  | of j y =>
    rw [shift_of]
    by_cases hjk : j = k
    · subst hjk
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · have h1 : k + 1 ≠ j + 1 := fun h => hjk (Nat.add_right_cancel h).symm
      have h2 : k ≠ j := fun h => hjk h.symm
      rw [DirectSum.of_eq_of_ne (j + 1) (k + 1) (g j y) h1, DirectSum.of_eq_of_ne j k y h2,
        map_zero]
  | add x y hx hy =>
    rw [map_add (shift g) x y, DirectSum.add_apply, DirectSum.add_apply, hx, hy,
      map_add (g k) (x k) (y k)]

/-- **`1 - shift` is injective** on `⊕ₖ Gₖ`. -/
theorem sub_shift_injective :
    Function.Injective (AddMonoidHom.id (DirectSum ℕ G) - shift g) := by
  refine (injective_iff_map_eq_zero (AddMonoidHom.id (DirectSum ℕ G) - shift g)).mpr ?_
  intro x hx
  have h1 : x - shift g x = 0 := hx
  have h2 : x = shift g x := sub_eq_zero.mp h1
  have key : ∀ k, x k = 0 := by
    intro k
    induction k with
    | zero =>
      rw [h2]
      exact shift_apply_zero g x
    | succ k ih =>
      rw [h2, shift_apply_succ g x k, ih]
      exact map_zero (g k)
  exact DirectSum.ext fun k => key k

end LimOne

/-- **`lim¹ Hom(Gₖ, D) = 0` for divisible `D`**: for a direct system `gₖ : Gₖ → Gₖ₊₁` and any
family `hₖ : Gₖ → D` there are `fₖ : Gₖ → D` with `fₖ - fₖ₊₁ ∘ gₖ = hₖ`. This is the vanishing
of the Milnor `lim¹` term (Rosenberg–Schochet, Duke Math. J. 55 (1987), Prop. 1.8). -/
theorem IsDivisibleGroup.exists_telescope_solution {D : Type u} [AddCommGroup D]
    (hD : IsDivisibleGroup D) {G : ℕ → Type v} [∀ k, AddCommGroup (G k)]
    (g : ∀ k, G k →+ G (k + 1)) (h : ∀ k, G k →+ D) :
    ∃ f : ∀ k, G k →+ D, ∀ k, f k - (f (k + 1)).comp (g k) = h k := by
  obtain ⟨F, hF⟩ := hD.exists_extension (AddMonoidHom.id (DirectSum ℕ G) - LimOne.shift g)
    (LimOne.sub_shift_injective g) (DirectSum.toAddMonoid h)
  refine ⟨fun k => F.comp (DirectSum.of G k), fun k => AddMonoidHom.ext fun y => ?_⟩
  have hy : F (DirectSum.of G k y - LimOne.shift g (DirectSum.of G k y)) =
      DirectSum.toAddMonoid h (DirectSum.of G k y) :=
    DFunLike.congr_fun hF (DirectSum.of G k y)
  rw [LimOne.shift_of, map_sub, DirectSum.toAddMonoid_of] at hy
  exact hy

end GroupApproximation.Full.TWWSchafhauser
