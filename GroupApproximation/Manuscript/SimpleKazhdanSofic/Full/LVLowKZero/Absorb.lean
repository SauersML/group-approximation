import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowK.KZero

/-!
# Modules absorbing the regular module

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2). Work order WO-LVLowK-1:
the algebraic `K₀` of `L = L_k(1,2)` vanishes.

Over a ring `R` with a binary Leavitt family, `[R] = 0` in `K₀(R)`
(`Full.LVLowK.AlgKZero.cls_regular_eq_zero`). So a module `M` with `M ⊕ R ≅ R` has class
`[M] = [M ⊕ R] - [R] = 0`. This file names that property and proves its closure properties:

* `AbsorbsRegular R M`: `M × R ≃ₗ[R] R` exists;
* invariance under isomorphism, stability under finite direct sums;
* the zero module, the regular module and every free module `Rⁿ` absorb `R`
  (the last two need a Leavitt family);
* `cls_eq_zero_of_absorbsRegular`: an absorbing f.g. projective module has class `0`.
-/

namespace GroupApproximation.Full.LVLowKZero

open GroupApproximation.Full.LVLowK

universe u v w

/-- A left `R`-module `M` **absorbs the regular module** when `M ⊕ R ≅ R` as left
`R`-modules (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def AbsorbsRegular (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nonempty ((M × R) ≃ₗ[R] R)

namespace AbsorbsRegular

variable {R : Type u} [Ring R]

/-- Absorption is invariant under isomorphism. -/
theorem of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : AbsorbsRegular R N) :
    AbsorbsRegular R M := by
  obtain ⟨f⟩ := h
  exact ⟨(e.prodCongr (LinearEquiv.refl R R)).trans f⟩

/-- If `M` and `N` absorb `R`, so does `M ⊕ N`: `(M ⊕ N) ⊕ R ≅ M ⊕ (N ⊕ R) ≅ M ⊕ R ≅ R`. -/
theorem prod {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : AbsorbsRegular R M) (hN : AbsorbsRegular R N) :
    AbsorbsRegular R (M × N) := by
  obtain ⟨f⟩ := hM
  obtain ⟨g⟩ := hN
  exact ⟨((LinearEquiv.prodAssoc R M N R).trans
    ((LinearEquiv.refl R M).prodCongr g)).trans f⟩

/-- A module with a single element absorbs `R`. -/
theorem of_unique {M : Type v} [AddCommGroup M] [Module R M] [Unique M] :
    AbsorbsRegular R M :=
  ⟨(LinearEquiv.prodComm R M R).trans
    (LinearEquiv.prodUnique (R := R) (M := R) (M₂ := M))⟩

/-- Over a ring with a binary Leavitt family, `R ⊕ R ≅ R`. -/
theorem regular (L : LeavittFamily R) : AbsorbsRegular R R :=
  ⟨L.linearEquivSquare.symm⟩

/-- Over a ring with a binary Leavitt family, every free module `Rⁿ` absorbs `R`. -/
theorem finFun (L : LeavittFamily R) (n : ℕ) : AbsorbsRegular R (Fin n → R) := by
  cases n with
  | zero => exact of_unique
  | succ m =>
    obtain ⟨e⟩ := L.nonempty_linearEquiv_finSucc m
    exact of_linearEquiv e.symm (regular L)

end AbsorbsRegular

/-- **An absorbing f.g. projective module has class zero.** Over a ring with a binary Leavitt
family, `P ⊕ R ≅ R` gives `[P] = [P ⊕ R] = [R] = 0` in `K₀(R)`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem cls_eq_zero_of_absorbsRegular {R : Type u} [Ring R] (L : LeavittFamily R)
    (P : FGProj R) (h : AbsorbsRegular R P.carrier) : AlgKZero.cls P = 0 := by
  obtain ⟨f⟩ := h
  calc AlgKZero.cls P = AlgKZero.cls (P.sum (FGProj.regular R)) :=
        (AlgKZero.cls_sum_regular L P).symm
    _ = AlgKZero.cls (FGProj.regular R) :=
        AlgKZero.cls_eq_cls (P := P.sum (FGProj.regular R)) (Q := FGProj.regular R) f
    _ = 0 := AlgKZero.cls_regular_eq_zero L

/-- **`K₀(R) = 0` as soon as every f.g. projective module absorbs `R`**, over a ring with a
binary Leavitt family (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem algKZero_eq_zero_of_forall_absorbsRegular {R : Type u} [Ring R] (L : LeavittFamily R)
    (h : ∀ P : FGProj R, AbsorbsRegular R P.carrier) (z : AlgKZero R) : z = 0 :=
  (AlgKZero.eq_zero_iff_forall_cls (R := R)).2
    (fun P => cls_eq_zero_of_absorbsRegular L P (h P)) z

end GroupApproximation.Full.LVLowKZero
