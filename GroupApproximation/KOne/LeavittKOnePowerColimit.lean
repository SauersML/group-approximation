import GroupApproximation.KOne.LeavittKOneDegreeZeroDeterminant
import Mathlib.Algebra.Colimit.DirectLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# The colimit of `k^×` along `d`-th powers, and its `(d-1)`-st power quotient

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex line 1249):

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

Every proof of the second isomorphism goes through the degree-zero part

    `L₀ = ⋃ₙ M_{dⁿ}(k)`,

whose `K₁` is the colimit of the groups `K₁(M_{dⁿ}(k)) = k^×` along the maps
induced by the stage inclusions `A ↦ A ⊗ 1_d`.
`KOne/LeavittKOneDegreeZeroDeterminant.lean` identifies those maps:
`det (A ⊗ 1_d) = (det A)^d`, so the transition is `x ↦ x^d`.

This module builds that colimit for an arbitrary abelian group and computes the
quotient the printed answer needs:

    `G / G^{d-1} ≅ PowColim(G,d) / PowColim(G,d)^{d-1}`   (`ofStageQuotientEquiv`)

At `G = k^×` the left side is the printed `k^×/(k^×)^{d-1}`.

## Where this sits in the Ara--Brustenga--Cortiñas computation

`L = L₀[t₊, t₋; φ]` is a corner skew Laurent polynomial ring, and the `K₁` half
of its fundamental theorem reads `K₁(L) ≅ coker(1 - φ_*)` on `K₁(L₀)`.  Under
`K₁(L₀) = PowColim(k^×, d)` the corner endomorphism `φ_*` is the inverse of the
`d`-th power map, which `powBijective` shows is an automorphism; so `1 - φ_*`
has image the `(d-1)`-st powers, and its cokernel is the quotient computed here.

**That cokernel identification is the elementary half of the computation, and it
is what this module closes.**  Two things it does not do: identify `K₁(L₀)` with
this colimit, which needs `K₁` of a filtered colimit of rings together with
`K₁(M_n(k)) ≅ k^×`; and the fundamental theorem itself, which is the
Bass--Heller--Swan step.  See `$S/cc/backup/o-leavitt-k1/RESIDUAL.md`.

## Nothing here is about rings

`PowColim` is built from an arbitrary abelian group and an arbitrary `d`; the
Leavitt algebra enters only through the reader's choice of `G = k^×`.
-/

namespace GroupApproximation
namespace PowerColimit

open LeavittScalarQuotient

/-! ### `x^{(m+1)^j} = x` in `H/H^m` -/

/-- Raising to the `(m+1)`-st power is the identity on `H/H^m`, hence so is
raising to any power of `m+1`. -/
theorem mk_pow_pow_eq_mk {H : Type*} [CommGroup H] (m : ℕ) (a : H) (j : ℕ) :
    (QuotientGroup.mk' ((powMonoidHom m : H →* H).range)) (a ^ ((m + 1) ^ j))
      = (QuotientGroup.mk' ((powMonoidHom m : H →* H).range)) a := by
  induction j with
  | zero => rw [pow_zero, pow_one]
  | succ j ih =>
      have hstep : a ^ ((m + 1) ^ (j + 1)) = (a ^ ((m + 1) ^ j)) ^ (m + 1) := by
        rw [← pow_mul, pow_succ]
      rw [hstep, map_pow, ih, ← map_pow]
      exact mk_pow_succ_eq_mk m a

variable (G : Type*) [CommGroup G] (d : ℕ)

/-! ### The direct system `G --(·)^d--> G --(·)^d--> ⋯` -/

/-- The transition from stage `n` to stage `m`: raise to the `d^(m-n)`. -/
def step (n m : ℕ) (_h : n ≤ m) : G →* G := powMonoidHom (d ^ (m - n))

instance powDirectedSystem :
    DirectedSystem (fun _ : ℕ => G) (fun i j h => ⇑(step G d i j h)) where
  map_self := fun i x => by
    show x ^ (d ^ (i - i)) = x
    rw [Nat.sub_self, pow_zero, pow_one]
  map_map := fun {i j k} hij hjk x => by
    -- Mathlib's `map_map` runs the composite `k → j → i`, so the transitions
    -- here are `step k j` then `step j i`.
    have hexp : (j - k) + (i - j) = i - k := by omega
    show (x ^ (d ^ (j - k))) ^ (d ^ (i - j)) = x ^ (d ^ (i - k))
    rw [← pow_mul, ← pow_add, hexp]

/-- **`PowColim G d`**: the colimit of `G --(·)^d--> G --(·)^d--> ⋯`.  At
`G = k^×` this is what the degree-zero determinant computes `K₁(⋃ₙ M_{dⁿ}(k))`
to be. -/
noncomputable abbrev PowColim : Type _ :=
  DirectLimit (fun _ : ℕ => G) (step G d)

/-- The canonical map from the `n`-th stage. -/
noncomputable def ofStage (n : ℕ) : G →* PowColim G d where
  toFun x := ⟦⟨n, x⟩⟧
  map_one' := (DirectLimit.one_def (f := step G d) n).symm
  map_mul' x y := (DirectLimit.mul_def (f := step G d) n x y).symm

@[simp] theorem ofStage_apply (n : ℕ) (x : G) :
    ofStage G d n x = ⟦⟨n, x⟩⟧ := rfl

/-- Moving up a stage: the `d^(m-n)`-th power at stage `m` names the same class
as the element at stage `n`. -/
theorem ofStage_step {n m : ℕ} (h : n ≤ m) (x : G) :
    ofStage G d m (x ^ (d ^ (m - n))) = ofStage G d n x := by
  have hmk := DirectLimit.mk_apply (f := step G d) n m x h
  exact hmk

/-- Every element of the colimit comes from some stage. -/
theorem ofStage_surjective (z : PowColim G d) :
    ∃ (n : ℕ) (x : G), ofStage G d n x = z := by
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk (f := step G d) z
  exact ⟨n, x, hx.symm⟩

/-- Two stage elements agree in the colimit only if they agree after enough
`d`-th powers. -/
theorem eq_of_ofStage_eq {n m : ℕ} {x y : G}
    (h : ofStage G d n x = ofStage G d m y) :
    ∃ (i : ℕ), n ≤ i ∧ m ≤ i ∧ x ^ (d ^ (i - n)) = y ^ (d ^ (i - m)) := by
  obtain ⟨i, hn, hm, heq⟩ := Quotient.exact h
  exact ⟨i, hn, hm, heq⟩

/-! ### The `d`-th power map is an automorphism of the colimit -/

/-- **Raising to the `d`-th power is bijective on `PowColim G d`.**  Surjective
because a `d`-th root sits one stage up; injective because a class killed by the
`d`-th power was already trivial one stage up.

This is the fact that makes the corner endomorphism `φ_*` of the
Ara--Brustenga--Cortiñas sequence invertible on `K₁(L₀)`. -/
theorem powBijective : Function.Bijective (fun z : PowColim G d ↦ z ^ d) := by
  constructor
  · intro z w hzw
    obtain ⟨n, x, rfl⟩ := ofStage_surjective G d z
    obtain ⟨m, y, rfl⟩ := ofStage_surjective G d w
    have hbeta : (ofStage G d n x) ^ d = (ofStage G d m y) ^ d := hzw
    rw [← map_pow, ← map_pow] at hbeta
    obtain ⟨i, hn, hm, heq⟩ := eq_of_ofStage_eq G d hbeta
    have hxi : (x ^ d) ^ (d ^ (i - n)) = x ^ (d ^ (i + 1 - n)) := by
      have he : d * d ^ (i - n) = d ^ (i + 1 - n) := by
        rw [show i + 1 - n = (i - n) + 1 from by omega, pow_succ']
      rw [← pow_mul, he]
    have hyi : (y ^ d) ^ (d ^ (i - m)) = y ^ (d ^ (i + 1 - m)) := by
      have he : d * d ^ (i - m) = d ^ (i + 1 - m) := by
        rw [show i + 1 - m = (i - m) + 1 from by omega, pow_succ']
      rw [← pow_mul, he]
    rw [hxi, hyi] at heq
    rw [← ofStage_step G d (show n ≤ i + 1 by omega) x,
      ← ofStage_step G d (show m ≤ i + 1 by omega) y, heq]
  · intro z
    obtain ⟨n, x, rfl⟩ := ofStage_surjective G d z
    refine ⟨ofStage G d (n + 1) x, ?_⟩
    show (ofStage G d (n + 1) x) ^ d = ofStage G d n x
    rw [← map_pow]
    have hstep : x ^ d = x ^ (d ^ (n + 1 - n)) := by
      rw [show n + 1 - n = 1 from by omega, pow_one]
    rw [hstep, ofStage_step G d (show n ≤ n + 1 by omega) x]

/-! ### The `(d-1)`-st power quotient -/

/-- **The comparison map** `G → PowColim G d → PowColim G d / (…)^{d-1}`. -/
noncomputable def toQuotient :
    G →* (PowColim G d ⧸
      (powMonoidHom (d - 1) : PowColim G d →* PowColim G d).range) :=
  (QuotientGroup.mk' _).comp (ofStage G d 0)

/-- **The comparison map is surjective.**  A class from stage `n` is carried to
stage `0` by `d^n` powers, and in the `(d-1)`-st power quotient raising to `d`
is the identity. -/
theorem toQuotient_surjective (hd : 2 ≤ d) :
    Function.Surjective (toQuotient G d) := by
  have hd1 : d - 1 + 1 = d := by omega
  intro z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨n, x, rfl⟩ := ofStage_surjective G d w
  refine ⟨x, ?_⟩
  show (QuotientGroup.mk' ((powMonoidHom (d - 1) :
      PowColim G d →* PowColim G d).range)) (ofStage G d 0 x)
    = (QuotientGroup.mk' _) (ofStage G d n x)
  have hzero : ofStage G d 0 x = ofStage G d n (x ^ (d ^ n)) := by
    rw [show (d : ℕ) ^ n = d ^ (n - 0) from by rw [Nat.sub_zero]]
    exact (ofStage_step G d (Nat.zero_le n) x).symm
  rw [hzero, map_pow]
  have hmk := mk_pow_pow_eq_mk (H := PowColim G d) (d - 1) (ofStage G d n x) n
  rw [hd1] at hmk
  exact hmk

/-- **The comparison map kills exactly the `(d-1)`-st powers of `G`.** -/
theorem toQuotient_ker (hd : 2 ≤ d) :
    (toQuotient G d).ker = (powMonoidHom (d - 1) : G →* G).range := by
  have hd1 : d - 1 + 1 = d := by omega
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hmem : ofStage G d 0 x ∈
        (powMonoidHom (d - 1) : PowColim G d →* PowColim G d).range :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨w, hw⟩ := hmem
    obtain ⟨n, y, rfl⟩ := ofStage_surjective G d w
    have hwval : ofStage G d n (y ^ (d - 1)) = ofStage G d 0 x := by
      rw [map_pow]
      exact hw
    obtain ⟨i, hni, h0i, heq⟩ := eq_of_ofStage_eq G d hwval
    have hxpow : (QuotientGroup.mk' ((powMonoidHom (d - 1) : G →* G).range))
        (x ^ (d ^ (i - 0))) = (QuotientGroup.mk' _) x := by
      rw [Nat.sub_zero]
      have hmk := mk_pow_pow_eq_mk (H := G) (d - 1) x i
      rwa [hd1] at hmk
    have hyone : (QuotientGroup.mk' ((powMonoidHom (d - 1) : G →* G).range))
        (y ^ (d - 1)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨y, by rw [powMonoidHom_apply]⟩
    have hone : (QuotientGroup.mk' ((powMonoidHom (d - 1) : G →* G).range)) x
        = 1 := by
      rw [← hxpow, ← heq, map_pow, hyone, one_pow]
    exact (QuotientGroup.eq_one_iff x).mp hone
  · rintro ⟨y, rfl⟩
    show (QuotientGroup.mk (ofStage G d 0 (powMonoidHom (d - 1) y)) :
      PowColim G d ⧸ (powMonoidHom (d - 1) :
        PowColim G d →* PowColim G d).range) = 1
    refine (QuotientGroup.eq_one_iff _).mpr ⟨ofStage G d 0 y, ?_⟩
    rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]

/-- **The printed answer group, at the colimit.**

`G/G^{d-1} ≅ PowColim(G,d)/PowColim(G,d)^{d-1}`.  With `G = k^×` and
`PowColim(k^×,d) = K₁(⋃ₙ M_{dⁿ}(k))`, the right-hand side is the cokernel of
`1 - φ_*` in the Ara--Brustenga--Cortiñas sequence and the left-hand side is the
printed `k^×/(k^×)^{d-1}`. -/
noncomputable def ofStageQuotientEquiv (hd : 2 ≤ d) :
    (G ⧸ (powMonoidHom (d - 1) : G →* G).range) ≃*
      (PowColim G d ⧸
        (powMonoidHom (d - 1) : PowColim G d →* PowColim G d).range) :=
  (QuotientGroup.quotientMulEquivOfEq (toQuotient_ker G d hd)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toQuotient_surjective G d hd))

end PowerColimit
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.PowerColimit.mk_pow_pow_eq_mk
#audit_axioms GroupApproximation.PowerColimit.ofStage_step
#audit_axioms GroupApproximation.PowerColimit.powBijective
#audit_axioms GroupApproximation.PowerColimit.toQuotient_surjective
#audit_axioms GroupApproximation.PowerColimit.toQuotient_ker
#audit_axioms GroupApproximation.PowerColimit.ofStageQuotientEquiv
