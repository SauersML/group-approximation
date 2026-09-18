import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilCharP
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal stability on `ker ev₀`: reduction to elements killed by every augmented
specialization to one variable fewer

Lane `bh-met-95a`.  Target: the second conjunct `PolyK2StabRangeDiagStatementOver (ZMod p) 4` of
the leaf `P1 = PolyK2NilGapStatementOver (ZMod p) 4` (module `ElemFPCharZeroK2NilGeneric`).
Write `R_k = A[s_1..s_k]` and `cc = MvPolynomial.constantCoeff : R_k → A` (`ev₀`).

## LOUD: the target is not a statement about `F_p[s]` alone

`PolyK2StabRangeDiagStatementOver A 4` quantifies over **every** `k ≥ 1`.  For `k ≥ 2` the ring
`F_p[s_1..s_k]` is not a PID, let alone Euclidean.  So no Euclidean normal form over `F_p[s]`
can close the target: the Euclidean ring only appears as the instance `k = 1`.  The reduction
below makes this precise.  After it, the only instance that still concerns `F_p[s]` is the base
instance `k = 0` of the residual, and that instance is **not** proved here.

## The residual

`stabDiagFp_SpecStatementOver A d`: for `k ≥ 0` and every rank `N ≥ (k + 1) + d`, an element
`u ∈ K₂(N, R_{k+1})` with `K2Stab N u = 1` is trivial, **provided** `K2Map φ u = 1` for every
ring map `φ : R_{k+1} →+* R_k` with `cc ∘ φ = cc` (an *augmented specialization* to one
variable fewer).

* The extra hypothesis implies `cc u = 1`: take `φ = C ∘ cc` and use `cc ∘ C = id`.  So each
  instance is weaker than the corresponding instance of `PolyK2NilStabilityStatementOver A d`.
* It is not vacuous.  It contains `s_i ↦ 0` followed by renumbering (so `u` is killed by every
  cube projection `π_i` of `ElemFPCharZeroCubePosStab`), and every substitution
  `s_i ↦ f(s_{≠ i})` with `f(0) = 0`.  Maps to fewer than `k` variables are covered too:
  compose with the renaming `R_j → R_k`, which has the left inverse `killCompl` and respects `cc`.
* At `k = 0` the only augmented map `A[s] → A` is `s ↦ 0`, so the base instance is exactly the
  one-variable statement: `u ∈ K₂(N, A[s])`, `N ≥ 1 + d`, `ev₀ u = 1` and `K2Stab u = 1`
  imply `u = 1`.

## What is proved

* `stabDiagFp_stab_of_spec`: the residual gives injective stability on `ker cc` over `R_k` for
  every `k ≥ 0` and every rank `N ≥ k + d`.  Induction on `k`.  At `k = 0`, `cc` is an
  isomorphism (`eq_one_of_K2Map_constantCoeff_eq_one`).  At `k + 1`, for each augmented
  `φ : R_{k+1} → R_k`, the element `φ u` has `cc (φ u) = cc u = 1` and trivial stabilization
  (naturality), and lives at rank `N ≥ k + d`, so the induction hypothesis kills it.  This is
  why the residual has to carry every rank `N ≥ (k + 1) + d` and not just the diagonal: the
  induction hypothesis is used one rank above the diagonal of `R_k`.
* `stabDiagFp_stabRangeDiagOver_of_spec`: the residual gives `PolyK2StabRangeDiagStatementOver`.
* `stabDiagFp_spec_of_stabRangeDiagOver`: the converse (via `polyK2NilStabilityOver_of_diag`).
* `stabDiagFp_nilGapOver_of_spec`, `stabDiagFp_polyK2StabRangeDiag_of_spec`: the endpoints at
  `P1`'s parameters (`A = ZMod p`, `d = 4`) and in the char-`p` form.

## LOUD: strength

The residual is **logically equivalent** to the target (both directions are proved here).  It
is instancewise weaker (extra hypothesis on `u`), and strictly smaller in proof content: the
induction on the number of variables, the passage from the diagonal to all ranks, and the
naturality bookkeeping are discharged.  What remains is van der Kallen's injective stability on
the elements killed by every augmented specialization, including the base instance over `A[s]`.
It is **not** equivalent to `vdkParPres_NoHiddenRelStatement`: that statement concerns every
ring of stable rank `≤ r` and all of `K₂`.  The rings here are fixed and only a subset of
`ker ev₀` is concerned.  The bridge from `ker Π = ⊥` is `ElemFPStabDiagFpBridge`.

## Truth check

By the converse, the residual at `(ZMod p, 4)` follows from `PolyK2StabRangeDiagStatement`.  That
is true: `sr(F_p[s_1..s_k]) ≤ k + 1` (Bass), and van der Kallen's injective stability for `K₂`
holds for `n ≥ sr + 2`, while here `n ≥ k + 4`.  Small sanity check of the induction: at `k = 0`
the residual is the base instance over `F_p[s]` at ranks `N ≥ 5`.  There `sr(F_p[s]) ≤ 2`
(`vdkStab_stableRangeLE_polyOne`), so van der Kallen already covers `n ≥ 4`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- Trivial stabilization is preserved by coefficient maps (naturality of `K2Stab`). -/
theorem stabDiagFp_K2Stab_K2Map_eq_one {R S : Type*} [Ring R] [Ring S] {n : ℕ} (f : R →+* S)
    {u : K2n n R} (hu : K2Stab n R u = 1) : K2Stab n S (K2Map f u) = 1 :=
  (K2IndexMap_K2Map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) f u).trans
    ((DFunLike.congr_arg (K2Map (I := Fin (n + 1)) f) hu).trans
      (map_one (K2Map (I := Fin (n + 1)) f)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_K2Stab_K2Map_eq_one

/-- `cc ∘ (C ∘ cc) = cc`: the map `C ∘ cc : R_{k+1} → R_k` is an augmented
specialization. -/
theorem stabDiagFp_cc_comp_C_comp (A : Type*) [CommRing A] (k : ℕ) :
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A).comp
        ((MvPolynomial.C : A →+* MvPolynomial (Fin k) A).comp
          (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A)) =
      MvPolynomial.constantCoeff := by
  rw [← RingHom.comp_assoc, MvPolynomial.constantCoeff_comp_C, RingHom.id_comp]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_cc_comp_C_comp

/-- **The residual** (lane `bh-met-95a`): for `k ≥ 0` and every rank `N ≥ (k + 1) + d`, an
element of `K₂(N, A[s_0..s_k])` with trivial stabilization that is killed by every augmented
specialization `φ : A[s_0..s_k] → A[s_1..s_k]` (`cc ∘ φ = cc`) is trivial.
LOUD: equivalent to `PolyK2StabRangeDiagStatementOver A d`
(`stabDiagFp_spec_iff_stabRangeDiagOver`); strictly smaller in proof content only. -/
def stabDiagFp_SpecStatementOver (A : Type*) [CommRing A] (d : ℕ) : Prop :=
  ∀ k N : ℕ, k + 1 + d ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) A),
      (∀ φ : MvPolynomial (Fin (k + 1)) A →+* MvPolynomial (Fin k) A,
        (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A).comp φ =
            MvPolynomial.constantCoeff →
          K2Map φ u = 1) →
      K2Stab N (MvPolynomial (Fin (k + 1)) A) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_SpecStatementOver

/-- **Induction on the number of variables**: the residual gives injective stability on
`ker cc` over `A[s_1..s_k]` for every `k ≥ 0` and every rank `N ≥ k + d`. -/
theorem stabDiagFp_stab_of_spec (A : Type*) [CommRing A] (d : ℕ)
    (h : stabDiagFp_SpecStatementOver A d) (k : ℕ) :
    ∀ N : ℕ, k + d ≤ N → ∀ u : K2n N (MvPolynomial (Fin k) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin k) A) u = 1 → u = 1 := by
  induction k with
  | zero =>
    intro N _ u hu0 _
    exact eq_one_of_K2Map_constantCoeff_eq_one hu0
  | succ k ih =>
    intro N hN u hu0 hu
    refine h k N hN u (fun φ hφ ↦ ?_) hu
    refine ih N (by omega) (K2Map φ u) ?_ (stabDiagFp_K2Stab_K2Map_eq_one φ hu)
    rw [K2Map_K2Map, hφ, hu0]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_stab_of_spec

/-- **Endpoint**: the residual gives diagonal injective stability on `ker ev₀` at offset `d`. -/
theorem stabDiagFp_stabRangeDiagOver_of_spec (A : Type*) [CommRing A] (d : ℕ)
    (h : stabDiagFp_SpecStatementOver A d) : PolyK2StabRangeDiagStatementOver A d :=
  fun k _ u hu0 hu ↦ stabDiagFp_stab_of_spec A d h k (k + d) le_rfl u hu0 hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_stabRangeDiagOver_of_spec

/-- **The converse**: diagonal injective stability on `ker ev₀` gives the residual.  The
hypothesis at `φ = C ∘ cc` gives `cc u = 1`; then use stability at `k + 1` variables and rank
`N ≥ (k + 1) + d` (`polyK2NilStabilityOver_of_diag`). -/
theorem stabDiagFp_spec_of_stabRangeDiagOver (A : Type*) [CommRing A] (d : ℕ)
    (h : PolyK2StabRangeDiagStatementOver A d) : stabDiagFp_SpecStatementOver A d := by
  intro k N hN u hφ hu
  have h1 := hφ ((MvPolynomial.C : A →+* MvPolynomial (Fin k) A).comp
    (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A))
    (stabDiagFp_cc_comp_C_comp A k)
  have hcc : K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A) u = 1 :=
    calc K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A) u
        = K2Map ((MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A).comp
            ((MvPolynomial.C : A →+* MvPolynomial (Fin k) A).comp
              (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A))) u := by
          rw [stabDiagFp_cc_comp_C_comp A k]
      _ = K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A)
            (K2Map ((MvPolynomial.C : A →+* MvPolynomial (Fin k) A).comp
              (MvPolynomial.constantCoeff : MvPolynomial (Fin (k + 1)) A →+* A)) u) :=
          (K2Map_K2Map _ _ u).symm
      _ = 1 := by rw [h1, map_one]
  exact polyK2NilStabilityOver_of_diag A d h (k + 1) N (by omega) hN u hcc hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_spec_of_stabRangeDiagOver

/-- **LOUD (strength)**: the residual is equivalent to the target. -/
theorem stabDiagFp_spec_iff_stabRangeDiagOver (A : Type*) [CommRing A] (d : ℕ) :
    stabDiagFp_SpecStatementOver A d ↔ PolyK2StabRangeDiagStatementOver A d :=
  ⟨stabDiagFp_stabRangeDiagOver_of_spec A d, stabDiagFp_spec_of_stabRangeDiagOver A d⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_spec_iff_stabRangeDiagOver

/-- **Endpoint at `P1`'s parameters**: the one-variable nil part (lane `bh-met-94c`) and the
residual over `ZMod p` give the leaf `PolyK2NilGapStatementOver (ZMod p) 4`. -/
theorem stabDiagFp_nilGapOver_of_spec (p : ℕ) (hnil : PolyK2OneVarNilStatementOver (ZMod p))
    (hspec : stabDiagFp_SpecStatementOver (ZMod p) 4) :
    PolyK2NilGapStatementOver (ZMod p) 4 :=
  ⟨hnil, stabDiagFp_stabRangeDiagOver_of_spec (ZMod p) 4 hspec⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_nilGapOver_of_spec

/-- **Char-`p` endpoint**: the residual over every `ZMod p`, `p` prime, gives
`PolyK2StabRangeDiagStatement`. -/
theorem stabDiagFp_polyK2StabRangeDiag_of_spec
    (h : ∀ p : ℕ, p.Prime → stabDiagFp_SpecStatementOver (ZMod p) 4) :
    PolyK2StabRangeDiagStatement :=
  polyK2StabRangeDiag_iff_forall_over.mpr fun p hp ↦
    stabDiagFp_stabRangeDiagOver_of_spec (ZMod p) 4 (h p hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagFp_polyK2StabRangeDiag_of_spec

end GroupApproximation.BooneHigman.Metabelian.ElemFP
