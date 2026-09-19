import GroupApproximation.BooneHigmanLinear.K2Poly.Statements
import GroupApproximation.Meta.AxiomGuard
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Panin's geometric presentation, specialized to polynomial rings (lane k2-panin)

The Lavrenov–Sinchuk–Voronetsky route to `P1` (`K2Poly.Statements`, section `LSV`) uses one
geometric input: Panin's Theorem 2.8 of LSV (arXiv:2110.11087), which is Theorem 1.2 / 2.5 of
Panin, *Nice triples and Grothendieck–Serre's conjecture…* (arXiv:1707.01756).  It enters only the
proof of LSV Cor 2.9.  In general it needs Artin elementary fibrations, étale neighbourhoods and,
over a finite field, Poonen's Bertini theorem, none of which Mathlib has.  For the rings of the
chain, two reductions remove it.

* **Finite to infinite field** (`unstableNKAt_of_ratFunc`, proved here).  Unstable `NK₂` over
  `F[s₁..s_k]` follows from unstable `NK₂` over `F(T)[s₁..s_k]`, together with monic injectivity
  over `F[s₁..s_k][X]` (Horrocks, `HorrocksMonicAt`, residue fields finite) and a finitary
  statement for `F → F(T)` (`RatFuncFinitaryAt`, from board piece F.5).  So LSV are needed only
  over the infinite field `F_p(T)`.
* **Linear presentation over an infinite field** (`AffineMonicFibreStatement`, stated here and
  proved in `PaninAffine.Main`). Let `K` be infinite, `R = K[s₀..s_n]`, `M` a closed point with
  `f ∈ M`, and `f'` coprime to `f` with `f' ∉ M`. A shear `sⱼ₊₁ ↦ sⱼ₊₁ + aⱼ s₀` has two effects:
  - `f` becomes monic in `s₀` up to a constant;
  - `f` and `f'` have no common zero on the `s₀`-fibre through `M`.
  With `C = K[s₁..s_n]` and `𝔭 = M ∩ C`, Nakayama then makes `(f, f')` the unit ideal of
  `C_𝔭[s₀]`. So in LSV Cor 2.9, Zariski excision (LSV Lemma 2.6, from Tulenbaev's patching,
  board piece F.4) and monic injectivity (Lemma 2.7) suffice. Neither the Nisnevich excision
  (A3) nor an étale neighbourhood is needed.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigman

section Geometry

/-- **The fibre map** of the coordinates `φ`: `K[s₁..s_n] → R/M`, `sⱼ ↦ φ⁻¹(sⱼ₊₁) mod M`.
Its kernel is `𝔭 = φ(M) ∩ K[s₁..s_n]`, the point under `M` of the base of the projection that
forgets `s₀`. Mapping coefficients along it restricts a polynomial in `s₀` to the fibre over `𝔭`,
viewed over the extension field `R/M` of the residue field `k(𝔭)`. -/
noncomputable def fibreMap {K : Type} [Field K] {n : ℕ} (M : Ideal (MvPolynomial (Fin (n + 1)) K))
    (φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin (n + 1)) K ⧸ M :=
  (Ideal.Quotient.mk M).comp
    ((φ.symm : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K).toRingHom.comp
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fibreMap

/-- **Affine presentation over a field `K`** (board piece GEO, specialized to polynomial rings).
Let `M` be a maximal ideal of `K[s₀..s_n]`, let `f ∈ M` be nonzero, and let `f' ∉ M` be coprime
to `f`. Then some `K`-automorphism `φ` satisfies:
- `φ f` is a nonzero constant times a polynomial monic in `s₀` over `K[s₁..s_n]`;
- `φ f` and `φ f'` are coprime on the fibre through `M`, i.e. coprime in `(R/M)[s₀]` after
  mapping coefficients along `fibreMap M φ`.
By `Polynomial.isCoprime_map` the fibre condition descends to the residue field `k(𝔭)`. Since
`φ f` is monic up to a unit, Nakayama then makes `(φ f, φ f')` the unit ideal of
`K[s₁..s_n]_𝔭[s₀]`. That is the Zariski-excision input of LSV Cor 2.9 (see
`research/artifacts/gq-k2-panin-affine-presentation.md`). For an infinite `K`, a linear `φ` (a
shear) works: `PaninAffine.Main.infiniteFieldAffineMonicFibre`. -/
def AffineMonicFibreStatement (K : Type) [Field K] : Prop :=
  ∀ (n : ℕ) (f f' : MvPolynomial (Fin (n + 1)) K) (M : Ideal (MvPolynomial (Fin (n + 1)) K)),
    M.IsMaximal → f ∈ M → f' ∉ M → f ≠ 0 → IsRelPrime f f' →
      ∃ φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K,
        (∃ c : K, c ≠ 0 ∧ (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c * φ f)).Monic) ∧
          IsCoprime ((MvPolynomial.finSuccEquiv K n (φ f)).map (fibreMap M φ))
            ((MvPolynomial.finSuccEquiv K n (φ f')).map (fibreMap M φ))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.AffineMonicFibreStatement

/-- The affine presentation for every infinite field. It is the only geometric input the
polynomial-ring case of the LSV route needs, once `unstableNKAt_of_ratFunc` has moved the finite
base field `F_p` to `F_p(T)`. Proved in `PaninAffine.Main`. -/
def InfiniteFieldAffineMonicFibreStatement : Prop :=
  ∀ (K : Type) [Field K] [Infinite K], AffineMonicFibreStatement K

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.InfiniteFieldAffineMonicFibreStatement

end Geometry

section Descent

/-- Coefficient extension `F[s₁..s_k] → F(T)[s₁..s_k]`. -/
noncomputable abbrev ratFuncCoeff (F : Type) [Field F] (k : ℕ) :
    MvPolynomial (Fin k) F →+* MvPolynomial (Fin k) (RatFunc F) :=
  MvPolynomial.map (algebraMap F (RatFunc F))

/-- **Finitary input for `F → F(T)`** (a consequence of board piece F.5).  Let `B = F[s₁..s_k]`.
An element of `St_r(B[X])` that dies after extending coefficients from `F` to `F(T)` already dies
in every commutative ring where some monic `g ∈ F[T]` becomes a unit.  Here `T` is the outer
variable of `B[X][T]`.
Why it holds: `F(T)[s][X]` is the directed colimit of the rings `F[T]_g[s][X]`, and a monic
normalization of `g` has the same localization. -/
def RatFuncFinitaryAt (F : Type) [Field F] (k r : ℕ) : Prop :=
  ∀ y : SteinbergBasic.St r (Polynomial (MvPolynomial (Fin k) F)),
    SteinbergGroup.ringMap (Polynomial.mapRingHom (ratFuncCoeff F k)) y = 1 →
      ∃ g : Polynomial F, g.Monic ∧
        ∀ (S : Type) [CommRing S] (φ : Polynomial (Polynomial (MvPolynomial (Fin k) F)) →+* S),
          IsUnit (φ (g.map ((Polynomial.C : MvPolynomial (Fin k) F →+*
              Polynomial (MvPolynomial (Fin k) F)).comp MvPolynomial.C))) →
            SteinbergGroup.ringMap (φ.comp Polynomial.C) y = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.RatFuncFinitaryAt

/-- `X ↦ 0` commutes with extending coefficients. -/
theorem evalRingHom_zero_comp_mapRingHom {R S : Type} [CommRing R] [CommRing S] (ι : R →+* S) :
    (Polynomial.evalRingHom 0 : Polynomial S →+* S).comp (Polynomial.mapRingHom ι) =
      ι.comp (Polynomial.evalRingHom 0) := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_map]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.evalRingHom_zero_comp_mapRingHom

/-- **Finite to infinite base field.**  Unstable `NK₂` over `F[s₁..s_k]` follows from:
* unstable `NK₂` over `F(T)[s₁..s_k]`;
* the finitary input for `F → F(T)`;
* monic injectivity (Horrocks) over `F[s₁..s_k][X]`.

Proof: `u` dies over `F(T)`, hence wherever some monic `g ∈ F[T]` is a unit.  Horrocks kills the
constant image of `u` in `St_r(B[X][T])`, and `T ↦ 0` recovers `u`. -/
theorem unstableNKAt_of_ratFunc {F : Type} [Field F] {k r : ℕ}
    (hInf : UnstableNKAt (MvPolynomial (Fin k) (RatFunc F)) r)
    (hFin : RatFuncFinitaryAt F k r)
    (hH : HorrocksMonicAt (Polynomial (MvPolynomial (Fin k) F)) r) :
    UnstableNKAt (MvPolynomial (Fin k) F) r := by
  intro u hu
  have hcomm := evalRingHom_zero_comp_mapRingHom (ratFuncCoeff F k)
  have h0 : SteinbergGroup.ringMap
      (Polynomial.evalRingHom 0 : Polynomial (MvPolynomial (Fin k) F) →+* MvPolynomial (Fin k) F)
      (u : SteinbergBasic.St r (Polynomial (MvPolynomial (Fin k) F))) = 1 :=
    congrArg Subtype.val hu
  -- the image of `u` over `F(T)` is killed by `X ↦ 0`
  have hu' : SteinbergBasic.K2Map
      (Polynomial.evalRingHom 0 : Polynomial (MvPolynomial (Fin k) (RatFunc F)) →+*
        MvPolynomial (Fin k) (RatFunc F))
      (SteinbergBasic.K2Map (Polynomial.mapRingHom (ratFuncCoeff F k)) u) = 1 := by
    apply Subtype.ext
    show SteinbergGroup.ringMap
        (Polynomial.evalRingHom 0 : Polynomial (MvPolynomial (Fin k) (RatFunc F)) →+*
          MvPolynomial (Fin k) (RatFunc F))
        (SteinbergGroup.ringMap (Polynomial.mapRingHom (ratFuncCoeff F k))
          (u : SteinbergBasic.St r (Polynomial (MvPolynomial (Fin k) F)))) = 1
    rw [SteinbergBasic.ringMap_ringMap, hcomm, ← SteinbergBasic.ringMap_ringMap, h0, map_one]
  have hy : SteinbergGroup.ringMap (Polynomial.mapRingHom (ratFuncCoeff F k))
      (u : SteinbergBasic.St r (Polynomial (MvPolynomial (Fin k) F))) = 1 :=
    congrArg Subtype.val (hInf _ hu')
  obtain ⟨g, hg, hkill⟩ := hFin _ hy
  have hkill' : ∀ (S : Type) [CommRing S]
      (φ : Polynomial (Polynomial (MvPolynomial (Fin k) F)) →+* S),
      IsUnit (φ (g.map ((Polynomial.C : MvPolynomial (Fin k) F →+*
        Polynomial (MvPolynomial (Fin k) F)).comp MvPolynomial.C))) →
      SteinbergGroup.ringMap φ (SteinbergGroup.ringMap
        (Polynomial.C : Polynomial (MvPolynomial (Fin k) F) →+*
          Polynomial (Polynomial (MvPolynomial (Fin k) F)))
        (u : SteinbergBasic.St r (Polynomial (MvPolynomial (Fin k) F)))) = 1 := by
    intro S _ φ hφ
    rw [SteinbergBasic.ringMap_ringMap]
    exact hkill S φ hφ
  have hα := hH (g.map ((Polynomial.C : MvPolynomial (Fin k) F →+*
      Polynomial (MvPolynomial (Fin k) F)).comp MvPolynomial.C)) (hg.map _) _ hkill'
  apply Subtype.ext
  have h := congrArg (SteinbergGroup.ringMap
    (Polynomial.evalRingHom 0 : Polynomial (Polynomial (MvPolynomial (Fin k) F)) →+*
      Polynomial (MvPolynomial (Fin k) F))) hα
  rw [SteinbergBasic.ringMap_ringMap, Metabelian.ElemFP.evalRingHom_zero_comp_C,
    SteinbergBasic.ringMap_id, map_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.unstableNKAt_of_ratFunc

/-- **The `F_p` target from the `F_p(T)` target.**  `UnstableNKPolyFpStatement`, which is the whole
of `P1` (bh-pal-wire, 01437ed31f), follows from unstable `NK₂` over every `F_p(T)[s₁..s_k]`, the
finitary input, and monic injectivity over `F_p[s₁..s_k][X]`. -/
theorem unstableNKPolyFp_of_ratFunc
    (hInf : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r →
      UnstableNKAt (MvPolynomial (Fin k) (RatFunc (ZMod p))) r)
    (hFin : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r → RatFuncFinitaryAt (ZMod p) k r)
    (hH : ∀ (p : ℕ) [Fact p.Prime] (k r : ℕ), 5 ≤ r →
      HorrocksMonicAt (Polynomial (MvPolynomial (Fin k) (ZMod p))) r) :
    UnstableNKPolyFpStatement := by
  intro p hp k r hr
  haveI : Fact p.Prime := ⟨hp⟩
  exact unstableNKAt_of_ratFunc (hInf p k r hr) (hFin p k r hr) (hH p k r hr)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.unstableNKPolyFp_of_ratFunc

end Descent

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
