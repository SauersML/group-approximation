import GroupApproximation.BooneHigmanLinear.K2Poly.Statements
import GroupApproximation.Meta.AxiomGuard
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

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
* **Linear presentation over an infinite field** (`AffineMonicFibreStatement`, stated here; the
  proof is in `research/artifacts/gq-k2-panin-affine-presentation.md`).  Let `K` be infinite,
  `R = K[s₀..s_n]`, `M` a closed point with `f ∈ M`, and `f'` coprime to `f` with `f' ∉ M`.  A
  linear change of coordinates makes `f` monic in `s₀` and leaves no common zero of `f` and `f'`
  on the `s₀`-line over the point.  Panin's étale neighbourhood can then be taken to be the
  principal localization `A[t]_{p(f')}`, where `A = R_M`, `p(sᵢ) = sᵢ` for `i ≥ 1` and
  `p(s₀) = s₀ + t`, with `h = p(f)` monic.  LSV's Nisnevich excision (A3) is then used only in its
  Zariski form (LSV Lemma 2.6, which follows from Tulenbaev's patching, board piece F.4).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigman

section Geometry

/-- **The fibre condition.**  With `s₀` as the fibre variable (the variable `MvPolynomial.finSuccEquiv`
singles out), `f` and `f'` generate the unit ideal modulo the image of `M ∩ K[s₁..s_n]`.  In other
words, they have no common zero on the `s₀`-line over the image of the closed point `M`. -/
def FibreCoprime {K : Type} [Field K] {n : ℕ} (M : Ideal (MvPolynomial (Fin (n + 1)) K))
    (f f' : MvPolynomial (Fin (n + 1)) K) : Prop :=
  Ideal.span {f, f'} ⊔
      Ideal.map (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1)))
        (Ideal.comap (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))) M) = ⊤

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.FibreCoprime

/-- **Affine presentation over a field `K`** (board piece GEO, specialized to polynomial rings).
Let `M` be a maximal ideal of `K[s₀..s_n]`, let `f ∈ M` be nonzero, and let `f' ∉ M` be coprime
to `f`.  Then some `K`-automorphism `φ` makes `φ f` a nonzero constant times a polynomial monic in
`s₀` over `K[s₁..s_n]`, and makes `φ f`, `φ f'` satisfy the fibre condition at `φ(M)`.  For an
infinite `K` a linear `φ` works (see the module docstring). -/
def AffineMonicFibreStatement (K : Type) [Field K] : Prop :=
  ∀ (n : ℕ) (f f' : MvPolynomial (Fin (n + 1)) K) (M : Ideal (MvPolynomial (Fin (n + 1)) K)),
    M.IsMaximal → f ∈ M → f' ∉ M → f ≠ 0 → IsRelPrime f f' →
      ∃ φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K,
        (∃ c : K, c ≠ 0 ∧ (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c * φ f)).Monic) ∧
          FibreCoprime (Ideal.map φ M) (φ f) (φ f')

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.AffineMonicFibreStatement

/-- The affine presentation for every infinite field.  This is the only geometric input the
polynomial-ring case of the LSV route needs, once `unstableNKAt_of_ratFunc` has moved the finite
base field `F_p` to `F_p(T)`. -/
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
