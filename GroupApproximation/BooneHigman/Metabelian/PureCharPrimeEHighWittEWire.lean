import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittETWPoly
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittERing
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEMod
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittTransport
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighETwoUnits
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighMixed
import Mathlib.RingTheory.MvPolynomial.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The infinite mixed coprimary case, for every `e ≥ 2` (bh-met-87h, part 12)

This proves `eHighMixed_InfiniteStatement` outright (`eHighWittE_infinite`), and with it
`PureCharPrimeEHighModuleStatement` (`eHighWittE_pureCharPrimeEHighModule`). The steps are:

1. `M ↪ D_eⁿ` additively, with `q ∈ Q` acting by a matrix `U q` over `D_e`
   (`eHighWittE_module`).
2. Compose with the injective ring map `φ : D_e →+* W_e(L)`, where `L = Frac(𝔽_p[X₁..X_d])`
   (`eHighWittE_phi`). This gives `M ↪ W_e(L)ⁿ` with `q` acting by `φ (U q)`
   (`eHighWittE_embed_tw`).
3. On `W_e(L)ⁿ`, translations and matrix actions are weight-polynomial, which gives an
   invariant, separating, finite-dimensional function space (`eHighWittE_tw_polyFun`).
4. Restrict it to `M` (`eHighWitt_transport`). The translation algebra is then a
   finite-dimensional commutative `L`-algebra containing `M` multiplicatively
   (`eHighArtinHasse_exists_units_of_polyFun`).
5. Left multiplication in a basis gives the representation (`eHighETwo_exists_gl_of_units`).
   Its field `L` has characteristic `p`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- Composing the embedding `M ↪ D_eⁿ` with `φ` gives `M ↪ W_e(L)ⁿ` with matrices `φ (U q)`. -/
theorem eHighWittE_embed_tw (p e : ℕ) [NeZero e] [Fact p.Prime] (d n : ℕ) {M Q : Type}
    [AddCommGroup M] (act : Q → M → M) (j : M →+ (Fin n → eHighWittE_D p e (Fin d)))
    (hj : Function.Injective j) (U : Q → Fin n → Fin n → eHighWittE_D p e (Fin d))
    (hU : ∀ (q : Q) (m : M) (i : Fin n), j (act q m) i = ∑ l, U q i l * j m l) :
    ∃ ι : M →+ (Fin n → TruncatedWittVector p e (eHighWittE_L p (Fin d))),
      Function.Injective ι ∧ ∀ (q : Q) (m : M),
        ι (act q m) = fun i => ∑ l, eHighWittE_phi p e (Fin d) (U q i l) * ι m l := by
  refine ⟨{ toFun := fun m i => eHighWittE_phi p e (Fin d) (j m i),
            map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · funext i
    show eHighWittE_phi p e (Fin d) (j 0 i) = 0
    simp only [map_zero, Pi.zero_apply]
  · intro a b
    funext i
    show eHighWittE_phi p e (Fin d) (j (a + b) i) =
      eHighWittE_phi p e (Fin d) (j a i) + eHighWittE_phi p e (Fin d) (j b i)
    simp only [map_add, Pi.add_apply]
  · intro a b hab
    refine hj (funext fun i => eHighWittE_phi_injective p e (Fin d) ?_)
    exact congrFun hab i
  · intro q m
    funext i
    show eHighWittE_phi p e (Fin d) (j (act q m) i) =
      ∑ l, eHighWittE_phi p e (Fin d) (U q i l) * eHighWittE_phi p e (Fin d) (j m l)
    rw [hU q m i, map_sum]
    simp only [map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_embed_tw

/-- **The infinite mixed coprimary case, for every `e ≥ 2`.** -/
theorem eHighWittE_infinite : eHighMixed_InfiniteStatement := by
  intro p hp e he Q _ hfg M _ _ hfin P k hM hpP hk _ _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero e := ⟨by omega⟩
  obtain ⟨d, n, j, U, hj, hU⟩ := eHighWittE_module p e Q hfg M hfin P k hM hpP (by omega)
  obtain ⟨ι, hι, hιU⟩ := eHighWittE_embed_tw p e d n
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m) j hj U hU
  obtain ⟨V, hfd, htrans, hact, hsep⟩ :=
    eHighWittE_tw_polyFun (fun q i l => eHighWittE_phi p e (Fin d) (U q i l))
  obtain ⟨W, hWfd, hWtrans, hWact, hWsep⟩ := eHighWitt_transport ι hι
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)
    (fun q x i => ∑ l, eHighWittE_phi p e (Fin d) (U q i l) * x l) hιU V hfd htrans hact hsep
  haveI : FiniteDimensional (eHighWittE_L p (Fin d)) W := hWfd
  obtain ⟨B, _, _, _, θ, σ, hθ, hequiv⟩ := eHighArtinHasse_exists_units_of_polyFun
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)
    (fun q x y => smul_add (MonoidAlgebra.of (ZMod (p ^ e)) Q q) x y)
    (fun _ _ _ => by simp only [map_mul, mul_smul])
    (fun _ => by simp only [map_one, one_smul]) W hWtrans hWact hWsep
  obtain ⟨d', κ, ρ, hκ, hκρ⟩ := eHighETwo_exists_gl_of_units
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m) θ hθ σ hequiv
  exact ⟨eHighWittE_L p (Fin d), inferInstance, d', κ, ρ,
    ringChar.eq (eHighWittE_L p (Fin d)) p, hκ, hκρ⟩

#audit_closed_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_infinite

/-- **The high-exponent module statement, outright.** -/
theorem eHighWittE_pureCharPrimeEHighModule : PureCharPrimeEHighModuleStatement :=
  eHighMixed_pureCharPrimeEHighModule_of_infinite eHighWittE_infinite

#audit_closed_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pureCharPrimeEHighModule

end GroupApproximation.BooneHigman.Metabelian.Coprimary
