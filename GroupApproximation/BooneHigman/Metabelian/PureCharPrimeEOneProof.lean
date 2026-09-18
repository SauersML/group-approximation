import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import GroupApproximation.BooneHigman.GroupRing.Noetherian
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEStatement
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProofField
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProofPiece
import GroupApproximation.Meta.AxiomGuard

/-!
# Pure characteristic `p`, exponent `p`: the module statement (lane bh-met-52)

`pureCharPrimeEOne : PureCharPrimeEOneStatement`.

Proof.  `R = 𝔽_p[Q]` is Noetherian (Hilbert basis theorem), so the finitely generated module `M`
has a coprimary decomposition `0 = S_1 ∩ ... ∩ S_n` (`Primary.exists_coprimary_decomposition`).
Each `M ⧸ S_j` is coprimary, with prime `P_j` and exponent `e_j`.  It need not be an `R ⧸ P_j`-module, but
the Frobenius twist `r ↦ r ^ (p ^ e_j)` makes it one, finite and torsion-free over the domain
`R ⧸ P_j`.  So it embeds `Q`-equivariantly into `K_j^{d_j}` with `K_j = Frac(R ⧸ P_j)` of
characteristic `p` (`exists_charP_linearization_of_coprimary`).  Embed all `K_j` into one field
`L` of characteristic `p` (`exists_common_field_charP_finset`) and assemble the block-diagonal
representation (`exists_linearization_of_field_pieces`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **The exponent-`p` module statement holds.** -/
theorem pureCharPrimeEOne : PureCharPrimeEOneStatement := by
  intro p hp Q _ hQ hfg M _ _ hfin
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hQ }
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.FG Q := hfg
  haveI : Module.Finite (MonoidAlgebra (ZMod p) Q) M := hfin
  haveI : IsNoetherianRing (MonoidAlgebra (ZMod p) Q) := GroupRing.isNoetherianRing_monoidAlgebra
  obtain ⟨n, S, P, e, hS, -, hP⟩ :=
    Primary.exists_coprimary_decomposition (MonoidAlgebra (ZMod p) Q) M
  choose K _ d ρ ι hchar hinj hequiv using
    fun j : Fin n => exists_charP_linearization_of_coprimary (hP j)
  haveI : ∀ j, CharP (K j) p := hchar
  obtain ⟨L, _, hL, hemb⟩ := exists_common_field_charP_finset p K Finset.univ
  have f : ∀ j, K j →+* L := fun j => Classical.choice (hemb j (Finset.mem_univ j))
  obtain ⟨d', ρ', ι', hinj', hequiv'⟩ :=
    exists_linearization_of_field_pieces (fun q (m : M) => MonoidAlgebra.of (ZMod p) Q q • m)
      K f d ρ (fun j => (ι j).comp (S j).mkQ.toAddMonoidHom)
      (fun m hm => hS m fun i => by
        have h0 : ι i (Submodule.Quotient.mk m) = ι i 0 :=
          (hm i).trans (map_zero (ι i)).symm
        exact (Submodule.Quotient.mk_eq_zero (S i)).mp (hinj i h0))
      (fun j q m => hequiv j q (Submodule.Quotient.mk m))
  exact ⟨L, inferInstance, d', ι', ρ', ringChar.eq_iff.mpr hL, hinj', hequiv'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharPrimeEOne

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
