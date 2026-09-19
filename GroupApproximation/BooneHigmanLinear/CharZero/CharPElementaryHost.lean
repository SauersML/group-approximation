import GroupApproximation.BooneHigmanLinear.CharZero.ElementaryFactor
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFree
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsAway
import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost
import GroupApproximation.BooneHigman.Metabelian.ElemFPEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic-`p` linear host without Suslin's theorem

This is the positive-characteristic companion of `CharZero/ElementaryHost.lean`. It lives in this
directory because it uses the same characteristic-free lemmas (`CharZero/ElementaryFactor.lean`).

* `charP_exists_subring_matrixEmbedding`: for a field `K` of characteristic `p` and any finite
  `t ⊆ K`, some subring `B ⊇ t` embeds in a matrix ring over `F_p[x_0, …, x_{s-1}]`. This is the
  ring layer of `CharPCoords.charPCoordinates_of_finiteDomainAway`, with the same proof:
  `B = F_p[t]`, Noether normalization, generic freeness (`CharPCoords.finiteDomainAwayEmbedding`)
  and `CharPCoords.matrixEmbedding_localizationAway`.
* `charPElementaryCoordinates` is closed. A finitely generated subgroup of `GL_n(K)`,
  `char K = p > 0`, embeds in `E_N(F_p[x_0, …, x_k])` with `N ≥ k + 5`. One variable is added so
  that the self-similar host (which needs `k ≥ 1`) applies.
* `charPLinearHost_of_elementaryFP`: the characteristic-`p` linear host from finite
  presentation of `E_N(F_p[x])` alone (`ElemFP.PolynomialFpElementaryFPStatement`). The
  absorption leaf `Chain.CharPElementaryAbsorptionStatement` is not used. That leaf is Suslin's
  theorem over `F_p[x]`, which route A derives from `S1`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace NoSuslin

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **Char-`p` ring coordinates for any finite set.** For a field `K` of characteristic `p` and a
finite `t ⊆ K`, the subring `F_p[t] ⊇ t` embeds in a matrix ring over `F_p[x_0, …, x_{s-1}]`. -/
theorem charP_exists_subring_matrixEmbedding (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (t : Finset K) :
    ∃ B : Subring K, (↑t : Set K) ⊆ B ∧ ∃ s : ℕ,
      Coordinates.MatrixEmbedding B (MvPolynomial (Fin s) (ZMod p)) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra (ZMod p) K, A = Algebra.adjoin (ZMod p) (↑t : Set K) :=
    ⟨_, rfl⟩
  have hsub : (↑t : Set K) ⊆ (A.toSubring : Set K) := by
    rw [Subalgebra.coe_toSubring, hA]
    exact Algebra.subset_adjoin
  haveI : Algebra.FiniteType (ZMod p) A :=
    (Subalgebra.fg_iff_finiteType A).mp (by
      rw [hA]
      exact Subalgebra.fg_adjoin_finset t)
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  obtain ⟨f, hf⟩ := CharPCoords.finiteDomainAwayEmbedding (ZMod p) s A g.toRingHom hginj hgfin
  let ι : ↥A.toSubring →+* ↥A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (congrArg Subtype.val hxy)
  exact ⟨A.toSubring, hsub, s, (Coordinates.MatrixEmbedding.of_injective ι hι).trans
    (hf.trans (CharPCoords.matrixEmbedding_localizationAway f))⟩

#audit_axioms charP_exists_subring_matrixEmbedding

/-- **Elementary polynomial coordinates in characteristic `p`**: every finitely generated subgroup
of `GL_n(K)`, `char K = p > 0`, embeds in `E_N(F_p[x_0, …, x_k])` for some `k` and `N ≥ k + 5`. -/
def CharPElementaryCoordinatesStatement : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 0 < p → ringChar K = p →
    ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      ∃ k N : ℕ, k + 5 ≤ N ∧
        ∃ f : H →* elementaryGroup (Fin N) (Chain.CharPPoly p (k + 1)), Function.Injective f

#audit_axioms CharPElementaryCoordinatesStatement

/-- **Elementary polynomial coordinates in characteristic `p`, proved.** No Suslin input. -/
theorem charPElementaryCoordinates : CharPElementaryCoordinatesStatement := by
  intro K _ p hp hK n H hH
  haveI : CharP K p := ringChar.of_eq hK
  haveI : NeZero p := ⟨hp.ne'⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨t, ht⟩ := exists_finset_elementary_embedding H.subtype H.subtype_injective
  obtain ⟨B, hB, s, hemb⟩ := charP_exists_subring_matrixEmbedding K p t
  obtain ⟨φ, hφ⟩ := ht B hB
  obtain ⟨d, Φ, hΦ⟩ := hemb.trans (Coordinates.MatrixEmbedding.of_injective
    (MvPolynomial.rename (R := ZMod p) (Fin.castSucc : Fin s → Fin (s + 1))).toRingHom
    (MvPolynomial.rename_injective (R := ZMod p) (Fin.castSucc : Fin s → Fin (s + 1))
      (Fin.castSucc_injective s)))
  obtain ⟨f, hf⟩ := exists_elementary_transport (N := 2 * n + 2) (by omega) Φ hΦ (s + 5)
  exact ⟨s, (2 * n + 2) * d + (s + 5), by omega, f.comp φ, hf.comp hφ⟩

#audit_closed_axioms charPElementaryCoordinates

/-- **The characteristic-`p` linear host from finite presentation of `E_N` alone.** Every finitely
generated subgroup of `GL_n(K)`, `char K = p > 0`, embeds in a finitely presented self-similar
group, given only that `E_N(F_p[x_0, …, x_{k-1}])` is finitely presented for `N ≥ k + 4`. -/
theorem charPLinearHost_of_elementaryFP (hfp : ElemFP.PolynomialFpElementaryFPStatement) :
    Chain.CharPLinearHostStatement := by
  intro K _ p hp hK n H hH
  obtain ⟨k, N, hN, f, hf⟩ := charPElementaryCoordinates K p hp hK n H hH
  haveI : CharP K p := ringChar.of_eq hK
  have hprime : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right (by omega)
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Group.IsFinitelyPresented
      (Chain.AffineElementaryGroup N (Chain.CharPPoly p (k + 1))) :=
    Chain.affineExtensionFPStatement_holds (Chain.CharPPoly p (k + 1))
      (Chain.finiteType_int_transfer _
        (Chain.finiteType_int_of_surjective _ (Chain.charPPoly_map_surjective p (k + 1))) _)
      N (by omega) (hfp p hprime (k + 1) N (by omega))
  obtain ⟨X, _, _, ρ, hρ⟩ :=
    CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds p (k + 1) N (by omega) (by omega)
  exact Chain.embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ hf

#audit_axioms charPLinearHost_of_elementaryFP

end NoSuslin
end BooneHigmanLinear
end GroupApproximation
