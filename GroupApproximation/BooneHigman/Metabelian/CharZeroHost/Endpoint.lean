import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Host
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.ZInv
import GroupApproximation.BooneHigman.Metabelian.ChainCharZero
import GroupApproximation.Meta.AxiomGuard

/-!
# The char-zero self-similar host over `ℤ[1/m][t]` (lane bh-met-09)

Research node `polynomial-parameter-affine-groups-are-self-similar`: for `n ≥ 1` the affine
host `S^n ⋊ E_n(S)`, `S = ℤ[1/m][t_1, …, t_k]`, acts faithfully and self-similarly on a regular
rooted tree over a finite alphabet with at least two letters.

**Route.**
* `m ≠ 0`: pick a prime `p ∤ m` (`exists_prime_not_dvd`); `ℤ[1/m]` is a Noetherian char-zero
  domain with digit data at `p` (`digitAway`), so `exists_rep_affineElementary` applies.
* `m = 0`: `ℤ[1/0]` is the zero ring (`away_zero_eq_one`), so the affine host is trivial
  (`affineElementary_eq_of_zero_eq_one`) and the trivial representation on the binary tree is
  faithful and self-similar (`exists_rep_of_zero_eq_one`).
Endpoint: `charZeroAffineSelfSimilarStatement`, proving `Chain.CharZeroAffineSelfSimilarStatement`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

/-- Over the zero ring the affine elementary group is trivial. -/
theorem affineElementary_eq_of_zero_eq_one {R : Type} [CommRing R] (h01 : (0 : R) = 1)
    {n : ℕ} (x y : Chain.AffineElementaryGroup n R) : x = y := by
  have h1 : (Multiplicative.toAdd x.left : Fin n → R) = Multiplicative.toAdd y.left :=
    funext fun _ => eq_of_zero_eq_one h01 _ _
  have h2 : ((x.right : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) =
      ((y.right : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) :=
    Matrix.ext fun _ _ => eq_of_zero_eq_one h01 _ _
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective h1) (Subtype.ext (Units.ext h2))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.affineElementary_eq_of_zero_eq_one

/-- Over the zero ring the trivial representation on the binary tree is a faithful
self-similar representation. -/
theorem exists_rep_of_zero_eq_one {R : Type} [CommRing R] (h01 : (0 : R) = 1) (n : ℕ) :
    ∃ (X : Type) (_ : Finite X) (_ : Nontrivial X)
      (ρ : Chain.AffineElementaryGroup n R →* Trees.TreeAut X), Trees.IsSelfSimilarRep ρ :=
  ⟨Bool, inferInstance, inferInstance, 1,
    fun x y _ => affineElementary_eq_of_zero_eq_one h01 x y,
    (Trees.isSelfSimilar_range_iff (1 : Chain.AffineElementaryGroup n R →* Trees.TreeAut Bool)).2
      fun γ _ => ⟨γ, by rw [MonoidHom.one_apply, Trees.TreeAut.state_one]⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_rep_of_zero_eq_one

/-- **Endpoint** (research node `polynomial-parameter-affine-groups-are-self-similar`): the
affine host over `ℤ[1/m][t_1, …, t_k]` has a faithful self-similar tree representation. -/
theorem charZeroAffineSelfSimilarStatement : Chain.CharZeroAffineSelfSimilarStatement := by
  intro m k n hn
  by_cases hm : m = 0
  · have h01 : (0 : Chain.SIntPoly m k) = 1 :=
      calc (0 : Chain.SIntPoly m k) = MvPolynomial.C (0 : Localization.Away (m : ℤ)) :=
            (map_zero _).symm
        _ = MvPolynomial.C 1 := congrArg MvPolynomial.C (away_zero_eq_one hm)
        _ = 1 := map_one _
    exact exists_rep_of_zero_eq_one h01 n
  · obtain ⟨p, hp, hdvd⟩ := exists_prime_not_dvd hm
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : IsDomain (Localization.Away (m : ℤ)) := isDomain_away hm
    haveI : CharZero (Localization.Away (m : ℤ)) := charZero_away hm
    haveI : IsNoetherianRing (Localization.Away (m : ℤ)) := isNoetherianRing_away m
    exact exists_rep_affineElementary (k := k) (digitAway hp hdvd) (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.charZeroAffineSelfSimilarStatement

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
