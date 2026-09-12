import GroupApproximation.GGT.OsinTheorem54SepAssemble
import GroupApproximation.GGT.OsinTheorem54SepLemma510Right
import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.OsinTheorem54SepMultiplicity
import GroupApproximation.GGT.OsinTheorem54SepLemma49
import GroupApproximation.GGT.OsinLemma56Inheritance

/-!
# The assembly, with both halves of Lemma 5.10 discharged

`GGT/OsinTheorem54SepAssemble.lean` removed `hdist` from the binder list of
`sepDataFam_of_binders`; this module removes `hsle` as well, by passing in
`sep_le_dist_enlargedY`.  It sits downstream for the same reason that one does:
`SepInhabit` is imported by everything that proves either half, so neither half
can be folded into it in place.

What that leaves, and what each thing is:

* `hthr` --- `Dc` lies past the §4.2 threshold: SOME constant `C` bounds the
  isolated components of polygons with at most six sides, and `4C ≤ Dc`.  This
  is the whole of the geometry that the assembly still asks for, and it is one
  hypothesis where Osin's Lemmas 4.8 and 4.9 used to be two.
* `hloc` --- local finiteness of the enlarged relative metrics, Lemma 5.8.
* `h511` --- Lemma 5.11, the residue.

Five things that used to be on that list are not on it any more.

Osin's Lemmas 4.8 and 4.9 are theorems: `lemmaFourEight_forall_of_bound` and
`lemmaFourNine_of_bound` prove them from exactly the bound and threshold that
`hthr` packages, so the two binders collapse into it.  The threshold cannot be
dropped as well, because `C` is produced BY the bound and a signature that fixes
`Dc` first has nothing to compare it against; `OsinTheorem54SepAssembleHemb`
quantifies `C` first and so needs no threshold hypothesis at all --- it is the
form to call when `hemb` is in hand and `Dc` has not been chosen yet.

Lemma 5.6's bounded-detour condition is a theorem too.
`OsinLemma56Inheritance.exists_boundedDetour` proves it from `1 ≤ Dc` and a
symmetric base alone, routing through the base case of Lemma 5.10 rather than
through its counting form, so `hM` is supplied here rather than assumed.

Both halves of Lemma 5.10 are theorems of this tree, `dist_le_sep_enlargedY`
and `sep_le_dist_enlargedY`.

Lemma 5.5 is one too.  It was a declared debt until the guessing-geodesics
criterion was proved; `GuessingGeodesicsCriterion.osinLemma55` now supplies it,
so `h55` is gone from the binder list rather than passed through it.

The multiplicity hypothesis is gone as well.  `mult_of_relBall_one` proves it
outright --- an element of two distinct members of the family lies in the
radius-`Dc` ball of either --- so what was once a constraint on the choice of
`Dc` is now a consequence of `1 ≤ Dc`, which the assembly already assumes.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` at one `D`, modulo the §4.2 threshold, Lemma 5.8's
condition, and Lemma 5.11.**

The multiplicity hypothesis is gone too: `mult_of_relBall_one` proves it from
`1 ≤ Dc` alone.

Both halves of Lemma 5.10 are supplied here rather than assumed, and so is
Lemma 5.5: `GuessingGeodesicsCriterion.osinLemma55` proves it outright, so the
`h55` binder is gone from the list.  What Lemma 5.5 was carrying --- the passage
from hyperbolicity of `Γ(G,X ⊔ ℋ)` to hyperbolicity of the enlarged graph ---
is now a theorem of this tree, and `hloc` is what remains of that clause: the
local finiteness of Lemma 5.8.  The bounded-detour condition it consumes is
`exists_boundedDetour`, passed in below.

`hloc` and `h511` are binders here but not debts: one rung up,
`OsinEnlargement.exists_sepDataFam_of_hemb` discharges both from `hemb` --- the
first by `OsinComponents.relBall_enlargedY_finite`, the second by the Lemma 5.11
chain, which needs the bound `hthr` already carries.  They stay binders at this
rung because discharging them here would put the 5.11 modules in this file's
import closure and collapse the distinction from the rung above. -/
theorem sepDataFam_of_binders_of_lemma510 [Fintype Λ] (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hthr : ∃ C : ℕ,
      (∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D 1 0 n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) ∧ C * 4 ≤ Dc)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hloc : ∀ (lam : Λ) (n : ℕ),
      ((enlargedY D hDc hsymm).relBall lam n).Finite)
    (h511 : ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
        {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.Finite ∧
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.ncard ≤ N) :
    ∃ S : SepDataFam D, S.AcylindricalCore := by
  obtain ⟨C, hbnd, hCDc⟩ := hthr
  have h48 : ∀ lam : Λ, LemmaFourEight D lam Dc :=
    lemmaFourEight_forall_of_bound D hsymm hbnd hCDc
  have h49 := lemmaFourNine_of_bound D hsymm hbnd hCDc h48
  exact sepDataFam_of_binders_of_dist D hDc hsymm h48 h49 osinLemma55 hemb
    (exists_boundedDetour D hDc hsymm) hloc
    (fun f g => sep_le_dist_enlargedY D hDc hsymm h48
      (mult_of_relBall_one D hDc) h49 f g) h511

end OsinEnlargement
end GGT
end GroupApproximation
