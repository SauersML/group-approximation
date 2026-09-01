import GroupApproximation.GGT.OsinTheorem54SepAssembleHemb
import GroupApproximation.GGT.OsinTheorem54SepSymmetricFam

/-!
# Osin's Theorem 5.4, without geometric binders

This closes the separating-coset proof of Osin's Theorem 5.4.  A finite
hyperbolically embedded family first receives a symmetric relative generating
set.  The six-gon bound then determines a sufficiently large cutoff `D`, and
the completed Lemmas 5.6, 5.8, 5.10, and 5.11 produce the enlarged generating
set and its acylindrical action.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.GGT.OsinComponents

universe u w

/-- **Osin, Theorem 5.4**, for a finite family of peripheral subgroups. -/
theorem osinTheorem54Fam_unconditional : OsinTheorem54Fam.{u, w} := by
  intro G _inst Λ _finite D hemb
  letI : Fintype Λ := Fintype.ofFinite Λ
  obtain ⟨Dsymm, hbase, hfam, hsymm, hembSymm, -⟩ :=
    exists_symmetric_base' D hemb
  obtain ⟨C, _hC, hsep⟩ :=
    exists_sepDataFam_of_hemb Dsymm hsymm hembSymm
  let Dc := max 1 (C * 4)
  obtain ⟨S, hcore⟩ := hsep Dc (le_max_left 1 (C * 4))
    (le_max_right 1 (C * 4))
  exact ⟨S.enlarged, hbase.trans S.base_subset, S.fam_eq.trans hfam,
    S.emb, S.isAcylindrical_of_core hcore⟩

/-- **Osin, Theorem 5.4**, in the one-subgroup form used by Theorem 1.2. -/
theorem osinTheorem54_unconditional : OsinTheorem54.{u} :=
  osinTheorem54_of_fam osinTheorem54Fam_unconditional

end OsinEnlargement
end GGT
end GroupApproximation
