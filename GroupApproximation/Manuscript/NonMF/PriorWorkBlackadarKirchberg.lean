import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.FiniteDimensionalCStarWedderburn
import GroupApproximation.Analysis.LanceNFUnitalCPAP
import GroupApproximation.Meta.AxiomGuard

/-!
# `Relation to prior work`: the Blackadar--Kirchberg NF characterization

`non_mf_groups_exist.tex`, subsection *"Relation to prior work"*:

> Blackadar and Kirchberg developed the notions of MF and NF algebras and proved
> that a separable `C*`-algebra is NF if and only if it is nuclear and
> MF [BK].

`blackadarKirchberg_nfAlgebra_iff` below is that equivalence, stated at the
repository's independent finite-local NF predicate `IsNFAlgebra`, at
`CStarExactness.IsNuclearCStarAlgebra`, and at the bare MF-embedding predicate
`HasMFEmbedding`, with separability as the printed standing hypothesis.

## Which input is cited, and why

Exactly one: **the converse half of Blackadar--Kirchberg's characterization** —
a separable nuclear MF `C*`-algebra is NF.  It is exposed below as the leading
binder `BlackadarKirchbergNFConverseInput`; no theorem in this file hides the
citation behind an assumed hypothesis or an axiom.

The forward half is *not* cited.  `IsNFAlgebra` is defined in
`Analysis/NFAlgebra.lean` independently of nuclearity and of MF — its data are
completely positive contractions through a finite-dimensional matrix block that
recover a prescribed finite set and are approximately multiplicative there — so
the forward implication is a theorem and not an unfolding:

* separability is carried in the predicate (`IsNFAlgebra.separable`);
* nuclearity is `IsNFAlgebra.isNuclearCStarAlgebra`, which reuses the same CPC
  data as a completely positive approximating net for the identity; and
* the MF property is `IsNFAlgebra.isMFAlgebra`, which diagonalizes the local
  data into a sequence model, builds the corona homomorphism, and proves it
  injective from contractivity of the upward maps.

## Why the Wedderburn step is not the citation

The note that graded this sentence `partial` in
`metadata/NON_MF_SENTENCE_MAP.tsv` records the missing step as the assembly of
the finite-dimensional Wedderburn blocks.  That step is no longer missing, and
citing it would overstate what is unproved.  The repository has, unconditionally:

* `BlackadarKirchberg.exists_algEquiv_directMatrixSum_of_finiteDimensionalCStar`
  — the algebraic Artin--Wedderburn decomposition of a finite-dimensional
  complex `C*`-algebra, obtained from vanishing of its Jacobson radical
  (`finiteDimensionalCStar_jacobson_eq_bot`, proved from the `C*`-identity
  applied to `star a * a`);
* `BlackadarKirchberg.exists_starAlgEquiv_matrix_of_finiteDimensional_simpleCStar`
  — the `*`-isomorphism of a finite-dimensional simple block with a full matrix
  algebra, after correcting the transported involution to the adjoint; and
* `BlackadarKirchberg.exists_completelyPositiveContractive_matrix_lift` and
  `exists_completelyPositiveContractive_directMatrixSum_lift` — completely
  positive contractive lifting along the matrix-corona quotient out of one
  block and out of a finite direct sum of blocks.

What none of that supplies is the analytic content of the converse: producing,
from nuclearity's completely positive approximations and an MF corona
embedding, downward maps that are *approximately multiplicative* on a
prescribed finite set — the generalized-inductive-limit construction of
Blackadar and Kirchberg.  That, and only that, is cited.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace PriorWork

open CStarExactness ReducedGroupCStarTrace

universe u

-- LITERATURE INPUT: Blackadar--Kirchberg, Generalized inductive limits
-- of finite-dimensional C*-algebras, Math. Ann. 307 (1997), no. 3, 343--380;
-- the converse half of the NF characterization.
/-- **The exact Blackadar--Kirchberg converse interface.**

A separable nuclear MF `C*`-algebra is NF.  Separability is carried inside
`IsMFAlgebra`.

This is the direction that produces new approximation data rather than reading
it off: nuclearity gives completely positive contractions through
finite-dimensional algebras, MF gives a faithful corona embedding, and
Blackadar and Kirchberg combine them into downward maps that are approximately
multiplicative on a prescribed finite set.  The repository supplies the
finite-dimensional structure theory and the completely positive lifting used in
that combination — see the module docstring — but not the combination
itself.  Every type and structure binder is inside this proposition, so a
consumer must carry this citation explicitly. -/
def BlackadarKirchbergNFConverseInput : Prop :=
  ∀ (A : Type u) [CStarAlgebra A],
    IsNuclearCStarAlgebra A → IsMFAlgebra A → IsNFAlgebra A

/-- Apply the exact cited converse interface at one C-star algebra. -/
theorem blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra
    (bk : BlackadarKirchbergNFConverseInput.{u})
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A) :
    IsNFAlgebra A :=
  bk A hnuc hMF

/-- **Blackadar--Kirchberg CPAP/NF connected to the Lance interface.**

For a reduced group C-star algebra, the cited converse half of the
Blackadar--Kirchberg characterization turns nuclearity together with an MF
model into finite-local NF data.  The unconditional
`nuclearReducedCPAP_of_isNFAlgebra` theorem then repairs the CPC factorization
to a UCP factorization and transports its matrix block to the operator-algebra
target required by `NuclearReducedCPAP`.

Thus the only cited content in this composite is still the existing BK
converse above; the contractive-to-unital and matrix/operator steps introduce
no further input. -/
theorem blackadarKirchberg_nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra
    (bk : BlackadarKirchbergNFConverseInput.{0})
    (G : Type) [Group G]
    (hnuc : IsNuclearCStarAlgebra (ReducedGroupCStar G))
    (hMF : IsMFAlgebra (ReducedGroupCStar G)) :
    NuclearReducedCPAP G :=
  nuclearReducedCPAP_of_isNFAlgebra G
    (blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra bk hnuc hMF)

/-- **The printed sentence.**

> Blackadar and Kirchberg ... proved that a separable `C*`-algebra is NF if and
> only if it is nuclear and MF [BK].

The forward implication is proved here, from the repository's independent
finite-local NF predicate: it is `IsNFAlgebra.isNuclearCStarAlgebra` together
with the corona-embedding half of `IsNFAlgebra.isMFAlgebra`.  The converse is
the cited half, applied to `⟨hsep, hmf⟩ : IsMFAlgebra A`, which is where the
printed separability hypothesis is spent. -/
theorem blackadarKirchberg_nfAlgebra_iff {A : Type u} [CStarAlgebra A]
    (bk : BlackadarKirchbergNFConverseInput.{u})
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsNFAlgebra A ↔ IsNuclearCStarAlgebra A ∧ HasMFEmbedding A := by
  constructor
  · intro hA
    exact ⟨hA.isNuclearCStarAlgebra, hA.isMFAlgebra.2⟩
  · rintro ⟨hnuc, hmf⟩
    exact blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra bk hnuc
      ⟨hsep, hmf⟩

end PriorWork
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.PriorWork

#audit_axioms BlackadarKirchbergNFConverseInput
#audit_axioms blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra
#audit_axioms blackadarKirchberg_nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra
#audit_axioms blackadarKirchberg_nfAlgebra_iff
