import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.Hyperlinear

/-!
# LEF groups are sofic and hyperlinear

Pestov's Open Question 9.1 (*Hyperlinear and sofic groups: a brief guide*,
arXiv:0804.3968v8, p. 21) asks whether an infinite simple group with Kazhdan's
property `(T)` can be hyperlinear (sofic).  The witness of this development is
an LEF group, and this module supplies the approximation half of the answer:
an LEF group is sofic, and so hyperlinear.

Both steps are theorems of this repository, and nothing here adds a hypothesis.

1. **LEF ⇒ sofic** is `GroupApproximation.isSofic_of_isLEF` in
   `Sofic/LEFSofic.lean`.  The left-regular representation of the finite target
   of a local embedding is a permutation model with multiplicative defect `0`
   and Hamming separation `1`.
2. **Sofic ⇒ hyperlinear** is `GroupApproximation.isHyperlinear_of_isSofic` in
   `Sofic/Hyperlinear.lean`.  Permutation matrices are unitary, and the squared
   normalized Hilbert–Schmidt distance between two of them is twice the
   normalized Hamming distance between the permutations.

`isHyperlinear_of_isLEF` composes them.  The positive control for the
hypothesis is `GroupApproximation.isLEF_of_finite` in `Sofic/LEF.lean`: every
finite group is LEF, so the theorem is not about an empty class.

Both conclusions are the local finite-set definitions `IsSofic` and
`IsHyperlinear`.  Their bodies are those of the Pestov 9.1 Challenge's
`IsSoficGroup` and `IsHyperlinearGroup`, with the model carrier bundled as a
`FiniteModel` rather than the Challenge's `FiniteCarrier`.  A Solution file
therefore bridges into the Challenge by repackaging the carrier and nothing
else, as `Palomar/SurjunctiveNonsoficSolution.lean` does for `IsSoficGroup`.
-/

namespace GroupApproximation
namespace Pestov91

variable {G : Type*} [Group G]

/-- **LEF groups are hyperlinear.**  An LEF group is sofic
(`isSofic_of_isLEF`), and a sofic group is hyperlinear
(`isHyperlinear_of_isSofic`). -/
theorem isHyperlinear_of_isLEF (h : IsLEF G) : IsHyperlinear G :=
  isHyperlinear_of_isSofic (isSofic_of_isLEF h)

end Pestov91
end GroupApproximation
