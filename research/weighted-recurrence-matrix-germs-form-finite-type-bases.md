---
rg: 2
id: weighted-recurrence-matrix-germs-form-finite-type-bases
kind: claim
title: Bounded superdiagonal weights turn recurrence profile matrices into finitely generated nilpotent observation groups with injective shift
artifacts:
  - research/artifacts/beyond-polynomial-germs/recurrence-and-matrix-proofs.md
---

For finitely many eventually integral recurrent coefficient tails and
fixed matrix size `r`, choose a forward lattice `E` including `1` and
all scalar exponents and unipotent coefficients, from both endpoints
viewed on one forward index. Let `C_j` be the ℤ-span of products of
at most `j` elements of `E`, `C₀=ℤ1`. Then all `C_j` are finitely
generated, are shift invariant, have injective shift and no nonzero
eventually-zero elements, and satisfy `C_iC_j⊂C_(i+j)`.

The profile group `𝒰` of unitriangular matrices with `(i,j)` entry in
`C_(j−i)` is finitely generated torsion-free nilpotent and contains
constant `UT_r(ℤ)`. The central scalar product `L=E×𝒰`, realized as
`q^a I·U`, has type `F_∞`, injective shift and faithful germ
realization. It contains the whole constant depth-zero arithmetic
isotropy `UT_r(ℤ)×⟨qI⟩`.

## Attempts

Artifact Section 8 uses finite monomial bases, rational invertible
shift matrices and tensor powers to exclude eventually-zero products.
Weighted multiplication and inversion preserve superdiagonal degree;
elementary elimination gives finite generation. The supplied proof
needs independent review of these exact claims. No unrestricted
finite-rank ring closure is asserted: profiles `2^(kn)` already make
that false. Only weights up to `r−1` occur. The example commutator
of `I+2^nE₁₂` and `I+3^nE₂₃` lands in the required `6^nE₁₃`
weight-two slot. This substantive lemma has no complete-proof route yet.
