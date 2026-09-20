# A complete circuit-group presentation does not authenticate Toffoli semantics

20 September 2026. Bounded constructive-source audit. No computation,
build, or MSI job was run. The HALT-positive source in
`research/lcs-weighted-conjugacy-halting-gap-source.md` remains open.

## Candidate and outcome

The attempted global compiler was to compute a source BCS verifier using
reversible Boolean/quantum gates, share one complete Pauli matrix-algebra
anchor across its occurrences, and express gate composition and propagation
by ordinary group words and conjugacies. This is not a contextwise affine
replacement: one may impose the entire circuit group's presentation and
arbitrary additional globally shared word relations.

The missing step is representation soundness, not presentation completeness.
An exact 512-dimensional model satisfies every word identity of the standard
three-qubit model, keeps its central sign and full Pauli anchor, but violates
the nonlinear Toffoli covariance by squared normalized-HS distance 3/2.
Equivalently, the intended Boolean relation fails on 3/8 of its joint
spectrum. The proof below also covers an arbitrary global group extension
having the standard model, so adding more honest word relations cannot
repair this literal gate decoder.

This is a concrete application of the repository's established ternary
tensor mechanism, not a claim of a new general obstruction principle.
No new canonical claim is added. The additional content is the explicit
nonlinear gate identity, constant defect, and resulting distinction between
a complete circuit presentation and a source-sound matrix decoder.

## Exact calculation

On H=C^8 with basis |a,b,c>, a,b,c in F_2, let X_i flip the ith bit and
let Z_i give its sign. Put J=-I and let the self-adjoint Toffoli involution be

    T|a,b,c> = |a,b,c+ab>.

The X_i,Z_i generate the complete three-qubit Pauli matrix algebra M_8.
In its standard representation,

    T Z_3 T = Z_3 F(Z_1,Z_2),
    F(u,v) = (I+u+v-uv)/2.                              (1)

For commuting involutions u,v, F(u,v) is an involution: on their joint
signs (-1)^a,(-1)^b it has sign (-1)^(ab). Thus (1) is precisely the
non-affine AND operation in the output bit of Toffoli.

Let Gamma be any ordinary group with the indicated distinguished words
and a finite-dimensional representation rho in which these words act as
the displayed matrices, possibly tensored with a common identity factor.
All additional auxiliary generators and all global relations are allowed.
If prescribed central characters occur, denote them collectively by zeta.
The representation

    Psi = rho tensor rho tensor conjugate(rho)            (2)

has exactly the same central characters, since zeta^2 conjugate(zeta)=zeta.
It satisfies every relation of Gamma. In particular it preserves every
ordinary involutory conjugacy and signed commuting-product requirement of
the completed linear-plus-conjugacy compiler. These are exact models, so
all associated word-defect energies are zero for every weighting.

The displayed Toffoli and Pauli matrices are real. On this core, (2) is
therefore their diagonal triple tensor power. Denote the new operators by
T'=T^(tensor 3), Z_i'=Z_i^(tensor 3). The same holds for the X_i'.
All canonical Pauli commutation signs are unchanged, since (-1)^3=-1.
Their generated algebra is still a copy of M_8, acting with multiplicity
64 when rho has dimension 8. Thus this example passes a full Pauli-anchor
test, not merely tests of some commuting Z coordinates.

Write a=(a_1,a_2,a_3), b=(b_1,b_2,b_3), c=(c_1,c_2,c_3) for the three
tensor factors' computational bits. The two sides of the proposed new
identity

    T' Z_3' T' = Z_3' F(Z_1',Z_2')                       (3)

are diagonal in this basis, with exponents respectively

    sum_i c_i + sum_i a_i b_i,
    sum_i c_i + (sum_i a_i)(sum_i b_i).

Their discrepancy is a^T M b over F_2, where M is the 3 by 3 matrix
with zero diagonal and every off-diagonal entry one. Its kernel consists
of 000 and 111: M a=(sum_i a_i)1+a. Hence rank(M)=2. For 2/8 of the
a values the discrepancy is always zero; for the other 6/8, exactly half
the b values give discrepancy one. The mismatch fraction is therefore

    (6/8)(1/2)=3/8.

The c values do not affect that fraction. At each mismatch the two signs
differ by magnitude 2, so normalized Hilbert--Schmidt norm gives

    ||T' Z_3' T' - Z_3' F(Z_1',Z_2')||_2^2 = 4(3/8)=3/2. (4)

Common identity amplifications leave (4) unchanged. Any unitary change
of basis which identifies the new Pauli algebra with its standard M_8
factor also leaves (4) unchanged. In particular the multiplicity freedom
in matrix-algebra authentication cannot turn (3) into a valid identity
while retaining the authenticated anchor observables as the decoded bits.

The elementary assertion that the new anchor is M_8 needs no external
rigidity theorem. Its three Z_i' have all eight joint sign patterns with
equal multiplicity; the X_i' commute with each other and flip those signs
independently. Their joint spectral spaces and the products of X_i'
give the usual matrix units, with one common multiplicity space.

## What the countermodel excludes

Suppose a proposed compiler has exact completeness for this standard gate
model and reads the source bits as the specified anchor Z_i. If its
soundness theorem is intended to imply (1) with an error tending to zero
with the global word defects, (2)--(4) contradict that theorem already at
zero defect. This remains true if the compiler:

- shares the anchor, gate symbols, and all auxiliaries globally;
- includes every valid circuit-group identity, not just a finite list;
- uses noncommuting auxiliaries or additional central-character labels;
- first lowers its word equations by the completed Slofstra-type compiler.

For the last item, the input is already an exact involution model, so the
completed lowering preserves its existence. It cannot authenticate an
additive identity absent from the word theory.

Introducing a word C for T Z_3 T Z_3 is insufficient. In the honest model
C=F(Z_1,Z_2), but in the countermodel it is F(Z_1,Z_2)^(tensor 3), not
F(Z_1^(tensor 3),Z_2^(tensor 3)). A presentation of C as another gate only
names the left-hand expression. A polynomial relation identifying it with
the right-hand expression is the missing non-word condition.

This does NOT refute the HALT-positive source, arbitrary non-affine
decoders, a representation-dependent positive corner, or decoding that
discards the declared anchor bits and reconstructs different source
measurements from the multiplicity space. Such a construction would need
its own global consistency and dimension-independent retained-mass proof.
The countermodel does not supply that proof or show it impossible.

## Existing boundaries and fresh primary checks

The local searches included
`central-character-profiles-affine-under-odd-tensor-products`,
`controlled-pauli-corner-has-clifford-groupification`,
`central-block-hecke-predicates-force-affine-group-spectra`,
`ce-affine-decoder-positive-model-forces-safe-support`,
`wagon-wheel-stops-before-bcs-groupification`, and the shared-anchor
attack artifact. Their tensor, multiplicity, and affine-decoder warnings
are retained. The present calculation does not require scalar source
ports or three separately extendible local source assignments: it tensors
one complete matrix model of the entire proposed circuit system.

Fresh primary-source reconnaissance, 20 September 2026:

- [Culf--Mastel, arXiv:2410.21223v2](https://arxiv.org/abs/2410.21223v2):
  the current revision explicitly corrects the original algebra-map
  reduction and retains Boolean CSPs and 3-colouring, not the original
  blanket claim for every 2-CSP language. This does not remove the needed
  non-affine-to-involutory-word source interface. The existing perfect-gap
  source may be taken from 3-colouring; no withdrawn general-language
  assertion is used here.
- [Bian--Selinger, arXiv:2204.02217v3](https://arxiv.org/abs/2204.02217v3)
  and [arXiv:2306.08530v2](https://arxiv.org/abs/2306.08530v2) provide
  presentations for two-qubit Clifford+T and three-qubit Clifford+CS
  operator groups. The former archive also exposes the Agda completeness
  and soundness files. These are presentation results; no theorem that
  every abstract group representation realizes the intended gate matrices
  is asserted or imported. The countermodel is compatible with their
  results, not a criticism of their correctness.
- [Aharonov, quant-ph/0301040](https://arxiv.org/abs/quant-ph/0301040)
  explains the universality motivation for the Toffoli/Hadamard choice.
  Universality is not needed for (1)--(4).

The upstream CSP and downstream LCS results retain the attribution to
Culf--Mastel, Slofstra, Paddock--Slofstra, and Taller--Vidick given in the
completed compiler artifact. Liu's killed-sign seed and Thom's
normalization do not enter this countermodel. The result is a failed
specific global source mechanism, not another constant separating game
and not a resolution of perfect-completeness RE hardness.
