# Relative embeddability of the SL3 double: corrected proof boundary

Initial audit: 2026-08-21. Corrected: 2026-09-07.

The original audit checked the stated hypotheses of Gao's Appendix Theorem
7.1 but missed an inclusion required by its proof diagram. The group
conclusion remains established by a new tensor proof, described below.

## What the primary source states

[Gao, with appendix by Marius Junge and David Gao,
arXiv:2012.07940v3](https://arxiv.org/html/2012.07940v3#S7), Theorem 7.1,
identifies RE/N1 with embeddability of the enlarged amalgam

    (M tensor L-infinity(S1)) *_N M

into (R tensor N1)^omega, for a finite-factor coefficient N1. It also
states the same equivalence for the plain double when M has a unitary u
whose nonzero powers all have zero N-expectation.

## The missing arrow in the former arithmetic replay

For C=SL_3(Z), A=SL_3(Z[1/2]), the unitary of
h=diag(2,1,1/2) does satisfy E_L(C)(u^k)=0 for every k != 0. However,
printed page 35 uses the further inclusion

    L(C) subset {u}' intersect (L(A) *_L(C) L(A)).

This inclusion fails: h (I+E12) h^(-1)=I+2E12 is different from I+E12.
The source's vanishing-average calculation on L(A) minus L(C) does not
show that its conditional expectation fixes L(C). The previous audit
therefore did not verify this argument. This is a gap in that proof,
not a counterexample to the theorem's statement. See the complete
[commuting-square audit](centralizer-hnn-relative-embedding-audit-2026-09-07.md).

## The replacement group proof

The independently proved
[tensor-swap theorem](tensor-swap-expectation-repair-2026-09-07.md) works
for every countable C <= A. Hyperlinearity of D=A *_C A passes to its
index-two factor-swap extension E=A *_C(C x C2), using an explicit
block matrix construction. Its canonical involution s satisfies

    tau(u_g^* s u_g s)=1_C(g).

Averaging over s gives squared conditional-expectation norm one on C and
one half outside C. Tensoring k copies raises these norms to the kth
power. A countable diagonalization produces finite matrix subalgebras
whose expectations fix the subgroup and kill every off-subgroup group
unitary. This is scalar relative embeddability, with every inclusion
and expectation identity verified. It needs no relative-Haar element.

The valid forward relative-amalgam theorem proves the reverse direction.
For the arithmetic pair, residual finiteness of SL_3(Z) makes its group
factor Connes embeddable. Gao Proposition 2.2 then identifies scalar
relative embeddability with relative embeddability over L(C), as recorded
in `sl3-re-over-lattice-iff-re-over-scalars`. Thus

    D hyperlinear iff L(C) subset L(A) is RE/scalars
                  iff L(C) subset L(A) is RE/L(C).

This is the current proof behind
`sl3-arithmetic-double-gao-equivalence-proof`. The equivalence does not
establish either positive or negative embeddability of the chosen pair.
