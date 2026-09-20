# Controlled-Pauli authentication: a quantitative fixed-port boundary

Date: 2026-09-20. Bounded follow-up to
`lcs-anchored-attack-2026-09-20.md`. No computation or build was run.
This records a failed authentication target, not a new hardness theorem.
The tensor principle is already established in the repository; no duplicate
canonical claim or route is added.

## 1. What was tested

The previous globally shared candidate admits inactive isotropic gates:
`s_t=I` but `U_t!=I`. The requested repair would add ordinary group
relations and auxiliary generators so that, in every marked matrix model,

    U_t=(1-q_t)+X q_t,   V_t=(1-q_t)+Z q_t,

where `X,Z` are one Pauli anchor. We allow the proposed projection `q_t`
to be an arbitrary, potentially non-affine matrix-algebra readout. It need
not equal `(1-s_t)/2`. The original ports `U_t,X` remain group words.

This more generous fixed-port target already fails by tensoring one whole
honest model. No context-private gluing and no K4 combinatorics are needed.

## 2. Exact assumptions and construction

Let Gamma be any group presentation, finite or infinite, with words
`J,X,Z,U,s`. Suppose it has a finite-dimensional representation rho on
`C^2 tensor K` such that

    rho(J)=-I,  rho(X)=X_Pauli tensor I,
    rho(Z)=Z_Pauli tensor I,
    rho(s)=I tensor (1-2p),
    rho(U)=I tensor (1-p)+X_Pauli tensor p,

for a projection `p` with normalized trace `t` strictly between zero and
one. All other generators, including globally shared auxiliaries, are
whatever this honest representation supplies.

Form the representation

    R = rho tensor rho tensor conjugate(rho).

Every defining relation of Gamma still holds exactly. In particular this
is a countermodel to an arbitrary ordinary-group completion having the
displayed honest model, not just to the equations from the earlier artifact.
Also `R(J)=-I`. More generally every prescribed scalar central character
is preserved, since `lambda^2 conjugate(lambda)=lambda`.

The anchor is

    X_* = X_1 X_2 X_3,  Z_* = Z_1 Z_2 Z_3,

and anticommutes as required. Its negative Pauli representation can be
unitarily put in standard `M_2 tensor I` form. This does not change any
of the norm calculations below.

Let `p_1,p_2,p_3` denote the three tensor-factor controls, with the third
complex-conjugated. Their joint spectral branches are indexed by
`a=(a_1,a_2,a_3)` in `{0,1}^3`. Branch a has normalized weight

    t^|a| (1-t)^(3-|a|),

and on it

    U_* = product_(i:a_i=1) X_i,
    s_* = (-1)^(a_1+a_2+a_3) I.

The Pauli factors are independent of these controls in the original
honest representation, so their normalized trace on every nonzero branch
is the standard three-qubit trace.

## 3. A lower bound against every decoded projection

Set `e_+=(I+X_*)/2`. Every literal controlled-X operator obeys

    e_+ [(1-q)+X_* q-I] = 0.                          (A)

This identity holds even without requiring q to commute with X_*; the
intended controlled form does of course require the relevant commutation.
Consequently, for every projection q,

    ||U_* - [(1-q)+X_*q]||_2^2
        >= ||e_+(U_*-I)||_2^2.                        (B)

On branches `000` and `111`, the right side vanishes. On each of the six
mixed branches, `U_*` and `X_*` are distinct nonidentity commuting Pauli
words, and their product is also nonidentity. Hence

    tr(U_*)=tr(X_*)=tr(X_* U_*)=0

on that branch. As `U_*` is an involution,

    tr(e_+(U_*-I)^2)
      = tr((I+X_*)(I-U_*)) = 1.

Adding the branch weights gives the exact obstruction

    ||e_+(U_*-I)||_2^2
       = 1-t^3-(1-t)^3
       = 3t(1-t).                                    (C)

Thus no projection q whatsoever gives the desired literal controlled
form, and its normalized-HS distance from every such form is at least
`sqrt(3t(1-t))`, although all ordinary relator defects are zero.
For a half-rank honest control the squared lower bound is `3/4`.

If the decoder is specifically `q=(1-s_*)/2`, the exact squared defect is

    ||U_* - [(1-q)+X_*q]||_2^2 = 6t(1-t).             (D)

Indeed, on every mixed branch the intended and actual Pauli words are
distinct, so their squared normalized-HS distance is two. The two constant
branches agree. At half rank the squared defect in (D) is `3/2`.

The same calculation applies to the controlled-Z port. Simultaneous
unitary conjugation or restandardization of the Pauli anchor cannot alter
(B)--(D).

If a source has two scalar perfect solutions assigning an atom differently,
and the completion extends both, their direct sum first produces the
honest half-rank model needed here. A source with an already nontrivial
projection needs no such preliminary sum.

## 4. Concrete filters and matrix-frame alternatives checked

A tempting spectral filter is an odd-order relation `(UR)^m=1`, with R
fixed in the qubit anchor and m odd. It would exclude the unwanted sign
`U=-I` on the inactive sector if `R^m=1`. But completeness on both honest
scalar controls would require `R^m=(XR)^m=I`. Their determinants differ
by `det(X)=-1`; two determinants of odd-order matrices cannot differ by
minus one. This particular two-dimensional filter already breaks perfect
completeness. This determinant check is deliberately not asserted for
arbitrary larger auxiliary packets; (B)--(C) handle any ordinary-group
completion that retains the specified honest ports.

A genuinely different possibility is to decode projections directly from
matrix units of a finite nonabelian anchor, abandoning U as the literal
controlled operator. An incidence construction might use context frames
and stable letters to identify their prescribed matrix blocks. Ordinary
conjugacy relations can identify entire subgroup representations and
therefore their specified matrix-algebra projections. However, the source
PVM relations supply equality of projections, not equality of the entire
auxiliary frames. Perfect completeness would need a simultaneous choice
of all those frames, across noncommuting contexts. No such extension
construction was obtained in this bounded attack. Merely writing a
projection as a linear combination of anchor words does not turn that
linear combination into an ordinary relator.

The existing `group-corner-decoders-split-into-coset-and-matrix-readouts`
shows why this remaining distinction is real: nonabelian matrix readouts
can realize an already given perfect matrix model. It does not construct
a source-independent or source-computable presentation that forces an
unknown perfect model, nor the simultaneous frame extensions just needed.

## 5. Boundary, source check, and relation to existing work

Read before this attack: the README; the earlier anchored countermodel;
`controlled-pauli-corner-has-clifford-groupification`;
`central-corner-block-is-not-a-group-word`;
`controlled-pauli-commutator-is-and-times-multiplicity-commutator`;
`controlled-pauli-commutator-robustly-measures-projection-overlap`;
`pauli-gauge-word-retains-and-cocycle`;
`ce-affine-decoder-positive-model-forces-safe-support` and its proof;
and `group-corner-decoders-split-into-coset-and-matrix-readouts` and proof.
Lexical duplicate searches found the tensor and affine obstructions but
not the explicit decoder-independent error calculation (B)--(C). It is
recorded as an application of the existing tensor principle, not claimed
as a new general research theorem.

The primary [Taller--Vidick v2 introduction](https://arxiv.org/html/2507.22444v2#S1)
was rechecked on 2026-09-20. It explicitly separates its noisy completeness
theorem from the perfect-completeness problem and notes the obstruction
to generic algebra-morphism reductions. Nothing in the present argument
solves the stronger perfect-quantum-completeness halting reduction.

The proved boundary concerns full-space authentication of fixed group-word
ports while retaining an honest nontrivial controlled projection. It does
not exclude changing the ports themselves to non-word matrix readouts,
decoding on a proper model-dependent corner, using a genuinely different
source encoding, or accepting a controlled positive loss. No soundness
claim for any of those alternatives was obtained.

Independent review on 2026-09-20: the hardness-audit sibling checked
(A)--(D), including projections q that mix control branches and the
complex-conjugated third control. The review passed. This is a mathematical
review, not a computation or formal verification.
