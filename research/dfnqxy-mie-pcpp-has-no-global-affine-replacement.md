---
rg: 2
id: dfnqxy-mie-pcpp-has-no-global-affine-replacement
kind: claim
title: DFNQXY uses Mie's circuit-table PCPP, while a global affine replacement is impossible
distinct_from:
  dfnqxy-pcpp-contract-allows-nonlinear-proof-views: that modifies an arbitrary admissible PCPP by appending one nonlinear proof bit; this identifies the PCPP actually inherited by the published construction and proves that the stronger global-linear replacement cannot work for all source verifiers.
  hadamard-pcpp-reflects-affine-unsafety: that propagates one affine-unsafe positive strategy support through every PCPP; this is a verifier-level obstruction to an ambient-affine proof encoder with affine local checks, independent of which perfect strategy is selected.
  affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain: that assumes only a source-support-specific affine section on an accepted affine hull; this proves why one cannot replace that local hypothesis by a global linear-PCPP theorem.
---

**ESTABLISHED SOURCE AUDIT AND NO-GO.**  The constant-query PCPP in the
Hadamard answer reduction of Dong--Fu--Natarajan--Qin--Xu--Yao (DFNQXY) is
the time-efficient PCPP of Mie, not a PCPP carrying a published global
linearity theorem.  Moreover, no PCPP with an ambient-affine proof encoder
and affine local acceptance predicates can replace it uniformly in
DFNQXY's answer-reduction theorem.

## Which PCPP the published construction uses

Section 6.3 of arXiv:2312.04360v3 states the parameter block

```text
r(m)=log T(m)+O(log log T(m)),
q(m)=O(1),
t(n,K)=poly(n,log K,log T(n+K)).                         (MIE1)
```

The section imports its modular answer reduction from Natarajan--Wright.
In Section 17.2 and Theorem 17.5 of arXiv:1904.05870v3, Natarajan--Wright
attribute exactly `(MIE1)` to Mie, Theorem 1.  Fu--Mastel--Zhang then make
the provenance explicit in Appendix A of arXiv:2503.04517v2: the
Hadamard-code answer reduction of DFNQXY "relies on the PCPP constructed in
[Mie09]."

The same appendix audits the honest Mie proof.  Its starting BS-type proof
is a low-degree encoding of the complete evaluation table of a circuit on
the input and witness.  It is then oracularized, passed through repeated
gap amplification (dummy copies, graph powering, and assignment testers),
and finally reduced to a binary alphabet.  This gives an efficiently
computable perfect proof, but none of those primary statements asserts that
the resulting proof is affine in the implicit input on the relevant
positive supports.

There is a genuine distinction from the known *linear* PCPP special case.
In Theorem 6.1 and its proof in arXiv:1801.03821v2, Natarajan--Vidick extract
from Ben-Sasson--Goldreich--Harsha--Sudan--Vadhan a proof whose bits and
checks are linear only when the tested property is an AND of linear
constraints.  DFNQXY's language

```text
L_Enc(x_0,x_1) = {(Had(y_0),Had(y_1)):
                   C_(x_0,x_1)(y_0,y_1)=1}              (MIE2)
```

has an arbitrary polynomial-time Boolean predicate `C`; the cited linear
special case therefore does not apply to `(MIE2)`.

## A global affine replacement cannot handle arbitrary source verifiers

Here is an exact obstruction, separate from the absence of a citation.
Call a binary PCPP **ambient-affine** if it comes with an affine map

```text
P:F_2^K -> F_2^m                                         (MIE3)
```

and, for every random seed, its queried acceptance relation is an affine
subset of the queried input-and-proof bits.  Assume perfect completeness,
proximity threshold `gamma<=1/4`, and soundness `s<1`.

Take one explicit input whose valid raw answer pairs are precisely

```text
(e_1,e_1), (e_2,e_2), (e_3,e_3) in F_2^3 x F_2^3.       (MIE4)
```

Put `z_i=(Had(e_i),Had(e_i))`.  Perfect completeness accepts
`(z_i,P(z_i))` for every random seed.  Coordinate restriction is linear,
and an odd xor preserves affine relations.  Hence every seed also accepts

```text
xor_(i=1)^3 (z_i,P(z_i))
  = (z_*,P(z_*)),
z_*=(Had(111),Had(111)).                                 (MIE5)
```

The equality for the proof uses ambient affineness: an affine map preserves
odd xors.  But `z_*` is at relative Hamming distance `1/2` from every word
in `(MIE4)`: in each of its two Hadamard blocks, distinct messages have
relative distance `1/2`.  Thus `z_*` is farther than `gamma` from
`L_Enc`, while `(MIE5)` is accepted with probability one, contradicting
soundness `s<1`.

Consequently the missing affine-seam theorem cannot be obtained by simply
declaring the DFNQXY PCPP globally linear, or by swapping in a universal
Hadamard/linear PCPP with affine checks.  The still-viable target is strictly
more local:

```text
for the particular HALT strategy and each affine-safe positive support A,
choose a coherent perfect-proof section A -> F_2^m that is affine on A.
                                                               (MIE6)
```

The no-go does not refute `(MIE6)`: its three-word witness deliberately has
an invalid odd xor and hence is not an affine-safe support.  It does show
that a proof of `(MIE6)` must exploit the selected HALT supports and the
specific accepted affine hulls; no known global linear-PCPP theorem supplies
it automatically.

Primary sources:

- Dong--Fu--Natarajan--Qin--Xu--Yao,
  arXiv:2312.04360v3, Sections 6.3--6.4.
- Natarajan--Wright, arXiv:1904.05870v3, Section 17.2 and Theorem 17.5.
- Fu--Mastel--Zhang, arXiv:2503.04517v2, Appendix A.
- Natarajan--Vidick, arXiv:1801.03821v2, Section 6.1, especially Theorem 6.1.

