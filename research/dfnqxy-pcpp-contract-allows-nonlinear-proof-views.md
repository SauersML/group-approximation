---
rg: 2
id: dfnqxy-pcpp-contract-allows-nonlinear-proof-views
kind: claim
title: The DFNQXY PCPP contract allows a forced nonlinear proof view over an affine source
distinct_from:
  dfnqxy-answer-reduction-does-not-preserve-affine-safe-support: that starts with an affine-unsafe three-point source support and shows the final PCPP cannot repair it; this starts with a four-point affine source support and makes the permitted PCPP proof oracle introduce the first affine-unsafe view.
  hadamard-pcpp-reflects-affine-unsafety: that proves every proof selection reflects an earlier odd-xor violation; this proves the stated PCPP contract can itself introduce an odd-xor violation when no earlier one exists.
  uniform-linear-pcpp-tensorizes-to-amitsur-hs: that assumes a linear PCPP and derives an operator consequence; this proves that linearity is an additional hypothesis absent from Definition 6.6 and Theorem 6.9.
---

**ESTABLISHED CONTRACT COUNTEREXAMPLE.**  Perfect completeness, proximity
soundness, and constant query complexity in Definition 6.6 of
Dong--Fu--Natarajan--Qin--Xu--Yao do not imply that perfectly accepting
PCPP proofs can be chosen with affine-safe local views, even when the
positive source relation and support are affine.

Start with any PCPP verifier `V` for a pair language whose implicit input
has two distinguished coordinates `z_1,z_2`.  Form `V_AND` by appending one
proof bit `b`, running `V`, and also querying

```text
z_1, z_2, b       and requiring       b=z_1 z_2.        (NAP1)
```

For a true input, append `b=z_1 z_2` to any perfect proof.  For an input
far from the language, the new acceptance probability is no larger than
that of `V`.  Randomness is unchanged, and query and verification
complexity increase by only three and one fixed Boolean gate.  Thus
`V_AND` satisfies exactly the PCPP hypotheses used in Definition 6.8 and
Theorem 6.9.

Now take the one-question-pair source verifier whose accepted answer pairs
are

```text
{(y,y): y in F_2^2}.                                   (NAP2)
```

Use the real symmetric EPR strategy given by the four equal diagonal
projections, so all four pairs have positive mass.  Both the accepted
relation and its positive support are affine.  In the two Hadamard words,
choose `z_1,z_2` to be the coordinates indexed by the two standard basis
vectors; on the honest encoding they are exactly the two bits of `y`.

For the three positive outcomes `y=00,01,10`, the forced proof bits in
`(NAP1)` are all zero.  Their odd xor has visible coordinates `11` and
proof bit zero, but `(NAP1)` requires proof bit one at `11`.  Hence the
positive honest response support on every augmented `Verify` view contains
three accepted points whose odd xor is rejected.  It is affine-unsafe even
though `(NAP2)` was affine-safe.

The actual completeness paragraph of Theorem 6.9 only says that the prover
"compute[s] a PCPP proof" separately for its answers.  Definition 6.6 gives
an existential perfect proof for each accepted input and imposes no joint
linearity, canonicity, or affine-section condition on this choice.  Therefore
the published answer-reduction theorem cannot certify the required support
property.  A successful use at the Culf--Mastel seam must choose and prove an
additional source-specific PCPP property, for example:

```text
on the positive affine source support, the perfect proof word is affine
in the source answer (or, more generally, every sampled accepted view is
affine-safe).                                            (NAP3)
```

This claim does not say that every permissible PCPP fails `(NAP3)`; it
shows that `(NAP3)` is not a consequence of the exact PCPP contract used in
the cited construction.

