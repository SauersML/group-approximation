---
rg: 2
id: affine-ghosts-survive-recoverable-tracial-dilations
kind: claim
title: Affine ghosts survive every support-surjective recoverable tracial dilation
distinct_from:
  affine-auxiliary-control-flow-barrier: that projects an affine solution set and shows its visible relation is affine; this allows arbitrary nonlinear enlarged predicates and uses only an affine decoder back to the supplied perfect support.
  dynamic-fano-cap-incidence-labels-are-a-reversible-dilation: that treats one specific Fano incidence refinement; this is the general support-hull invariant covering amplification, central sums, tagged tensor products, and polarization.
  tracial-cap-menus-are-central-core-partitions: that classifies tracial postselection inside one von Neumann algebra; this proves why every recoverable dilation before postselection retains the original affine ghost.
---

**ESTABLISHED DILATION INVARIANT.**  Let

```text
S subseteq R subseteq F_2^k
```

be the local support and allowed relation of one context in a perfect trace.
Suppose a modified context has support and allowed relation

```text
S_tilde subseteq R_tilde subseteq F_2^m
```

and there is an affine decoder

```text
pi:F_2^m -> F_2^k,
pi(S_tilde)=S,                 pi(R_tilde) subseteq R.   (AGD1)
```

Then

```text
Aff(S_tilde) subseteq R_tilde
       ==> Aff(S) subseteq R.                           (AGD2)
```

Equivalently, if the original support has a forbidden affine ghost, every
support-surjective recoverable dilation still has a forbidden affine ghost.
The statement is contextwise and therefore applies simultaneously to every
context of a BCS.

This disposes of the standard trace modifications.

1. **Matrix amplification** has `S_tilde=S` and `pi=id`.
2. **Finite central/direct sums** replace supports by unions.  If one
   summand has unsafe support `S_0`, then
   `Aff(S_0) subseteq Aff(union S_j)`, so mixing cannot dilute its ghost.
3. **Classical ancillas and polarization** retain the visible assignment as
   an affine marginal, hence satisfy `(AGD1)`.  Splitting an atom into tagged
   subatoms changes its multiplicity but not its decoded affine hull.
4. **Tagged diagonal tensoring** has local assignments `(u,t)=(s+t,t)` and
   affine decoder `pi(u,t)=u+t=s`.  Thus tensoring while retaining enough of
   the auxiliary packet to recover the original non-CE algebra cannot repair
   the support.

An untagged tensor/convolution can evade `(AGD1)` only by discarding the
decoder.  Then the original contextual algebra is no longer an expected or
recoverable subalgebra, so non-Connes-embeddability of the output does not
follow from that of the input.  It is a new source construction, not an
amplification of the fixed witness.

The only ordinary operation on a supplied perfect tracial model which can
actually shrink `S` is postselection to a summand.  By
`tracial-cap-menus-are-central-core-partitions`, a normalized compression is
tracial on the generated von Neumann algebra only when its support is
central.  Hence the sole live within-model possibility is:

```text
find a non-CE central/factor summand whose local supports are affine-safe.
                                                               (AGD3)
```

Neither amplification, convex mixing, tensor tagging, nor reversible
polarization manufactures such a summand.  A noncentral local projection may
prune assignments, but its compressed functional is not a trace and cannot
feed the perfect-kernel quotient.

Thus the locally separating perfect-kernel route has a sharper remaining
gate: choose a support-pruned non-CE central component of the fixed BCS trace,
or build a genuinely global nonrecoverable compiler and prove its output
non-CE afresh.  By `locally-affine-support-bcs-is-exactly-the-lcs-boundary`,
success of either option is already the perfect non-CE LCS endpoint.

DERIVATION
affine-ghost-recoverable-dilation-proof

