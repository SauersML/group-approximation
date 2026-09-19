# The exact normalized-HS gate in the Higman four-cycle

## What the vertex theorem really gives

The presentation

```text
<g_0,g_1,g_2,g_3 |
 g_i g_(i+1) g_i^-1=g_(i+1)^2>
```

contains four overlapping copies of `BS(1,2)`.  Levit--Vigdorovich,
arXiv:2206.02268, Corollary D(3), makes each copy normalized-HS stable in the
same dimension.

Applying the theorem separately does not produce a Higman representation.
It produces four exact BS representations with two corrected occurrences of
each cyclic generator.  If the original relator defect is `delta`, the two
occurrences differ by at most `2 omega_BS(delta)`.

This is not merely a weakness of the proof.  It is an equivalent
reformulation.  If exact edge pairs have occurrence mismatch `eta`, choosing
one occurrence of every generator produces a Higman tuple with relator defect
at most `3 eta`.  Thus

```text
Higman microstates
    <== quantitatively ==>
exact BS packets with four vanishing occurrence seams.
```

## Why cyclic compatibility is the whole problem

Higman's group has no nontrivial finite quotient.  Every finite-dimensional
unitary representation is therefore trivial by Malcev residual finiteness of
finitely generated linear groups.  Hence a dimension-free theorem saying
that all four seams can be repaired simultaneously is exactly normalized-HS
stability of Higman's group.  Together with any microstate keeping one
generator visible, it would prove nonhyperlinearity; without such a
microstate, it is already the marked-collapse problem.

Conversely, an exact BS-packet cycle with seams tending to zero and one
conjugator bounded away from identity is itself an explicit marked Higman
microstate.  There is no intermediate compatibility lemma left after the
edge exactification.

## Relation to the existing countermodels

`split-higman-cycle-has-haar-marginals-and-maximal-role-gap` has exact
periodic BS packets but seams tending to `sqrt(2)`, so it lies outside the
minimal gate.  `one-product-holonomy-does-not-sew-four-bs-clocks` shows that
one unlocalized product word can vanish while those seams remain large.

The new reduction identifies what an actual countermodel must improve: all
four operator seams, not their marginal spectra or their product, must tend
to zero.  Producing that cycle is equivalent to producing the marked
microstate, so it must not be described as a consequence of amenability or
BS stability.

Primary source: https://arxiv.org/abs/2206.02268

