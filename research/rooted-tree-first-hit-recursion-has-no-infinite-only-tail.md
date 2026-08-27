---
rg: 2
id: rooted-tree-first-hit-recursion-has-no-infinite-only-tail
kind: claim
title: A rooted-tree first-hit recursion has no nontrivial infinite-only tail
distinct_from:
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that gives finite affine models of every finite clone pattern; this proves that the putative residual element on the unique never-hit ray is already the identity.
  word-recursion-cannot-amplify-sublinear-summands: that keeps an external reducing block invisible; this is an exact faithfulness/continuity obstruction inside the recursive tree action itself.
  bounded-hs-loss-kills-static-heavy-tail-library: that dilutes countably many positive-mass carriers; this rules out putting the marked group element only on the zero-mass limiting ray.
---

Let `X` be a finite alphabet with at least two letters and distinguished
letter `0`, and let a group
act faithfully by level-preserving automorphisms of the rooted tree `X^*`.
Suppose `g` has trivial root permutation and wreath recursion

```text
g=(g,1,...,1),                                         (RTF1)
```

where the first section is at `0`.  Then

```text
g=1.                                                   (RTF2)
```

More generally, if

```text
g=(g,h_x)_(x!=0)                                      (RTF3)
```

and every `h_x` is trivial in the presented group, then `g` is trivial.

Indeed, a finite word either consists entirely of zeroes, in which case
`(RTF1)` recursively fixes every prefix, or has a first nonzero letter, after
which its section is the identity.  Thus `g` fixes every finite tree vertex;
faithfulness gives `(RTF2)`.

There is an identical Cantor/full-group formulation.  A homeomorphism of
`X^omega` which is the identity off the singleton `0^omega` is the identity:
the moved-point set of a nonidentity homeomorphism is a nonempty open set,
whereas a Cantor singleton has empty interior.

Therefore the tempting checksum

```text
recurse on the persistent child;
put a relator syndrome on every first-hit exit;
leave one nontrivial mark on the never-hit infinite ray                 (RTF4)
```

cannot work algebraically.  If the exit syndrome words are genuine
relators, the purported tail mark is trivial.  If an exit word is
nontrivial, the recursion aggregates a real group element rather than a
finite-dimensional-only failure; it still needs a separate argument forcing
that exit to fail in matrices.

One related firewall is immediate.  Every faithful level-preserving rooted
tree group is residually finite: the kernels of its actions on the finite
levels have trivial intersection.  Hence a pure automaton-group checksum is
hyperlinear.  A non-hyperlinear construction must use an additional
non-level-preserving prefix group, a proper-corner/multiplicity actuator, or
a matrix-only decoding step.
