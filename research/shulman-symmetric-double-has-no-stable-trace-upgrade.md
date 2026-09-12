---
rg: 2
id: shulman-symmetric-double-has-no-stable-trace-upgrade
kind: claim
title: Shulman's 2026 symmetric-double theorem has no Hilbert-Schmidt-stable trace upgrade
artifacts:
  - research/artifacts/shulman-2603-13564-verified.md
  - notes/FALSE_SHULMAN_TRACE_AUDIT.md
distinct_from:
  shulman-amalgam-mf-criterion: that imports the actual operator-norm MF theorems for full amalgamated free products; this excludes a stronger trace statement incorrectly attributed to the same paper
  symmetric-double-weak-mf: that applies Theorem 10 to obtain weak MF of a group double; this says that theorem does not select or preserve a hyperlinear trace
  hyperlinear-trace-not-mf-trace: that separates two trace classes using this repository's constructed group; this is only a source-scope correction for a proposed symmetric-double shortcut
---

The current primary source arXiv:2603.13564v2 contains no theorem asserting
that, when `A` is Hilbert--Schmidt stable, every hyperlinear trace on
`A *_C A` is MF.

Its Theorem 10 instead says:

```text
A separable MF, C<=A  ==>  A *_C A is MF                (SHT1)
```

in the operator-norm C-star-algebra sense.  Its Theorem 20 is the compatible
norm-corona embedding criterion for a general amalgam.  Neither statement
controls a prescribed trace on the double.

The nearby genuine trace theorem is Shulman,
*Homotopy lifting, asymptotic homomorphisms, and traces*, arXiv:2508.00125,
Corollary 35: hyperlinear traces on `B` are MF when `B` is homotopy dominated
by a Hilbert--Schmidt-stable algebra.  For `B=A *_C A`, the fold and one vertex
inclusion show that `A` is dominated by `B`, the opposite direction from the
hypothesis needed to transfer trace lifting from `A` to `B`.  No homotopy from
the fold retraction on the double to its identity is supplied.

Therefore the claimed stable-double trace criterion is not an established
theorem.  Theorem 10 proves algebra MF permanence only; a hyperlinear or MF
trace which sees a specified fold-radical element remains additional data.

