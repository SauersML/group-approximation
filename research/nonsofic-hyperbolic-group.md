---
rg: 2
id: nonsofic-hyperbolic-group
kind: claim
title: A nonsofic hyperbolic group — the second nonsoficity mechanism
distinct_from:
  hyperlinear-nonsofic-group: that claim demands a group that is hyperlinear yet not sofic; this one demands a nonsofic group that is hyperbolic, and says nothing about hyperlinearity
  wreath-not-sofic: that is nonsoficity of this program's own (T)-compression wreath candidate; this is a different group produced by a different mechanism
  non-residually-finite-hyperbolic-group: that is strictly weaker; nonsoficity implies failure of residual finiteness, but no converse is known in the hyperbolic class.
root: true
---

Produce a hyperbolic group that is not sofic. This would in particular
produce a non-residually-finite hyperbolic group, since every residually
finite group is sofic. The implication is one-way: a non-residually-finite
hyperbolic group could still be sofic. The weaker Gromov problem is carried
separately at [[non-residually-finite-hyperbolic-group]].

## Why this sits in this program

`notes/OBSTRUCTIONS.md` §5 records the caution that Pestov's Question 3.4
"may be inaccessible until a *second* nonsoficity mechanism exists", because
every known nonsofic group came from the same (T)-compression pattern that
the eight no-gos attack.  As of 2026-08 that caution is still literally
true: the unconditional nonsofic groups (OpenAI's `L_(F_2)(1,2)^x`,
Kun--Thom's wreath products, Fournier-Facio's torsion-free example) are all
one-sided-compression + property (T) + a non-LEF commuting subgroup.

This node names the only *different* mechanism found in the 2023--2026
literature.  It matters here for one reason: the eight dead architectures
are attacks on the (T)-compression pattern, and none of them evidently
applies to a group whose nonsoficity comes from local-testability failure
instead.  A nonsofic hyperbolic group would therefore be a genuinely fresh
Q3.4 candidate rather than another instance of the blocked pattern.

Conservatively modeled as OPEN and explicitly conjectural: no source claims
such a group exists.  The one route recorded below is conditional on an
unproved probabilistic estimate.

**2026-09-11 precision (read from the PDF).** Chapman--Peled Theorem 1.1
assumes only `h_1(Y,Sym) = ω(n^(-2-η))`, not a constant lower bound. The exact
record is `nonsofic-hyperbolic-via-cheeger-threshold` with premise
`random-complex-cocycle-cheeger-beats-triangle-count`.

The soficity-free half of their proof is now the established
`finite-quotient-caps-cocycle-cheeger-constant`: any finite quotient of `π_1(Y)`
that detects a missing triangle caps the Cheeger constant at `O(1/|Y(2)|)`. So the
premise is a statement about the finite quotients of random Kazhdan hyperbolic
groups. It already forces a non-residually-finite hyperbolic group
(`non-rf-hyperbolic-via-cheeger-threshold`), and residual finiteness of those
groups would refute it (`random-complex-cheeger-capped-by-triangle-count`).

## Attempts

- **Forcing a nontrivial block representation on the Leavitt cover: dead.**
  - The cover `hyperbolic-kazhdan-cover-of-leavitt-unit-group` gives
    `1 -> N -> G -> R^x -> 1` with `N` Kazhdan.
  - By `kazhdan-quotient-sofic-iff-injective-block-representation`, each sofic
    approximation of `G` induces `tau_sigma : R^x -> S_U` on the expander
    blocks of `N`.
  - By `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`, that
    representation is trivial for **every** approximation, because `R^x` is
    simple and nonsofic.
  - So showing that some approximation moves the blocks nontrivially is
    impossible. That route to nonsoficity of `G` is closed by a theorem, not
    left as a gap. A contradiction has to come from inside single blocks: see
    `relative-normalization-modulo-kazhdan-kernel`.
- **Bounded inner realizers: dead.**
  - On blocks, an element outside `N` is not within `eps < 1/2` of a kernel
    element from a fixed finite set times an exact block centralizer, except on
    negligible mass (`bounded-blockwise-inner-realizers-fail-off-kernel`).
  - So blockwise realizers must leave every finite set along `U`. The genuine
    realizers of the finite quotients
    (`leavitt-cover-finite-quotients-split-over-the-kernel`) do not transfer
    with bounded size.
  - What remains is the unbounded-cocycle conjugacy hinge recorded on
    `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`.
