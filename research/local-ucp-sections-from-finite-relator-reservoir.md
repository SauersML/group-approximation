---
rg: 2
id: local-ucp-sections-from-finite-relator-reservoir
kind: route
title: Bound the relator depth of the packetwise corrections and let RFD compactness produce the exact section
target: triangle-relator-extension-admits-local-ucp-sections
requires:
  - finite-relator-reservoir-repairs-every-fd-packet
  - finite-reservoir-compactness-lifts-ucp-repairs
  - virtually-free-full-algebras-are-rfd
  - triangle-colimit-llp-reduces-to-relator-local-splitting
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

Let `Lambda`, its triangle presentation, `G_0`, `A=C^*(G_0)`, `q:A->>
C^*(Lambda)` and `I_N=ker q` be the instance supplied by
`finite-relator-reservoir-repairs-every-fd-packet`, which is by construction an
instance of the kind the target quantifies over: the presentation is a triangle
of finite groups satisfying (H1)-(H2), and `Lambda` is one of the infinite
finitely presented simple Kazhdan lattices of
`simple-kazhdan-kac-moody-lattices-exist`.

**Step 1 (the ambient algebra is RFD).**
`triangle-colimit-llp-reduces-to-relator-local-splitting` (TC1) proves `G_0` is
finitely generated virtually free, so `virtually-free-full-algebras-are-rfd`
applies and `A` is RFD.  This is the only place a literature input enters the
route, and it enters as a named requirement rather than inside a proof.

**Step 2 (apply the compactness lemma).**  Fix a finite-dimensional operator
system `E subset C^*(Lambda)`.  The reservoir claim supplies a unital
self-adjoint linear section `t:E->A` and a finite symmetric `W subset G_0` such
that, for every finite packet `R` of finite-dimensional representations of `A`,
some linear `d_R:E->L_W` makes every `rho o (t+d_R)` ucp.  The space `L_W` of
`(RR1)` is finite-dimensional and contained in `I_N`, so the hypotheses `(FR1)`
and `(FR2)` of `finite-reservoir-compactness-lifts-ucp-repairs` hold verbatim
with `I=I_N`, `L=L_W`.  Its conclusion `(FR3)` gives a single ucp
`s:E->A` with `q s = incl`.

**Step 3 (conclude).**  `E` was an arbitrary finite-dimensional operator system
of `C^*(Lambda)`, so the extension `0 -> I_N -> C^*(G_0) -> C^*(Lambda) -> 0`
is locally ucp-split.  That is the statement of the target, which by (TC3)-(TC4)
of the equivalence node is exactly LLP of `C^*(Lambda)`.

**This is a reduction, not a restatement -- checked deliberately.**  The
recorded trap is a single-prerequisite route whose prerequisite is equivalent
to its target.  Here the implication is strictly one-way and the two statements
are about different objects:

- The prerequisite can fail while the target holds.  A ucp section `s` has
  `s-t` valued in the **closed** ideal `I_N`; nothing forces those values into
  any finite span of relator words `u_a(u_n-1)u_b`.  So local splitting does
  not return the reservoir property, and the reduction is not invertible.
- The prerequisite does not mention the target's distinguishing object.  It
  never quantifies over quotients, ucp maps into quotients, or lifting; it is a
  statement about finite packets of finite-dimensional representations and a
  word-depth bound in a finitely generated ideal.
- The recovery step is genuine, not bookkeeping: it is the compactness argument
  of `finite-reservoir-compactness-lifts-ucp-repairs`, which consumes RFD twice
  and would be false without the finite-dimensionality of the reservoir.

**What this route does not do.**  It does not decide the target: its leaf
`finite-relator-reservoir-repairs-every-fd-packet` is open, and by
`fd-representation-packets-never-obstruct-ucp-sections` no finite-dimensional
computation can decide that leaf either.  It also does not touch the *global*
splitting side (the LP), which remains expected to fail at these lattices per
`compact-hyperbolic-km-lattices-fail-lp`; nothing in Steps 1-3 produces a
section defined on all of `C^*(Lambda)`, and the window no-go
`position-window-ucp-sections-collapse-to-folner-vectors` explains why the
obvious globalization of the finite-face section
`explicit-finite-face-ucp-section-is-edge-equivariant` cannot exist.  Prior to
this route the target had no live routes at all.
