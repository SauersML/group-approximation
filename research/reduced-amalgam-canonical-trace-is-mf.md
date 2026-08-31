---
rg: 2
id: reduced-amalgam-canonical-trace-is-mf
kind: claim
title: The canonical trace on the Kun-Thom group double amalgam is an MF trace
distinct_from:
  shulman-symmetric-double-has-no-stable-trace-upgrade: that is the negative source-scope correction, recording that arXiv:2603.13564v2 contains no theorem promoting Hilbert--Schmidt stability of a vertex algebra to MF-ness of a prescribed trace on the double; this is the positive statement that one specific trace on one specific double is MF, i.e. the hole that correction leaves open.
  symmetric-double-weak-mf: that is the established algebra-level conclusion, weak MF of every symmetric double of a countable residually finite group, and it selects no trace; this asks for the strictly finer datum of a matricial trace converging to the canonical group trace.
  shulman-amalgam-mf-criterion: that imports Shulman's Theorem 20 corona-embedding criterion for general amalgams as a literature fact; this is an open question about the trace on one instance, not an import.
  hyperlinear-trace-not-mf-trace: that separates the two trace classes on this repository's constructed group; this asks whether the two coincide on the Kun--Thom double, and is not settled by that separation, which concerns a different group.
  kt-double-mixed-word-trace-selection: that asks only for normalized-Hilbert--Schmidt models with the canonical mixed reduced-word traces; this asks for the strictly stronger operator-norm MF approximation of the canonical trace.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
  - research/artifacts/shulman-2603-13564-verified.md
---

Let `Gamma < G` be a Kun--Thom infranormal Kazhdan pair -- for instance the
explicit Theorem E pair `Gamma = EL_r(F_q[x_1..x_d])`,
`G = EL_r(F_q[x^(+-1)]) rtimes SL_d(Z)` with `r,d >= 3` -- and let

```text
D = G *_Gamma G,        C*(D) = C*(G) *_(C*(Gamma)) C*(G)
```

be the group double and its full amalgam.  Let `tau` be the canonical group
trace on `C*(D)`.

**Claim.**  `tau` is an **MF trace**: there are `d_n -> infinity` and unital
completely positive maps `phi_n : C*(D) -> M_(d_n)(C)` which are
asymptotically multiplicative and asymptotically isometric in **operator
norm**, with

```text
tr_(d_n) o phi_n -> tau   pointwise.                             (RAT1)
```

The operator-norm requirement is what makes this stronger than
hyperlinearity of `D`, and is what makes it a statement Shulman's machinery
can plausibly reach; see the route
`hyperlinear-nonsofic-from-mf-amalgam-trace` for the payoff.

## Attempts

1. **Shulman Theorem 10 directly.**  `A` separable MF and `C <= A` give
   `A *_C A` MF, which is exactly the algebra `C*(D)` here, and is already
   recorded at group level as `symmetric-double-weak-mf`.  It supplies norm
   microstates for the algebra but selects **no trace**: the limit of
   `tr_(d_n) o phi_n` along an arbitrary MF embedding need not be `tau`.
   Dies at trace selection.  `shulman-symmetric-double-has-no-stable-trace-upgrade`
   records that the paper contains no theorem closing this step.

2. **Shulman arXiv:2508.00125, Corollary 35.**  Hyperlinear traces on `B` are
   MF when `B` is homotopy dominated by a Hilbert--Schmidt-stable algebra.
   For `B = A *_C A` the fold and one vertex inclusion show `A` is dominated
   by `B` -- the opposite direction from the hypothesis needed.  Dies on the
   missing homotopy from the fold retraction to the identity of the double.

3. **Weaken the target to "`tau` is a hyperlinear trace".**  Recorded and
   rejected, not parked: `tau` hyperlinear is literally `L(D)` Connes
   embeddable, i.e. `D` hyperlinear, so that version of the statement is a
   restatement of the target of the payoff route and buys nothing.  The
   operator-norm demand in `(RAT1)` is exactly what keeps this a genuine
   strengthening with a machine attached.

4. **Why no formal upgrade exists from (1).**  Norm data does not pin a
   trace at any finite stage.  A rank-one modification

```text
U_n = diag(-1, 1, ..., 1) in U(n),
||U_n - I|| = 2,        ||U_n - I||_2 = 2 / sqrt(n) -> 0,
```

   is maximal in operator norm and invisible in normalized Hilbert--Schmidt
   norm.  So the two topologies separate on exactly the perturbations a
   trace cannot see, and no soft argument turns an MF embedding of the
   algebra into control of `tau`.  This is the reason the hole is real
   rather than bookkeeping.

5. **Exact weaker trace target.**
   `kt-double-hyperlinear-iff-mixed-word-trace-selection` identifies the
   merely hyperlinear endpoint exactly: besides asymptotic vertex models,
   agreement on `Gamma`, and canonical vertex marginals, one must make every
   nontrivial reduced alternating word asymptotically traceless.  The open
   claim `kt-double-mixed-word-trace-selection` asks for exactly those data.
   The present MF-trace claim implies it, but not conversely.  This is a
   finite-window unpacking of the gap, not a reduction of its logical
   strength.
