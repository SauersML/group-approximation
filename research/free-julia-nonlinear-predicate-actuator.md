---
rg: 2
id: free-julia-nonlinear-predicate-actuator
kind: claim
title: Charge nonlinear predicate mass on the free Julia Gram source
distinct_from:
  common-partial-isometry-swap-game-compiler: that uses a central D8 spin sector and separately selected context types; this has no packet selector or partial-isometry requirement because the nontrivial free commutator word itself supplies an arbitrary common Gram contraction of canonical mass one quarter.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for a full compatible algebraic BCS atlas in one canonical corner; this asks only for state-dependent forbidden mass on one off-diagonal Gram block.
  context-word-julia-rows-only-cut-affine-supports: that proves ordinary character-word returns cannot be the actuator requested here.
---

**OPEN.**  Fix the finite BCS game `B` supplied by
`oracularizable-tracial-nonru-game-exists`, with perfect tracial value and
finite-dimensional value at most `theta<1`.

Construct a finite ordinary-group presentation containing involutions `z,j`
and one involution `d_x` for every BCS variable, with

```text
[d_x,z]=1,
[d_x,d_y]=1                 when x,y share a context.  (FJPA1)
```

In the `z` grading put

```text
G=P_+jP_-,       A_x=P_+d_xP_+,       B_x=P_-d_xP_-.
```

The presentation may contain `d_x j d_x j=1`; by
`free-julia-grading-carries-one-gram-at-canonical-quarter-mass` these rows
pay all occurrence-consistency terms `||A_xG-GB_x||_2^2`.

The missing actuator is a fixed finite ordinary-word menu with both of the
following properties.

1. **Exact completeness.**  The perfect tracial model of `B`, in standard
   left--right form and with a nonzero Gram contraction, extends to an exact
   representation of the presentation in which `zjzj!=1`.
2. **Finite-matrix predicate payment.**  After fixed-relation rounding, its
   word energy `E_pred^word` obeys

   ```text
   sum_c mu_c ||F_c(A)G||_2^2
      <= C E_pred^word+o(1),                           (FJPA2)
   ```

   with `C` independent of matrix dimension.  Here `F_c(A)` is the forbidden
   joint spectral projection computed from the commuting positive blocks
   `(A_x)_(x in U_c)`.

No common-source, source-mass, polar-cut, or context-alignment hypothesis is
missing from this interface: the literal pair `z,j` supplies all of them.
The remaining operation is exactly nonlinear predicate-to-word payment on
that source.  By `context-word-julia-rows-only-cut-affine-supports`, a finite
list of returns by ordinary words in the commuting context involutions cannot
satisfy `(FJPA2)` for a nonaffine predicate.  The actuator must use a
genuinely non-character packet or a matrix-only/canonical-only return.

## Attempts

1. **Use more context-word return rows.**  Their common zero set on the Gram
   source is affine by `context-word-julia-rows-only-cut-affine-supports`, so
   they retain the `R_*` ghost whenever they retain all seven honest points.
2. **Put the nonlinear truth table in one finite role packet.**
   `finite-role-packet-cannot-supply-hybrid-predicate-row` shows that every
   universally oriented scalar word is again a selector character; the
   induced ghost sector survives.
3. **Mix selector sectors by a finite Weyl frame.**  If both the frame lower
   bound and the mixing rows are algebraic, then
   `algebraic-selector-mixing-frame-collapses-forbidden-sector` kills the
   forbidden projection already in the full group C-star algebra, destroying
   the phase-safe exact packet rather than producing a matrix-only gap.
4. **Give each context a private Julia source.**  This loses the one-Gram
   hypothesis: orthogonal direct sums can put each local row on a different
   source, exactly the escape in
   `pairwise-cross-grams-do-not-supply-one-game-state`.
5. **Use several noncommuting returns but prove one universal SOS bound.**
   `regular-free-julia-atom-mass-is-uniform-or-affine` evaluates any such
   tracially functorial bound in the regular representation.  The free-Julia
   source is then either uniform on all context assignments or supported on
   one affine halfspace.  For `R_*` the latter is precisely a maximal Fano
   cap, so a universal multi-return identity merely reinstates the
   deterministic-parity gate.

The deferred attack is therefore a non-character predicate return whose
positive payment is specific to canonical finite matrix models while its
zero-energy equations remain compatible with one exact tracial Julia
source.
