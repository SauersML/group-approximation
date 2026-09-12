---
rg: 2
id: depthwise-canonical-kleene-needs-no-uniform-runtime-gap
kind: claim
title: Reverse Kleene accepts depthwise canonical soundness with arbitrary runtime loss
distinct_from:
  kleene-self-destroying-microstate-lemma: that forward search needs one open matrix window with a positive soundness gap; this uses proof enumeration in the reverse orientation and takes the microstate limit before depth.
  halt-now-certificate-area-still-needs-a-crossing-envelope: that proves candidate-dependent forward windows need a crossing envelope; this bypass never asks a matrix candidate to cross its own runtime-dependent window.
  fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity: that treats one already fixed finitely presented group; this is a machine-indexed compiler interface and applies Kleene self-reference before effective Higman embedding.
  canonical-profile-kleene-higman: that assumes qualitative canonical-profile collapse; this gives a concrete sufficient family of nonuniform quantitative estimates for that hypothesis.
---

ESTABLISHED.  Suppose a total computable compiler sends a machine index `e`
to a finite alphabet `S_e`, a uniformly recursively enumerable relator stream
`R_e`, and a marked word `w_e`.  Put `Gamma_e=<S_e|R_e>`.  Assume

```text
e halts  =>  w_e!=1 in Gamma_e.                              (DCK1)
```

On a nonhalting input, allow the compiled simulation to have completely
nonuniform runtime loss.  It is enough that there are numbers `b_(e,N)->0`
and, for each `N`, a finite relator prefix `R_(e,N)`, a finite canonical trace
window `F_(e,N)`, and a finite constant `C_(e,N)` such that every matrix tuple
`U` satisfies

```text
 ||w_e(U)-I||_2^2
 <= b_(e,N)+C_(e,N)(def_(R_(e,N))(U)+sep_(F_(e,N))(U)).       (DCK2)
```

Neither `C_(e,N)` nor the rate `b_(e,N)->0` must be uniform in `e`, computable,
or bounded as a function of simulated runtime.  Under `(DCK1)--(DCK2)` one can
effectively construct a finitely presented nonhyperlinear group.

The order of quantifiers is load-bearing.  On a canonical-profile microstate
sequence for one fixed `Gamma_e`, first fix `N` and let the matrix index tend
to infinity.  The finite relator and trace errors in `(DCK2)` vanish, leaving
`limsup ||w_e(U_k)-I||_2^2<=b_(e,N)`.  Only afterward let `N->infinity`.
Thus NONHALT gives qualitative canonical-profile collapse, and reverse
Kleene applies.

This is the rigorous bypass for a recursively self-aware construction whose
late challenges have terrible finite proof area.  What it does **not** do is
make forward enumeration of rational microstates sound: if the machine halts
because a candidate enters a window of width about `1/C_(e,N)`, hyperlinearity
need not supply a candidate crossing that moving window.  The construction
must instead establish `(DCK2)` for every fixed depth in the final fixed group
and use proof enumeration as its self-reference trigger.

The remaining mathematical compiler target is consequently weaker than an
HS-PCP in one precise direction and stronger in another:

```text
arbitrary depth/runtime loss is allowed,
but every fixed-depth estimate must act on the same marked carrier
and must hold on canonical-profile matrix tuples.                     (DCK3)
```

Static challenge libraries and moving dimension-selected tests do not supply
`(DCK3)`; a self-similar boundary return or orthogonal checksum can.
