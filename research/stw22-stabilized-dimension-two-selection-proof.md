---
rg: 2
id: stw22-stabilized-dimension-two-selection-proof
kind: route
title: Combine all-factor weighted loop fillings with stabilized two-dimensional selection
target: stw22-dim2-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-diffuse-weighted-loop-extension-audit-2026-08-30.md
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
---

Use the stabilization, closedness, lower-semicontinuity, and operator-ball
recovery established in
`stw22-stabilize-l2-bundle-and-select-weighted-copies-proof`.  Thus, for a
fixed positive contraction `a in M`, a fixed replication number `m`, and

```text
m tau_x(supp(a_x))<=1-gamma        (x in K),
```

the exact weighted-copy sets `F_x(a)` are nonempty closed subsets of one
complete Hilbert space, and `x |-> F_x(a)` is lower semicontinuous.  The
quantitative correction estimate proving this is uniform over all finite
factor fibres.

Countable generation puts every fibre `L^2(M_x)` inside `ell^2`; hence each
factor fibre has separable predual.  The theorem
`stw22-all-finite-factor-weighted-copy-uniform-loop-fillings` therefore
applies to every value.  For fixed `m`, the maximum tuple metric and the
Hilbert-sum metric are uniformly bi-Lipschitz, so the values form a uniformly
equi-locally-`1`-connected family in the common ambient Hilbert space.  To
spell out the ambient-centre point in the maximum tuple metric, fix
`epsilon>0` and choose

```text
delta <= epsilon/2,
2sqrt(m) delta <= rho_(Hilbert-sum)(epsilon/2).
```

If a loop lies in `F_x(a) intersect B_max(c,delta)`, choose one point `v`
on it.  The loop lies in the Hilbert-sum ball
`B_2(v,2sqrt(m)delta)`.  The fibre-centred theorem fills it in
`B_2(v,epsilon/2)`, hence in
`B_max(c,epsilon/2+delta) subset B_max(c,epsilon)`.  The bi-Lipschitz
constants depend only on the already fixed `m`, not on `x`.  The values
are path connected by the principal-logarithm argument in the
one-dimensional route, and they are simply connected by the global
spectral-band filling in
`stw22-unitary-lifted-spectral-band-recursion-proof` (apply its relative
band recursion directly with constant complement `1`).

Michael's finite-dimensional selection theorem in degree `n=1` now gives a
continuous selection of `F_x(a)` over every paracompact base of covering
dimension at most two.  Stabilization identifies it with an `L^2` section;
the fibrewise operator-ball identity `(OB)` in the one-dimensional route
puts its components back in `M_1`.  Thus every globally slack positive
contraction has exact global orthogonal weighted copies.

Finally repeat Step 3 of
`stw22-stabilize-l2-bundle-and-select-weighted-copies-proof`.  Given a
positive gap element at `x_0`, cut it spectrally and multiply by a central
function supported where its fibre support trace is below `1/(2m)`.  The
selection just obtained gives `m` exact copies.  Any bounded positive trace
on the gap is at most its norm divided by `m`; letting `m` tend to infinity
and then removing the spectral cut makes it vanish.  The exact fibre-gap
criterion gives the asserted trace formula and uniform `2`-continuity.
