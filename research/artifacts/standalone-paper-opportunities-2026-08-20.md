# Strong standalone paper opportunities from original Cairn work

Date: 2026-08-20

This deliberately uses a high bar.  It omits published inputs, useful but
small lemmas, perspective pieces, and compiler components that do not yet
support a good standalone paper.  Novelty still requires a dedicated
MathSciNet/arXiv audit before submission.

## 1. Complete: coprime power-pair and phase-graph HNN residual finiteness

The strongest complete original package is a family of constructive
residual-finiteness theorems for HNN extensions of finite products of free
groups.  Its sharp endpoint is
`coprime-power-pair-phase-hnn-is-residually-finite`.

Let `F=F(x_1,...,x_r)` and `phi_k(x_i)=x_i^k`.  If `gcd(m,n)=1`, then

```text
E_(m,n)=<F_x times F_y,t |
 t(a,1)t^(-1)=(phi_m(a),phi_n(a)), a in F>
```

is residually finite.  The structural calculation underneath is valid for
arbitrary gcd.  If `d=gcd(|m|,|n|)` and `p` does not divide `mn`, then in the
free pro-`p` completion

```text
Graph(phi_n phi_m^(-1)) intersect (F times F)
 ={(phi_(m/d)(a),phi_(n/d)(a)):a in F}.                 (PAPER-HNN1)
```

This is `power-pair-pro-p-graph-has-gcd-saturation`.  It follows by comparing
ordinary cyclic-syllable normal forms in the embedded abstract free product
`* Z_p`.  In the coprime case the right side is exactly the intended edge.
Open characteristic subgroups then give one finite `p`-group quotient that
preserves every forbidden Britton pinch, and the word maps nontrivially to an
HNN extension of a finite group.

The surrounding original package supplies natural closure operations and a
sharp screening principle:

- `partial-phase-graph-hnn-is-residually-finite`;
- `phase-coordinate-switch-hnn-is-residually-finite`;
- `free-factor-phase-graph-hnn-is-residually-finite`;
- `hnn-mark-collapse-requires-profinite-edge-incompatibility`;
- `power-pair-phase-hnn-has-finite-heisenberg-mark-models`.

Together these make a coherent specialist group-theory paper rather than an
isolated exercise: fixed faithful-coordinate graphs, switches between free
factors, and the first nonprimitive coprime power-pair embeddings all admit
explicit compatible finite quotients.  Formula `(PAPER-HNN1)` also identifies
the exact obstruction when `d>1`: the standard pro-`p` quotients see the
larger gcd saturation, so the coprime proof is sharp.

**Assessment:** good standalone paper candidate now.  Its likely impact is
specialist rather than landmark.  The novelty case must be made against the
large literature on residual finiteness of HNN extensions, emphasizing these
explicit graph-subgroup classes, the gcd-saturation formula, and the
constructive simultaneous pinch separation.

## 2. Potentially major, incomplete: A8/Leavitt four-holonomy rigidity

The only current package with a plausible path to a genuinely high-impact
standalone result is the A8/Leavitt route.  The completed original core is:

- `atlas-a4-packet-four-rectangle-normal-form` reduces thirty A4 pair-cube
  constraints to four noncommutative rectangle holonomies after tree gauge;
- `atlas-a4-gl5-packet-collision-screen` exhausts all `9,999,360` relative
  positions of the standard A8 chart in `GL5(F2)`;
- exactly `202` positions satisfy all thirty packet constraints;
- collision `19243` is nonidentity on every one;
- the survivors have intersection orders `20160`, `1344`, and `168`, exactly
  matching the chart/parabolic/core subgroup ladder.

That is striking certified computational rigidity, but it does not yet meet
the high-impact standalone bar by itself.  The missing theorem is the fixed
four-unitary trace estimate

```text
S^2 + S x_12 + x_12^2 < 3/128,                          (PAPER-A8-1)
```

recorded as `atlas-a4-root-energy-ellipse-ceiling`.  The opposite collision
wall is already established.  The improved threshold uses the kernel relation
itself and is four times weaker than the older centrality-only target after
squaring.  A proof of `(PAPER-A8-1)` would therefore turn
the finite rigidity package into the decisive operator-algebraic collapse and
close the proposed non-hyperlinear-group route.

**Assessment:** potentially major paper if the ellipse is proved; not yet a
complete standalone result at that level.  Until then, the exact `GL5(F2)`
screen should be maintained as reproducible evidence and a guide to the
four-holonomy inequality, not oversold as the final theorem.

## Recommendation

Write the phase-graph HNN paper after a focused novelty audit.  Keep the
A8/Leavitt package in theorem-completion mode; proving the four-holonomy
ellipse is the only currently visible spin-off that would clearly outrank the
specialist HNN paper in impact.
