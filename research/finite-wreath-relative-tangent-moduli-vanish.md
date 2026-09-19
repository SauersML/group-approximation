---
rg: 2
id: finite-wreath-relative-tangent-moduli-vanish
kind: claim
title: Relative lamp-base tangent moduli vanish around every finite wreath packet
distinct_from:
  finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge: that counts exact unitary-equivalence classes and identifies the lamp eigenbasis orbit globally; this computes the local linearized kernel, including the relative fiber over a fixed actor representation, and gives an explicit dimension-free contracting homotopy.
  coset-wreath-microstates-carry-excess-entropy: that asks for nonlinear approximate moduli at positive precision; this proves no such moduli arise infinitesimally near an exact finite wreath packet with its full multiplication table.
  iwahori-uniform-infinitesimal-rigidity: that asks for uniform first-cohomology control for growing arithmetic amalgam representations; this uses elementary averaging for a finite wreath group and controls the relative actor-fixed tangent exactly.
---

Let `H=A rtimes Q` be a finite wreath packet and let
`rho:H->U(d)` be any exact representation.  Put

```text
M=u(d),              alpha_g(X)=rho(g)Xrho(g)^*.
```

A linearized deformation is a one-cocycle

```text
b(gh)=b(g)+alpha_g(b(h)).                               (FWT1)
```

Every such cocycle is a global-conjugacy tangent.  With

```text
X=(1/|H|) sum_(h in H)b(h),                             (FWT2)
```

averaging `(FWT1)` over `h` gives

```text
b(g)=X-alpha_g(X).                                      (FWT3)
```

Therefore `H^1(H,M)=0`.

For the regular amplification `rho=k lambda_H`, `d=k|H|`, the real
dimension of the raw cocycle space is

```text
dim_R Z^1(H,M)
 =d^2-dim_R M^H
 =d^2-|H|k^2
 =d^2(1-|H|^(-1)).                                     (FWT4)
```

This is macroscopic, but `(FWT3)` identifies it exactly with the tangent to
the global `U(d)` orbit.  Its quotient dimension is zero.

The relative fiber over a fixed actor packet is equally rigid.  If
`b(q)=0` for all `q in Q`, then `(FWT3)` implies `X in M^Q=rho(Q)'`.  Thus

```text
Z^1(H,Q;M)={delta X:X in M^Q},
Z^1(H,Q;M)/(actor-fixing conjugacies)=0.                (FWT5)
```

There is a dimension- and group-size-independent approximate linear form.
Suppose

```text
max_(g,h)||b(gh)-b(g)-alpha_g b(h)||_2 <= epsilon,
max_(q in Q)||b(q)||_2 <= eta.                          (FWT6)
```

The average `X` from `(FWT2)` satisfies

```text
max_g ||b(g)-(X-alpha_gX)||_2 <= epsilon.               (FWT7)
```

Average `X` over `Q` to obtain `Y in M^Q`.  Then

```text
||X-Y||_2 <= eta+epsilon,
max_g ||b(g)-(Y-alpha_gY)||_2 <= 3epsilon+2eta.         (FWT8)
```

Trace and Bernoulli-moment linearizations only cut down this cocycle space,
so they cannot create quotient tangent directions.

Consequently the congruence-commutant ratio has no local tangent entropy near
an exact finite wreath packet: its apparent `c d^2` kernel is precisely the
absorbing conjugacy orbit, even when the actor tuple is held fixed.  Any
positive entropy must live in models uniformly far from every exact finite
wreath table, or exploit deterioration when a fixed presentation is expanded
to a growing multiplication table.  It cannot be detected by a local
cohomology calculation around regular finite packets.

The presentation-level boundary is
`wreath-ball-area-controls-only-true-group-cells`.
True radius-`R` group cells have defect at most `Dehn_G(3R)delta`, and every
vanishing-defect sequence admits a diagonal `R->infinity` with vanishing true
table defect.  But a congruence quotient multiplication cell may be a
nontrivial moving kernel word in the original group, so the presentation
does not control the full finite table needed by `(FWT8)`.
