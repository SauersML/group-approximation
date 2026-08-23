---
rg: 2
id: three-actor-grades-support-an-exact-hadamard-cell
kind: claim
title: Three actor grades support an exact Hadamard cell under cyclic aperiodicity
distinct_from:
  cyclic-aperiodicity-collapses-two-actor-grade-unitaries: that proves two grades collapse to one homogeneous grade; this gives an exact genuinely mixed three-grade unitary under the same hypothesis.
  finite-pmp-actions-have-barren-haar-linear-compilers: that encodes a finite classical partition action and remains a normalizer construction; this unitary does not normalize the abelian base and implements coherent two-level mixing.
  manzoor-irs-generators-cannot-be-single-actor-grade: that obstructs homogeneous images of the canonical IRS generators; this supplies a local nonhomogeneous Fourier cell but does not yet match the Manzoor moments or multiplication law.
---

Let a torsion-free group `H` act cyclic-aperiodically by automorphisms on a
nonzero countable discrete abelian group `A`, as in
`cyclic-aperiodicity-collapses-two-actor-grade-unitaries`, and put

```text
M=L^infinity(K) rtimes H,              K=dual(A).
```

Fix `t!=e`. There is a projection `p in L^infinity(K)` with

```text
0<tau(p)<1/2,       p alpha_t(p)=0.                    (THC1)
```

Put

```text
q=alpha_t(p),       r=1-p-q,       v=q U_t.
```

Then `v` is a partial isometry from `p` to `q`, and

```text
W = r + 2^(-1/2)(p-q+v+v^*)                           (THC2)
```

is a self-adjoint unitary. Its actor Fourier expansion is

```text
W = (r+2^(-1/2)(p-q)) U_e
    +2^(-1/2)q U_t
    +2^(-1/2)p U_(t^(-1)).                            (THC3)
```

All three coefficients are nonzero. Moreover `W` does not normalize the
base `L^infinity(K)`: explicitly,

```text
W p W^* = (p+q+v+v^*)/2.                              (THC4)
```

The nonidentity Fourier coefficients in `(THC4)` are nonzero. Thus `W` is
neither homogeneous nor a finite measurable partition cocycle. On the
corner `p+q`, `(THC2)` is exactly the two-dimensional Hadamard reflection.

In fact the construction gives a full exact qubit cell. The four operators

```text
e_11=p,       e_22=q,       e_21=v,       e_12=v^*    (THC5)
```

are matrix units. Hence every scalar matrix

```text
C=[[a,b],[c,d]] in U(2)
```

has the exact three-grade realization

```text
W_C=r+a p+d q+c v+b v^*,                              (THC6)
```

which is unitary in `M`. If `b,c` are nonzero, its Fourier support is exactly
`{e,t,t^(-1)}`. Thus three grades contain an exact copy of `M_2(C)` on a
positive-trace carrier, not just one exceptional reflection.

Consequently cyclic aperiodicity gives a sharp two-grade theorem and no
finite-Fourier-support exclusion beyond it. Three grades already permit
genuine matrix mixing, not merely piecewise selection of actor elements.
This is a constructive local cell for the algebraic compact-action route,
but it does not by itself embed the Manzoor relation algebra: a successful
envelope must still assemble such cells so that all source-generator
products and IRS traces are preserved.

`countable-three-grade-cells-generate-the-whole-crossed-product` identifies
the exact scope of that assembly: after the base is included, countably many
cells recover every chosen actor unitary and hence exactly the crossed product
of the actor directions. Thus local three-grade syntax is no longer a gate,
but the global Manzoor inclusion remains precisely the algebraic-envelope
problem.
