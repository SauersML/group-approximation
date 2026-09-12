---
rg: 2
id: bass-serre-algebraic-projections-are-stably-vertex-induced
kind: claim
title: Every algebraic projection over a finite graph of finite groups is stably induced from finite vertex packets
distinct_from:
  finite-subgroup-hecke-literals-cannot-block-escape: that traps one compressed literal qgq by its canonical trace; this classifies an arbitrary finite linear-combination projection, including one whose support crosses many Bass--Serre double cosets.
  finite-graph-packet-compression-wandering-no-go: that separates one wandering group word from a fixed vertex-corner reflection by regular support; this is a projective-module classification and permits extensive reduced-word cancellation inside the idempotent.
  britton-support-traps-dense-free-phase-chord: that treats exact conjugation of one dense finite-support element across an HNN letter; this treats projections without any conjugation equation.
  finite-support-central-corners-are-finite-normal-twisted-sectors: that gives an unstabilized scalar decomposition for central projections using finite normal subgroups; this needs no centrality but concludes only rectangular stable equivalence to a sum of vertex packets.
---

Let `Gamma` be the fundamental group of a **finite** graph of **finite**
groups, put `R=C[Gamma]`, and let

```text
p=p*=p^2 in M_n(R).                                      (BSP1)
```

There are finitely generated projective modules `P_v` over the finite-
dimensional vertex algebras `C[Gamma_v]` such that

```text
R^n p  isomorphic to
directSum_v R tensor_(C[Gamma_v]) P_v.                  (BSP2)
```

After representing each `P_v` by a self-adjoint projection
`e_v in M_(m_v)(C[Gamma_v])` and putting `e=directSum_v e_v`, there is a
rectangular partial isometry over a matrix amplification of `L(Gamma)` with

```text
V*V=e,          VV*=p.                                  (BSP3)
```

Thus every finite-support algebraic projection is stably Murray--von Neumann
equivalent to a finite direct sum of finite vertex packets.  This remains
true even when the displayed formula for `p` has support in many Bass--Serre
double cosets.  In particular, for a free product `Gamma=H*K`, every
projection over `C[H*K]` is stably assembled from projectives over `C[H]`
and `C[K]`; a long reduced-word expression cannot create a new stable
projective carrier.

The statement applies without centrality to a Hecke corner.  If
`q in C[H]` is any projection and

```text
p in M_n(qRq),       p=p*=p^2,                           (BSP4)
```

then `R^n p` is a projective left `R`-module and hence has
`(BSP2)--(BSP3)`.
Consequently no arbitrary finite linear combination in a noncentral
finite-subgroup corner escapes the finite vertex packets **as an individual
stable Murray--von Neumann class**.

The canonical trace is retained exactly under `(BSP3)`.  If a rank-one
projection is chosen in the Fourier block belonging to
`pi in Irr(Gamma_v)`, its trace in `L(Gamma)` is

```text
dim(pi)/|Gamma_v|.                                       (BSP5)
```

Hence the unnormalised matrix trace of `p` is a finite sum of these vertex-
packet weights.  This gives a trace-level Plancherel check on the module
classification and rules out a hidden irrational capacity in an algebraic
Bass--Serre projection.

## Exact scope of the trap

This is not an unstabilized support theorem.  It does **not** assert that
`p` itself lies in a vertex group algebra, that it is unitarily conjugate to
one vertex projection inside the scalar corner `qL(Gamma)q`, or that the
partial isometry in `(BSP3)` has finite group-ring support.  It also does not
simultaneously straighten several BCS projections: different projections
can require incompatible rectangular equivalences, and their relative
holonomy is not recorded by their individual projective classes.

Therefore `(BSP3)` sharply fences the proposed *single escaping projection*
as a source of a new stable capacity, but it is not by itself a no-go for a
compatible signed-Hecke atlas.  Such an atlas would have to store its
non-Connes-embeddable information entirely in the relative position of
vertex-induced packets, not in any one algebraic projection.

The algebraic input is Proposition 2.12 of Pablo Sanchez-Peralta,
*Universal Localizations, Atiyah Conjectures and Graphs of Groups*, GAFA 35
(2025), 842--876, which combines Bergman's coproduct theorem with Dicks's
HNN theorem: over a finite graph of rings with semisimple edge rings, every
projective module is a direct sum of modules induced from projective vertex-
ring modules.  Complex group algebras of finite edge groups are semisimple,
and the graph of group rings is `C[Gamma]`.
