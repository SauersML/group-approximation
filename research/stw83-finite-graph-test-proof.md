---
rg: 2
id: stw83-finite-graph-test-proof
kind: route
title: Realize every finite generator packet inside a finite graph algebra
target: stw83-finite-graphs-are-complete-test
requires: []
---

Fix finite edge and vertex sets `F subset E^1` and `V subset E^0`, and
put

```text
D=V union s(F) union r(F).
```

In `C*(E)` let `Q_e=s_e s_e^*` for `e in F` and

```text
Q_v=p_v-sum_(e in F, s(e)=v) s_e s_e^*
```

for `v in D`, omitting zero `Q_v`.  These projections are pairwise
orthogonal.

Make a finite graph `G_(F,V)` with one vertex for each nonzero `Q_e,Q_v`;
each `Q_v` is a sink.  From vertex `e`, put an edge to vertex `f`
whenever `r(e)=s(f)`, represented by `s_e Q_f`, and an edge to the
residual vertex `r(e)` whenever `Q_(r(e))!=0`, represented by
`s_e Q_(r(e))`.  The decomposition

```text
p_(r(e))=sum_(f in F, s(f)=r(e)) Q_f+Q_(r(e))
```

gives the Cuntz--Krieger equality at `Q_e`.  The ambient gauge action has
degree one on the constructed edges and every retained vertex projection is
nonzero, so gauge-invariant uniqueness identifies `C*(G_(F,V))` with

```text
B_(F,V)=C*(s_e:e in F; p_v:v in D).
```

This also handles infinite emitters: omitted range pieces are absorbed into
the residual projection instead of imposing a false finite-emitter equality.

The family `B_(F,V)` is directed under enlarging `(F,V)`, and its union
contains every graph generator, hence is dense in `C*(E)`.  Nuclear
dimension at most one is a uniform local approximation property and passes
to this directed inductive limit.  Therefore the finite-graph bound implies
the bound for arbitrary `E`.
