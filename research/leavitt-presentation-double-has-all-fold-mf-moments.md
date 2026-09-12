---
rg: 2
id: leavitt-presentation-double-has-all-fold-mf-moments
kind: claim
title: The Leavitt presentation double has symmetric MF traces with every fold moment
distinct_from:
  shulman-presentation-double-has-a-faithful-fold-trace-model: that realizes the folded value `tau(w)=1`; this realizes every value in `[0,1]`, including the canonical one-word value zero, while retaining canonical vertex marginals and swap symmetry.
  hall-reflection-realizes-rank-one-restriction-instability: that has vanishing normalized-HS fold mass; this tensor-amplifies its exact finite-window edge models after adding a canonical finite-quotient vertex block.
  dimension-defect-controlled-mf-hyperlinear: that requires a dimension-versus-defect rate before functorial amplification of approximate multiplication; here every current kernel-window relation is exact, so arbitrary tensor powers cost no edge defect.
  leavitt-positive-rank-intertwiner-retention: that asks for a compressed adjoint sector satisfying IR1--IR3; this controls the ordinary trace of one group fold word and does not supply such a sector.
  leavitt-hall-tensor-mf-trace-quotients-are-sofic: that identifies the resulting GNS group quotients as sofic; this constructs and computes the MF traces before asking what approximation class their quotients have.
---

**ESTABLISHED FOLD-MOMENT SIMPLEX.** Fix `f_0 in F\K` and

```text
P=F *_K F,                 w=i_0(f_0)i_1(f_0)^(-1).
```

For every `t in [0,1]`, the full group algebra `C*(P)` has an MF trace
`tau_t` such that

```text
tau_t C*(i_0)=tau_F=tau_t C*(i_1),
tau_t swap=tau_t,
tau_t(w)=t.                                               (AFM1)
```

Moreover `tau_t` can be induced by an asymptotically isometric MF model of
the whole algebra.  For `t<1`,

```text
tau_t((u_w-1)^*(u_w-1))=2-2t>0,                         (AFM2)
```

so these traces lie outside the closed convex hull of exact
finite-dimensional characters by
`leavitt-presentation-double-fd-radical-is-fold-kernel`.  At `t=0`, one
fold word has its canonical group-trace moment even though only the two
vertex marginals and that one mixed moment have been prescribed.

The construction starts from the exact Hall reflection on each finite
kernel window, appends a finite-quotient regular block which makes the
vertex character uniformly less than one on the current nonidentity
window, and takes a tensor power `m_n`.  If the total one-particle dimension
is `D_n`, then

```text
tr(w_n)=(1-4/D_n)^(m_n).                                (AFM3)
```

Choosing `m_n/D_n->-log(t)/4` gives `(AFM1)` for `0<t<1`;
`m_n/D_n->infinity` gives `t=0`, while `m_n->infinity` and
`m_n/D_n->0` gives `t=1`.  Current edge relations remain exact under every
tensor power, so there is no dimension-versus-defect gate.

This answers the first ordinary mixed-moment **realization** question:
canonical marginals, exact swap symmetry, norm faithfulness and any chosen
value of one marked fold word can all be imposed without constructing an IR
sector.  These data therefore do not identify the remaining condition.  The
scalar appearing in IR is instead a **compressed adjoint** moment on the
same almost-reducing sector, identified separately in
`ir-survival-is-one-compressed-adjoint-moment`; it is not `tau_t(w)`.

Moreover these particular traces cannot supply a sofic-radical collision:
`leavitt-hall-tensor-mf-trace-quotients-are-sofic` proves that every one of
their GNS group quotients is sofic, including when `t<1` and the fold word
survives.

DERIVATION
all-fold-mf-moments-from-tensored-hall-reflections
