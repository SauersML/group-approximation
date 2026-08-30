---
rg: 2
id: stw22-tracefree-fibre-gap-ideals-force-trace-continuity
kind: claim
title: Trace-free, and in particular stable, norm-fibre gaps force central-bundle trace continuity
distinct_from:
  stw22-norm-fibre-gap-is-the-trace-obstruction: that theorem phrases the exact obstruction using restrictions of traces from the norm fibre; the present theorem identifies it intrinsically as bounded traces on the gap ideal and gives stability as a strictly weaker sufficient condition than vanishing of the gap.
  stw01-stable-algebras-are-bounded-quasitrace-invisible: that theorem is an intrinsic vanishing result for stable algebras; the present theorem applies it to the norm-fibre gap and transfers the conclusion to every trace on the ambient central bundle.
artifacts:
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
---

In the setting of `stw22-norm-fibre-gap-is-the-trace-obstruction`, put

```text
B_x=M/J_x,                    I_x=K_x/J_x triangleleft B_x.
```

Then the condition that every tracial state on `B_x` annihilates `I_x` is
equivalent to the intrinsic condition

```text
I_x has no nonzero bounded positive trace.                 (TF_x)
```

Consequently every tracial state on `M` is uniquely of the form `mu o E` as
soon as `(TF_x)` holds for every `x`.  In particular, it is enough that every
gap ideal `K_x/J_x` be stable.  This is strictly weaker than `J_x=K_x`: for a
one-point base,

```text
M=K(ell^2)^~,       J=0,       K=K(ell^2),       M/K=C
```

has a nonzero stable gap, but its only tracial state is the quotient
character and hence annihilates that gap.
