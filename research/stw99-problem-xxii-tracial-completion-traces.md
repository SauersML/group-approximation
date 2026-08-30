---
rg: 2
id: stw99-problem-xxii-tracial-completion-traces
kind: claim
title: Every trace on a uniform tracial completion is uniformly 2-norm continuous (STW Problem XXII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
---

**Problem XXII of Schafhauser--Tikuisis--White, *Nuclear C*-algebras:
99 problems*, arXiv:2506.10902v2.**  Let `A` be a C*-algebra with nonempty
compact trace space `T(A)`, and let

```text
M=completion of A in ||a||_(2,T(A))=sup_(tau in T(A)) tau(a*a)^(1/2).
```

Must every tracial state on `M` be continuous for the uniform `2`-norm?
Equivalently, does restriction identify

```text
T(A)=T(M)?
```

The problem remains open in general, including for nuclear `A`.  The source
records positive answers for finite-dimensional trace simplices, for
completions with complemented partitions of unity, and in further Bauer
cases.

For a tracially continuous `C(X)`-bundle with factor `2`-norm fibres, the
exact elementary obstruction is now isolated by
`stw22-norm-fibre-gap-is-the-trace-obstruction`.  A trace supported at
`x in X` factors automatically through the C*-norm fibre, but need not
factor through the smaller `2`-norm fibre.  Thus fibrewise uniqueness of the
II_1 trace does not by itself solve the problem.

The gap need not vanish.  The intrinsic sufficient condition established in
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` is that every
`K_x/J_x` carry no nonzero bounded positive trace.  Stability of all the gap
ideals is a concrete special case, strictly weaker than `J_x=K_x`.

The equality shortcut already fails in an actual zero-dimensional nuclear
Bauer completion.  The computation
`stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap` exhibits a
nonzero `K_x/J_x` and proves directly that it is bounded-trace-free by
orthogonal replication of spectral cuts.  It also isolates the remaining
general difficulty as neighbourhood-wise continuous selection rather than
pointwise finite-factor comparison.

## Attempts

For a Bauer-style central bundle, disintegrate an extreme trace over the
center.  This only proves that the trace factors through the norm fibre
`M/J_x`.  The canonical finite-factor fibre is instead `M/K_x`, with
`J_x` contained in `K_x`.  Fibrewise uniqueness therefore applies only
after one proves that every trace on `M/J_x` kills `K_x/J_x`.  The linked
norm-fibre-gap theorem makes this obstruction exact.  Equality `J_x=K_x`
holds for norm-continuous trivial fields, but uniform `2`-norm completeness
alone does not supply it, so the direct disintegration argument stops
precisely at this ideal gap.
