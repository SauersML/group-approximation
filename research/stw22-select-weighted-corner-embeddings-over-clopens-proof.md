---
rg: 2
id: stw22-select-weighted-corner-embeddings-over-clopens-proof
kind: route
title: Select square-root-weighted embeddings into fixed factor corners by clopen refinement
target: stw22-zero-dimensional-trivial-field-trace-continuity
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-zero-dimensional-weighted-selection-audit-2026-08-30.md
---

Put `R=pi_tau(U)''`.  We first record the weighted selection lemma used in
the proof.

**Weighted corner-selection lemma.**  Let `e` be a projection in the finite
factor `R`, and fix `s<tau(e)`.  If `Z` is compact, metrizable, and
zero-dimensional and

```text
d:Z -> R_+
```

is an operator-norm-bounded `2`-norm-continuous map satisfying
`tau(supp(d(z)))<=s`, then there is a `2`-norm-continuous map `w:Z->R`
such that

```text
w(z)^*w(z)=d(z),             w(z)w(z)^*<=||d|| e.        (WCS)
```

Here the second inequality means that the range support of `w(z)` is below
`e`; after normalizing `d`, it is the displayed operator inequality.

We give the selection argument because continuity of `supp(d(z))` is neither
assumed nor true.  For a positive contraction `a` with
`tau(supp(a))<=s`, the set

```text
F(a)={w:w^*w=a, supp(ww^*)<=e}
```

is nonempty: embed `supp(a)` into `e` and multiply the implementing partial
isometry by `a^(1/2)`.  The relation has the following local lifting
property in `2`-norm:

```text
a_n -> a and w in F(a)
  implies there are w_n in F(a_n) with w_n -> w.         (WCL)
```

To verify `(WCL)`, choose a spectral threshold `eta>0` for `a` so that the
`a`-mass below `2 eta` is as small as desired and the spectral band around
`eta` has arbitrarily small trace.  Standard spectral-projection
perturbation in a finite factor aligns the parts of `a_n` and `a` above the
threshold by a partial isometry converging in `2`-norm.  Transport `w` on
that high part.  The remaining support of `a_n` embeds into the complement
of the transported range inside `e`: the strict slack
`s<tau(e)` supplies the needed dimension.  Its contribution to the
weighted operator has squared `2`-norm equal to the trace of the low
spectral part of `a_n`, and hence tends to zero with `eta`.  First choose
`eta`, then let `n` grow.  This proves `(WCL)`.  Notice that the unweighted
support embeddings need not converge; multiplication by `a_n^(1/2)` is
essential.

Now choose finite clopen partitions of `Z`, successively refining and with
mesh tending to zero for the map `d`.  On the first partition choose one
element of `F(d(z))` at a sample point of each atom.  On each refinement,
use `(WCL)` to choose the new sample values arbitrarily close to their
parents.  Taking the meshes sufficiently small and the successive errors
summable gives locally constant maps `w_n` which are uniformly Cauchy in
`2`-norm, while

```text
w_n^*w_n=d_n,       supp(w_nw_n^*)<=e
```

for locally constant `d_n -> d` in uniform `2`-norm.  The common
operator-norm bound makes multiplication continuous in `2`-norm.  Passing
to the limit proves `(WCS)`.

We apply the lemma to a fibre gap.  Let `a in K_x` be a positive
contraction, fix `epsilon>0`, and put

```text
c=(a-epsilon)_+.
```

For an arbitrary integer `m`, `2`-norm continuity at `x` and Chebyshev give
a clopen neighbourhood `V` of `x` such that

```text
sup_(t in V) tau(supp(c(t)))
 <= epsilon^(-2) sup_(t in V)||a(t)||_2^2 < 1/(2m).      (WCS1)

```

The complement of `V` disappears modulo `J_x`, so replace `c` by `1_V c`.
Choose pairwise orthogonal projections `e_1,...,e_m in R` with
`tau(e_j)=1/m`.  Apply the weighted selection lemma to `c|V`, with
`s=1/(2m)`, separately for each `e_j`.  Extend the resulting maps by zero
off `V`.  This gives `v_1,...,v_m in K_x` satisfying `(ZDO)`; their ranges
are orthogonal because they lie in the fixed orthogonal corners.

Let `sigma` be a bounded positive trace on `K_x/J_x`.  From `(ZDO)`,

```text
m sigma(c)=sigma(sum_(j=1)^m v_jv_j^*) <= ||sigma||.
```

Since `m` is arbitrary, `sigma(c)=0`.  Finally
`||a-c||<=epsilon`, so `epsilon -> 0` gives `sigma(a)=0`.  Thus every fibre
gap is bounded-trace-free, and the abstract fibre-gap criterion proves the
description of all traces on `M`.
