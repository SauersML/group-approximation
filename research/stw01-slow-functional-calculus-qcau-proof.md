---
rg: 2
id: stw01-slow-functional-calculus-qcau-proof
kind: route
title: Convexify successive functional-calculus tails and use each quasitrace's spectral measure
target: stw01-sigma-unital-cuts-have-quasitracial-idempotence
requires: []
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

The zero ideal is immediate.  Otherwise choose a strictly positive
contraction `h in I` and put

```text
u_m=f_m(h),                 f_m(t)=min(1,mt).
```

Then `(u_m)` is an increasing positive-contractive approximate unit for
`I`.  Every bounded `2`-quasitrace `tau` is linear on the abelian unital
algebra `C*(1,h)`.  Its restriction is therefore integration against a
finite positive measure `mu_tau` on `spectrum(h)`.  Since

```text
(f_m(t)-f_m(t)^2)^2 -> 0
```

at every spectral point (including `t=0`) and the functions are uniformly
bounded, dominated convergence gives `(SFC1)` for `e_m=u_m`.  Notice that
the sequence is independent of `tau`, so this argument works simultaneously
for all bounded quasitraces; no uniformity over their norms is asserted or
needed.

Now suppose `A` is separable.  Fix increasing finite sets with dense union
in the unit ball of `A`.  The standard quasicentral approximate-unit
convexification lemma says that, for every finite `F subset A`, every
`epsilon>0`, and every tail index `M`, a finite convex combination of
`{u_m:m>=M}` has commutators of norm less than `epsilon` with every member
of `F`.  (The tail form is the usual lemma applied after discarding the
first `M-1` terms.)

Apply the lemma recursively.  If `e_{n-1}` is a convex combination whose
largest index is `K_{n-1}`, choose `M_n>K_{n-1}` and choose `e_n` as a finite
convex combination of `u_m`, `m>=M_n`, with commutators less than `2^{-n}`
on the first `n` elements of the dense set.  All these elements are
functions of `h`, and monotonicity of `(u_m)` gives

```text
e_{n-1} <= u_(K_{n-1}) <= u_(M_n) <= e_n.
```

Thus `(e_n)` is increasing.  Convex combinations of a sufficiently late
tail approximate every element of `I` uniformly on the left and right, so
it remains an approximate unit.  Density turns the finite-set estimates
into norm quasicentrality for every `a in A`.

Write `e_n=g_n(h)`.  Every summand defining `g_n` comes from the tail
starting at `M_n`, hence `g_n(0)=0` and

```text
g_n(t) >= f_(M_n)(t) -> 1                 (t>0).
```

Therefore `(g_n-g_n^2)^2` converges pointwise to zero and is uniformly
bounded.  Applying dominated convergence to each `mu_tau` proves `(SFC1)`
for the convexified sequence as well.  Finally positivity gives

```text
tau([e_n,a]*[e_n,a])
   <= tau(1) ||[e_n,a]||^2 -> 0,
```

which is `(SFC2)`.

**Continuity boundary.**  The spectral argument uses only the finite measure
attached to one bounded quasitrace at a time.  It does not exchange a limit
with a supremum over quasitraces.  The convexification uses separability of
the ambient algebra, not merely sigma-unitality of the ideal.
