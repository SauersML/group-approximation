---
rg: 2
id: haar-root-parabolic-bessel-proof
kind: route
title: Apply Bessel to the conjugacy orbit and use Leavitt self-doubling of one-sided ideals
target: haar-root-character-vanishes-off-parabolic-action-kernel
requires: []
---

We first use a general character lemma.  Let `A<=G`, let `tau` be a
character with `tau|_A=delta_1`, and let `g` normalize `A`.  If the
`A`-conjugacy orbit of `g` is infinite, choose `a_1,a_2,... in A` so that

```text
h_i=a_i g a_i^(-1)
```

are distinct.  Since `g` normalizes `A`, `h_i^(-1)h_j` belongs to `A` and
is nonidentity for `i!=j`.  Hence the GNS vectors `u_(h_i)` are orthonormal.
They all have inner product `tau(g)` with the trace vector, by conjugation
invariance.  Bessel gives

```text
M |tau(g)|^2 <= 1
```

for every `M`, so `tau(g)=0`.  When `A` is abelian, as the root modules below
are, replacing `g` by `vg`, `v in A`, does not change the conjugation action
on `A`; this proves the same conclusion on the corresponding
semidirect-product coset.

For a last-column root module, a nontrivial elementary shear has difference
image projecting onto `rL` for some `0!=r in L`.  For a first-row root
module the corresponding projection is `Lr`.  These one-sided ideals cannot
be finite.  Indeed, for a right ideal `I`,

```text
I -> I directSum I,       x |-> (x s_0,x s_1),
(y_0,y_1) |-> y_0 t_0+y_1 t_1
```

are inverse additive maps.  For a left ideal use

```text
x |-> (t_0x,t_1x),       (y_0,y_1) |-> s_0y_0+s_1y_1.
```

The Leavitt relations verify both inverse formulas.  A nonzero finite
`F_2`-vector space cannot be isomorphic to its double, so every nonzero
one-sided ideal is infinite.  The general lemma now proves the claim in both
orientations.
