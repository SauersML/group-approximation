---
rg: 2
id: fm-stone-lamp-corner-singularity-proof
kind: route
title: Force a reducing lamp corner and compare its Haar density with the Stone spectral law
target: fm-stone-lamp-corners-are-singular
requires:
  - stone-multiplicative-locus-is-haar-null-in-additive-dual
---

Let `v=q u_a q`.  Since `v` is unitary in `qMq`,

```text
q=v^*v=q u_a^* q u_a q.
```

Subtracting this from `q u_a^*u_a q=q` gives

```text
q u_a^*(1-q)u_a q=0,
```

hence `(1-q)u_aq=0`.  Applying the same calculation to `vv^*=q` gives
`q u_a(1-q)=0`; therefore `[q,u_a]=0`.  This holds for every `a in B`, and
the lamps generate `L^infinity(K)`.

Let `E:M -> L^infinity(K)` be the canonical conditional expectation and
`h=E(q)/tau(q)`.  For every `a in B`, commutation and traciality give

```text
tau(q)^(-1) tau(q u_a q)
 = tau(q)^(-1) tau(E(q)u_a)
 = integral_K chi_a h dm_K.                            (FSCP1)
```

Thus the normalized corner character is the Fourier transform of the
probability measure `h m_K`, which is absolutely continuous with respect to
Haar.

The source signs satisfy

```text
(1-2 1_a)(1-2 1_b)=1-2 1_(a symmetric_difference b).
```

Their joint spectral measure is therefore the pushforward of `mu` to
`dual(B,symmetric_difference)`.  Boolean multiplication of the event
projections says that this measure is supported on the ultrafilter/Stone
locus.  The established finite-subalgebra count makes that locus Haar-null
for atomless `B`.  If `(FSC1)` were trace preserving, `(FSCP1)` and its source
analogue would agree for all characters.  Characters determine probability
measures on the compact metrizable group `K`, yielding the contradiction.
