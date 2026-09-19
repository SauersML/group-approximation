---
rg: 2
id: homogeneous-quotient-hecke-dent-quantization-proof
kind: route
title: Count common-parahoric orbits and apply the exact one-shell dent identity
target: homogeneous-quotient-has-a-quantized-hecke-dent
requires:
  - homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse
  - single-hecke-dent-is-the-expanding-commutator-defect
---

Put `J=K cap hKh^(-1)`, so `[K:J]=D`.  Both `P` and `hP` are
`J`-invariant: `P` is `K`-invariant, while `hP` is
`hKh^(-1)`-invariant.  The action of every compact subgroup of `G` on
`X=G/Lambda'` is free.  Indeed a point stabilizer is an intersection of a
compact subgroup with a conjugate of the discrete lattice `Lambda'`; it is
finite, and hence trivial because `Lambda'` is torsion-free.

Consequently every `J`-orbit has measure

```text
Haar(J)/covol(Lambda')=1/(rD).                         (HQDP1)
```

The compact open set `P` is the disjoint union of exactly `D` such orbits,
and the `J`-invariant compact open set `P cap hP` is a union of `m` of them
for some integer `0<=m<=D`.  In fact `m<=D-1`.  If `m=D`, then
`P subseteq hP`; the two sets have equal measure, so `P=hP` modulo null sets
(and, being clopen, exactly).  Since `P` is also `C`-invariant and
`A=<C,h>`, this would make `P` `A`-invariant, contradicting ergodicity of the
`A`-action and `mu(P)=1/r` with `r>=2`.

It follows from `(HQDP1)` that

```text
mu(P triangle hP)
 =2(mu(P)-mu(P cap hP))
 =2(D-m)/(rD) >= 2/(rD).                               (HQDP2)
```

Conjugation sends `1_P` to `1_(hP)`, and therefore

```text
||Ad(u_h)(U)-U||_2^2
 =4 mu(P triangle hP) >= 8/(rD),                       (HQDP3)
```

which is `(HQD1)`.  The lower inequality `(SHD2)` of
`single-hecke-dent-is-the-expanding-commutator-defect` gives

```text
1-||S(U)||_2^2
 >=(1/4)||Ad(u_h)(U)-U||_2^2 >=2/(rD),
```

proving `(HQD2)`.

Finally normalized tensor amplification preserves every `2`-norm:
`||x tensor I_m||_(2,tau tensor tr_m)=||x||_(2,tau)`.  Since each Hecke
conjugation and its average act only on the first tensor factor,

```text
S_m(U tensor I_m)=S(U) tensor I_m.
```

This proves both identities in `(HQD3)`.  The same calculation applies to
the standard finite-rank corners of the stable identification `(DT2)`.
