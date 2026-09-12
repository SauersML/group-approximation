---
rg: 2
id: toeplitz-schur-heads-share-child-but-have-rank-two
kind: claim
title: Toeplitz-actuated Schur heads share one fixed child but have cocycle rank only two
distinct_from:
  schur-packet-head-actuator-generates-over-tail: that embeds one Schur packet so its missing generator actuates the whole Toeplitz head; this computes all compressor iterates of that embedding and their joint commutator rank.
  schur-flip-wreath-compressor-has-infinite-cocycle-rank: that places independent packet flip squares at distinct wreath sites and obtains unbounded cocycle rank; the one-tail head actuator here repeats only one transverse packet direction and therefore has bounded rank.
  infinite-index-does-not-force-supercritical-site-rank: that allows arbitrarily many genuinely independent recovered cells but leaves a spectator multiplicity; this shows that the most direct Toeplitz iteration does not even create independent cells.
---

Use the disjoint-character-twist embedding from
`schur-packet-head-actuator-generates-over-tail-proof`.  Thus

```text
iota(g)=rho_0(g) h_0^(chi(g)),
h_n=e_ij(sigma^n(s)),
p_n=alpha^n(iota(p_m))=rho_0(p_m)h_n.                 (TSR1)
```

The character `chi` vanishes on the child `B_f^Q` and `rho_0(B_f)` has
coefficients in the constant field `F_2`.  Since `sigma` fixes `F_2`
pointwise,

```text
alpha^n(iota(g))=iota(g)       for g in B_f^Q.        (TSR2)
```

Hence all shifted full packets

```text
B_n=<B_f^Q,p_n>
```

share the child, its selector center, and its forbidden spectral carrier
**pointwise**.  No cross-level selector renewal or approximate alignment is
needed for this family.

However, the shifted heads do not amplify Clifford rank.  The transvections
`h_n` use one root position, so they commute pairwise; their block is disjoint
from `rho_0(B_f)`.  Therefore the `p_n` commute pairwise and have exactly the
same commutators with the fixed child generators as `p_m`.  On a forbidden
sector, retain one child Pauli direction `q`.  The alternating commutator form
on

```text
span_F2{p_0,...,p_(N-1),q}
```

has an edge from every `p_n` to `q` and no edges among the `p_n`.  Its rank is
exactly two for every `N>=1`:

```text
rank Omega_N=2.                                           (TSR3)
```

Thus direct Toeplitz iteration forces at most one Pauli multiplicity bit.
The differences `p_n p_0=h_nh_0` lie in the radical of this cocycle form.
Any supercritical use of the Toeplitz tail must regenerate transverse child
directions inside the residual commutant, place independent packet replicas,
or add a second branching coordinate.  Repeating the single head actuator is
not a dimension-pressure amplifier.
