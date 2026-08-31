---
rg: 2
id: wedderburn-rank-vectors-classify-finite-packet-cuts-proof
kind: route
title: Rank vectors are the complete finite packet multiplicity invariant
target: finite-packet-trace-authentication-is-internal-equivalence
requires:
  - rectangular-safe-covariance-has-a-positive-head-absorber
---

Wedderburn decomposition gives

```text
C[F] isomorphic to directSum_(pi in Irr(F)) M_(d_pi)(C). (WRV1)
```

Write `p_pi,q_pi` for the components of the two projections. In the
irreducible representation `pi`,

```text
rank(pi(p))=rank(p_pi),          rank(pi(q))=rank(q_pi).
```

An arbitrary finite-dimensional representation has multiplicities
`m_pi` and therefore

```text
rank(rho(p))=sum_pi m_pi rank(p_pi),
rank(rho(q))=sum_pi m_pi rank(q_pi).                    (WRV2)
```

Equations `(WRV1)--(WRV2)` prove the equivalence of conditions 1 and 2.

Two projections in one full matrix algebra are Murray--von Neumann
equivalent exactly when they have the same rank. Thus condition 1 lets us
choose, in every Wedderburn block, a partial isometry `v_pi` with

```text
v_pi^*v_pi=p_pi,             v_pi v_pi^*=q_pi.
```

Their direct sum belongs to `C[F]` and proves condition 3. Conversely,
applying any representation to `(FPT1)` gives Murray--von Neumann
equivalent matrices and hence equal ranks. This completes the equivalence.

The normalized regular trace is only

```text
tau_reg(p)=|F|^(-1) sum_pi d_pi rank(p_pi).             (WRV3)
```

Equality of `(WRV3)` for `p,q` is one weighted scalar equation and need
not make the rank vectors equal. If
`rank(p_pi)!=rank(q_pi)` for one block, take
`rho=pi^(directSum M)`. Its normalized rank difference is

```text
|rank(p_pi)-rank(q_pi)|/d_pi,
```

independent of `M`. Hence regular-trace balance has no uniform
all-representation consequence.

For a qutrit tag with canonical trace `1/18`, formula `(WRV3)` is exactly
what the canonical computation supplies. To promote it to matrix-model
authentication one must still prove equality of the full rank vectors.
If that proof is internal to a finite packet, the blockwise construction
above simultaneously produces its absorber `v`. The same audit applies to
finite Clifford tags.

This is why a finite packet cannot provide a one-way same-trace constraint:
all-representation equality and internal partial-isometry equivalence are
the same semisimple datum.
