---
rg: 2
id: finite-packet-trace-authentication-is-internal-equivalence
kind: claim
title: Finite packet trace authentication is exactly finite packet equivalence
distinct_from:
  rectangular-safe-covariance-has-a-positive-head-absorber: that exploits unmatched multiplicities; this classifies when a finite packet can force those multiplicities to match
  qutrit-jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16: that computes canonical regular ranks of specific source cuts; this separates canonical trace equality from equality in every finite representation
  first-g2-mixed-return-has-a-dihedral-half-absorber: that finds one concrete finite sign absorber; this gives the general semisimple-algebra reason finite type balancing produces absorbers
---

Let `F` be a finite group and let `p,q` be projections in `C[F]`. The
following are equivalent:

1. `rank(pi(p))=rank(pi(q))` for every irreducible unitary
   representation `pi` of `F`.
2. `rank(rho(p))=rank(rho(q))` for every finite-dimensional unitary
   representation `rho` of `F`.
3. There is a partial isometry `v in C[F]` with

```text
v^*v=p,                    vv^*=q.                      (FPT1)
```

Thus a finite packet forces exact same-trace source and target
multiplicities in all matrix models only when the packet itself already
contains a finite partial-isometry absorber between them.

Equality in the canonical regular trace is strictly weaker. If
`tau_reg(p)=tau_reg(q)` but condition 1 fails, choose an irreducible block
where the ranks differ and repeat it. This gives exact finite packet models
with a fixed normalized source-target rank mismatch.

For the qutrit head packet, the established calculation

```text
tau_reg(E e_b)=1/18
```

is only canonical regular-trace data. It does not by itself prove equality
of the irreducible rank vectors. If an enlarged qutrit packet supplies an
explicit conjugator or matrix units proving equality in every irreducible
block, condition 3 then supplies an internal finite absorber. The same
dichotomy applies to a Clifford packet: matrix units inside one selected
representation are not enough unless they belong to the packet algebra
with the required blockwise source and target ranks.

Consequently the canonical value `alpha=1/18` does not by itself close the
rectangular Jacobson seam. A finite qutrit or Clifford tag gives either:

- only regular-trace equality, which arbitrary irreducible multiplicities
  can violate; or
- blockwise equality, which is already implemented by `(FPT1)` and can be
  absorbed without touching the payload.

A successful same-trace authentication must therefore use a shared
non-finite occurrence or a matrix-only selector coupling packet
multiplicity to the raw Jacobson coefficient. Pure finite type data cannot
supply it.

DERIVATION
wedderburn-rank-vectors-classify-finite-packet-cuts-proof
