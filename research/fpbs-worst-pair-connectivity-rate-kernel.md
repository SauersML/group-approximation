---
rg: 2
id: fpbs-worst-pair-connectivity-rate-kernel
kind: claim
title: A positive exponential rate for the worst connection in a ball at one p above p_c gives p_c < p_u, and the sphere rate below log gr already forces it
distinct_from:
  fpbs-sphere-two-point-rate-bounds-walk-rate: that bounds the walk rate by rho cosh g and needs g below arccosh(1/rho); this compares g with log gr through the minimum of tau over a ball and needs no spectral input
  fpbs-intrinsic-l2-rate-closed-zero-set: that rate uses chemical-radius truncations and BK and vanishes on [0,p_c]; this rate uses extrinsic worst pairs and Harris-FKG and is at least log gr at p_c
  fpbs-sphere-two-point-rate-below-arccosh-universal: that kernel (G) asks g(p) < arccosh(1/rho); this node proves (G) implies the strictly weaker sufficient kernels (K') and (K)
---

**ESTABLISHED.** Proof in `fpbs-worst-pair-connectivity-rate-kernel-proof`.

**Setting.** `G = Cay(Gamma,S)` for a finitely generated nonamenable group,
`o` the identity, `S_r` and `B_r` spheres and balls, `gr = lim |B_r|^(1/r) > 1`.
`tau_p(u,v) = P_p(u <-> v)`. Put

```text
kappa_p(n) = inf{ tau_p(u,v) : d(u,v) <= n } = min_(v in B_n) tau_p(o,v),
gamma(p)   = lim_n -(1/n) log kappa_p(n),
g(p)       = limsup_r (1/r) log E_p|K_o ∩ S_r|.
```

**Claim.** For `p in (0,1]`:

1. The limit `gamma(p)` exists and equals `inf_n -(1/n) log kappa_p(n)`, with
   `0 <= gamma(p) <= -log p`. `gamma` is nonincreasing and left-continuous.
2. If `gamma(q) > 0`, then no `p' <= q` has a unique infinite cluster.
3. `g(p) >= log gr - gamma(p)`.
4. So these kernels each imply `p_c < p_u`:
   - **(K)** `gamma(p) > 0` for some `p > p_c`;
   - **(K')** `g(p) < log gr` for some `p > p_c`.

   The implications `(EG) => (G) => (K') => (K) => p_c < p_u` all hold. The
   step `(G) => (K')` is `arccosh(1/rho) <= log gr`, from Section 4 of
   `research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md`.
5. **Strictness on trees.** On `T_d` (`d >= 3`), the kernel sets are:
   - (K): all of `(0,1)`;
   - (K'): all of `(0,1)`, which is the whole nonuniqueness interval;
   - (G): only `(0, 1/sqrt(d-1))`.
6. **Finite certificates only bound gamma from above.** `gamma` is an
   infimum over `n`, so knowing `kappa_q(N)` for finitely many `N` gives only
   upper bounds on `gamma`. A lower bound needs `kappa_p(n) <= e^(-cn)` for
   *every* `n`.

Beyond (G), the new content is **(K)**. It asks only that, in some ball of
every radius `n`, *one* point is connected to the centre with probability
`<= e^(-cn)`.
