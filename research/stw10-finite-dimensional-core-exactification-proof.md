---
rg: 2
id: stw10-finite-dimensional-core-exactification-proof
kind: route
title: Correct a quasidiagonal model by averaging its Stinespring isometry over the core
target: stw10-qd-traces-admit-exact-finite-dimensional-core-models
requires: []
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

We prove a perturbation lemma first.  Let `E subset A` be unital and
finite-dimensional.  Suppose `phi:A -> M_k` is u.c.p. and there is a unital
star homomorphism `pi:E -> M_k` such that

```text
delta = sup_(u in U(E)) ||phi(u)-pi(u)||
```

is small.  Take a Stinespring representation

```text
phi(x)=V* rho(x) V,             V*V=1.
```

For every `u in U(E)`, direct expansion gives

```text
||rho(u)V-V pi(u)||^2
 = ||2-phi(u*)pi(u)-pi(u*)phi(u)|| <= 2 delta.
```

Average over the compact unitary group of `E`:

```text
T = integral_(U(E)) rho(u) V pi(u)* du.
```

Haar invariance gives `rho(a)T=T pi(a)` first for unitaries and hence for
all `a in E`, while `||T-V|| <= sqrt(2 delta)`.  Thus `T*T` commutes with
`pi(E)` and converges to `1` as `delta` tends to zero.  For sufficiently
small `delta` it is invertible.  Put

```text
W=T(T*T)^(-1/2),                psi(x)=W* rho(x) W.
```

Then `W` is an isometry, still satisfies `rho(a)W=W pi(a)`, and converges in
norm to `V`.  Hence `psi` is u.c.p.,

```text
psi|E=pi,                       E subset MD(psi),
||psi-phi|| <= 2||W-V|| -> 0.
```

The last norm is the norm of maps on the whole unit ball, not merely on a
selected finite set.  This is the point that preserves every finite packet
of multiplicativity and trace estimates at once.

Now let `(phi_i)` be quasidiagonal trace models for `tau`.  Their restrictions
to `E` are asymptotically multiplicative unital completely positive maps.
Stability of the relations of a finite-dimensional C-star algebra gives, on
a cofinal tail, unital star homomorphisms

```text
pi_i:E -> M_(k_i),              ||phi_i|E-pi_i|| -> 0.
```

For completeness, write `E=direct_sum_r M_(d_r)` and choose matrix units
`e^(r)_(ab)`.  Approximate multiplicativity first makes the positive
contractions `phi_i(1_r)` into almost orthogonal almost projections whose
sum is `1`; functional calculus and successive orthogonal compression
replace them by orthogonal projections `q^(r)_i` summing to `1`.  In each
corner, functional calculus on the almost diagonal matrix units followed by
polar decomposition of the almost off-diagonal matrix units produces exact
matrix units `f^(r,i)_(ab)`.  Every perturbation tends to zero because the
list of relations is fixed and finite.  Sending `e^(r)_(ab)` to
`f^(r,i)_(ab)` defines `pi_i`.  Point-norm convergence on this fixed basis
implies uniform norm convergence on the unit ball of the fixed
finite-dimensional algebra `E`, which is the displayed estimate.

Applying the Stinespring averaging construction produces `psi_i` with
`E subset MD(psi_i)` and `||psi_i-phi_i|| -> 0`.  Therefore

```text
||psi_i(xy)-psi_i(x)psi_i(y)|| -> 0,
tr_(k_i)(psi_i(x)) -> tau(x)
```

for all `x,y in A`.  This proves the forward implication; the reverse is
immediate after forgetting the multiplicative-domain condition.  The same
argument, phrased over finite packets, applies to nonseparable `A` and
produces a net rather than silently choosing a sequence.

Apply the lemma to `E=D_n`.  Any unital homomorphism
`D_n isomorphic to M_(2^n) -> M_k` is an amplification of the defining
representation.  In particular `2^n` divides `k` and

```text
tr_k o psi|D_n = tr_(2^n) = tau_R|D_n.
```

This proves the core-exact finite criterion.  If `A` is separable and
contains all `D_n`, diagonalize ordinary quasidiagonal trace models against
a dense sequence in `A`, correcting the `n`-th chosen model relative to
`D_n`; this gives the asserted sequence.  Conversely that sequence is
already a quasidiagonal trace model.

**Trust boundary.**  The correction starts from operator-norm
multiplicativity.  Hyperfiniteness alone only supplies normalized
Hilbert--Schmidt multiplicativity, to which the matrix-unit perturbation and
the operator-norm estimate above do not apply.  No exactness, nuclearity,
local lifting, quotient descent, or norm approximation of `R` by the CAR
stages is used.
