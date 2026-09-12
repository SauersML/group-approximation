---
rg: 2
id: bc-kun-thom-gap-label-limit-proof
kind: route
title: Congruence moment convergence plus a continuity point of the density of states
target: bc-kun-thom-gap-label-is-congruence-eigenvalue-limit
requires: []
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

Let `taubar = tau/n` be the tracial state on `M_n(C*_r G)`. Write `mu` for the
spectral distribution of the self-adjoint `lambda(a)` with respect to `taubar`:
the compactly supported probability measure on `R` with moments
`int t^m dmu = taubar(lambda(a)^m)`. For each congruence quotient
`pi_(p') : G -> G/N_(p')` let `mu_(p')` be the eigenvalue-counting probability
measure of the Hermitian matrix `pi_(p')(a)` of size `n [G : N_(p')]`, i.e.
`mu_(p') = (n[G:N_(p')])^(-1) sum_j delta_(t_j)` over its eigenvalues `t_j`.

**1. Moment convergence.** Fix `m`. The `m`-th moment of `mu_(p')` is the
normalized trace `(n[G:N_(p')])^(-1) Tr pi_(p')(a)^m`. The image of `a^m` in
`M_n(C[G/N_(p')])` is `pi_(p')(a)^m`, and for the finite quotient
`(n[G:N_(p')])^(-1) Tr pi_(p')(a)^m = n^(-1) sum_i (a^m)_(ii)(1_{G/N_(p')})`,
the coefficient at the identity of `G/N_(p')`. The support of `a^m` lies in the
finite set `(supp a)^m`. By the avoidance lemma
(`kun-thom-actor-algebraic-idempotents-pass-trace-test`, Lemma C, from the
artifact), for every prime `p'` larger than a bound `M(m)` the kernel
`N_(p')` meets `(supp a)^m \ {1}` trivially, so the identity coefficient over
the quotient equals the identity coefficient over `G`:
`n^(-1) sum_i (a^m)_(ii)(1_{G/N_(p')}) = n^(-1) sum_i (a^m)_(ii)(1_G) =
taubar(lambda(a)^m)`. Hence `int t^m dmu_(p') -> int t^m dmu` as `p' -> inf`,
for every `m`.

**2. Weak convergence.** `mu` is compactly supported (`||lambda(a)|| < inf`),
so it is determined by its moments, and all `mu_(p')` are supported in the
fixed interval `[-||a||_1, ||a||_1]` (the coefficient `l^1` bound on `a`).
Moment convergence of measures on a fixed compact interval to a determinate
limit is weak convergence: `mu_(p') -> mu` weakly.

**3. Continuity point.** `c` lies in a spectral gap of `lambda(a)`, so an open
interval `(c-eps, c+eps)` is disjoint from `supp mu`. In particular
`mu({c}) = 0` and `mu` has no mass in that interval, so `c` is a continuity
point of the distribution function `F(t) = mu((-inf, t))`. By the Portmanteau
theorem, weak convergence gives `mu_(p')((-inf, c)) -> mu((-inf, c))` at the
continuity point `c`.

**4. Identification of the two sides.**
- Right side: `mu_(p')((-inf,c)) = #{ eigenvalues of pi_(p')(a) below c } /
  (n[G:N_(p')])`, exactly the displayed fraction.
- Left side: because `c` is not in `spec(lambda(a))`, the indicator
  `chi_((-inf,c))` is continuous on `spec(lambda(a))` (locally constant across
  the gap), so `chi = chi_((-inf,c))(lambda(a))` is a genuine projection in
  `M_n(C*_r G)` given by continuous functional calculus, and
  `taubar(chi) = int chi_((-inf,c)) dmu = mu((-inf,c))`.

Combining, `taubar(chi) = lim_(p') #{...}/(n[G:N_(p')])`, and multiplying by `n`
gives `tau(chi) = lim_(p') #{...}/[G:N_(p')]`. QED

**What this does not give.** The limit exists and is a real number in `[0, n]`
for `tau(chi)`, but the argument places no arithmetic constraint on it: the
finite quotients are not tempered, and eigenvalues of non-tempered constituents
may accumulate at the gap edge with vanishing weight. Forcing the limit into
`Z[1/P]` is the open determinant/Atiyah-type integrality question of
`baum-connes-counterexample-group-exists`; a limit outside `Z[1/P]` refutes
surjectivity of the reduced assembly map.
