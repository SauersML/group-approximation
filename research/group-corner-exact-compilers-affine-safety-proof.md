---
rg: 2
id: group-corner-exact-compilers-affine-safety-proof
kind: route
title: The canonical trace of a group corner is uniform on answer cosets, so an affine decoder returns an affine source support
target: group-corner-exact-compilers-force-source-affine-safety
requires: []
artifacts:
  - research/artifacts/exact-lcs-compilation-map-2026-09-13.md
---

Notation as in `group-corner-exact-compilers-force-source-affine-safety`.

## Proof of (CS1)

**The projection.** Since `J^n = 1` and `omega` is a character,
`p_omega^* = p_omega`. Also

```text
p_omega^2 = (1/n^2) sum_(j,k) conj(omega(J^(j+k))) J^(j+k) = p_omega,
```

because each power `J^m` arises from exactly `n` pairs `(j,k)`. `J` is
central, so `p_omega` is central in `C*(Gamma)`.

**The trace.** The canonical trace satisfies `tau_Gamma(g) = 1` if `g = e`
and `0` otherwise. If `J` has order exactly `n`, then `J^k = e` only for
`k = 0 mod n`, so `tau_Gamma(p_omega) = 1/n`. Hence `p_omega != 0`, and
`tau_omega = n tau_Gamma(p_omega . p_omega)` is a positive functional with
`tau_omega(p_omega) = 1`. It is tracial because `tau_Gamma` is tracial and
`p_omega` is central.

**Values on A.** For `a in A`, centrality and `p_omega^2 = p_omega` give
`tau_omega(a p_omega) = n tau_Gamma(a p_omega)`, and

```text
tau_Gamma(a p_omega) = (1/n) sum_k conj(omega(J^k)) tau_Gamma(a J^k).
```

The term `tau_Gamma(a J^k)` is `1` exactly when `a = J^(-k)`. So
`tau_omega(a p_omega) = omega(a)` if `a in <J>` and `0` otherwise.

**The distribution.** The elements `a p_omega`, `a in A`, are commuting
unitaries of the corner and represent `A`. The `e_chi` of (GC2) are its
spectral projections: they are orthogonal and sum to `p_omega`. Therefore

```text
mu_A(chi) = tau_omega(e_chi)
          = (1/|A|) sum_(a in A cap <J>) conj(chi(a)) omega(a).
```

By orthogonality of characters of the finite group `A cap <J>`, the sum is
`|A cap <J>|` when `chi` and `omega` agree on `A cap <J>`, and `0`
otherwise. This is (GC4).

## Proof of (CS2)

**Apply the hypothesis to the canonical model.** Condition 2 holds for every
model, in particular for `tau_omega`. It yields a perfect tracial source
model with context projections

```text
Q_(c,phi) = sum_(chi : D_c(chi) = phi) e_chi,     phi in F_2^(V_c).
```

These are the joint spectral projections of the commuting `X_v`, `v in V_c`,
defined by (GC5).

**Its support.** By (CS1), `tau_omega(Q_(c,phi)) > 0` exactly when some
`chi in X_(A_(t(c)))(omega)` has `D_c(chi) = phi`. So the support is
`S_c = D_c(X_(A_(t(c)))(omega))`.

**It is affine.** `X_(A_(t(c)))(omega)` is a coset of the annihilator of
`A cap <J>` in `A^`. An affine map sends a coset of a subgroup to a coset of
the image subgroup, so `S_c` is an affine subset of `F_2^(V_c)`.

**It is safe.** The model is perfect, so `S_c subseteq C_c`, and an affine
set is its own affine hull. This is (GC6).

**The first consequence.** If every perfect tracial model of `B` has a
context with `Aff_F2(S_c)` not contained in `C_c`, then (GC6) gives a
contradiction. So no such compiler exists into an algebraically satisfiable
corner, i.e. one with `J` of order exactly `n`.
