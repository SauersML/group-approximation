---
rg: 2
id: sl2-exact-projective-transfer-via-doubled-squeeze-proof
kind: route
title: Double by Ad, squeeze with tau on the doubled space, transfer through the common image
target: sl2-exact-projective-transfer-via-doubled-squeeze
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
---

**Step 1 (doubling identity).**  For unitaries `W in U(d)`, the inner
superoperator `Ad(W) = W tensor conj(W)` acts on `(M_d, <,>_HS)`, a
`d^2`-dimensional Hilbert space, with `Tr(Ad W) = |Tr W|^2`.  Hence in
the normalized Hilbert--Schmidt norm of `M_(d^2)`,

```text
|| Ad(W) - I ||_2^2 = 2 - 2 |tr_d(W)|^2,
```

and since `Ad` is multiplicative with scalar kernel,
`[Ad U, Ad V] = Ad([U,V])`, so

```text
|| [Ad U, Ad V] ||_"comm"^2 := || Ad U Ad V - Ad V Ad U ||_2^2
  = || Ad([U,V]) - I ||_2^2 = 2 e(U, V).                       (DSQ2)
```

**Step 2 (squeeze on the doubled space).**  Put `sigma = Ad circ rho`,
a finite-dimensional unitary representation of `Gamma` on `M_d`, i.e.
after choosing a basis a representation into `U(d^2)`; it factors
through the same odd congruence quotient `Q` as `rho`.  Apply part 3 of
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair` — the uniform `(tau)`
conjugation gap, valid for EVERY finite-dimensional representation of
`Gamma` and every vector of the matrix space — to the representation
`sigma` and the vector `V = Ad(U) in M_(d^2)`:

```text
dist_2(Ad U, sigma(Lambda)') <= max_(c in S)
   || sigma(c) Ad(U) sigma(c)* - Ad(U) ||_2 / kappa
   <= sqrt(2 sum_c e(U, rho(c))) / kappa,
```

using `(DSQ2)` for each generator (the conjugation displacement of
`Ad U` by `sigma(c)` IS the commutator norm).

**Step 3 (transfer through the common image).**  `rho`, hence `sigma`,
factors through `Q = SL_2(Z/m)` with `m` odd, where the images of
`Lambda` and of `Gamma` COINCIDE (co-density, part 2 of the same
node).  Therefore `sigma(Lambda)' = sigma(Gamma)'`, and every element
of it commutes with `sigma(h)`.  Writing `P` for the nearest point of
`sigma(Lambda)'` to `Ad U`,

```text
|| [Ad U, sigma(h)] ||_2 <= 2 || Ad U - P ||_2
   <= 2 sqrt(2 E_C) / kappa,
```

and by `(DSQ2)` again, `2 e(U, rho(h)) = || [Ad U, sigma(h)] ||_2^2
<= 8 E_C / kappa^2`, which is `(DSQ1)`.

**Remarks.**  No perfectness, no property (T), and no character
extraction: the scalar commutator phases live in the kernel of `Ad`
and never appear.  The same three steps run for every pair with
co-density and a uniform conjugation gap, so the SL_n versions hold
with the corresponding constants; the novelty is that `(tau)` alone
suffices.  All constants are independent of `d`, level, and
multiplicity, matching the probe's four-digit multiplicity
independence.
