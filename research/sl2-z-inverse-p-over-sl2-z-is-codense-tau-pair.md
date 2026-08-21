---
rg: 2
id: sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
kind: claim
title: SL2(Z) inside SL2(Z[1/p]) is co-dense with a uniform congruence conjugation gap
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  sl2-s-arithmetic-pair-is-codense-kazhdan: that uses the three-place group and a (T;FD) stabilizer; this uses the two-place group of Dogon--Vigdorovich's question and replaces (T;FD) of the subgroup by Selberg's property (tau), which is all the HNN theorem consumes.
---

Let `p` be a prime, `A = SL_2(Z[1/p])`, `C = SL_2(Z)`.

1. Every finite-dimensional unitary representation `rho` of `A` factors
   through a congruence quotient `SL_2(Z/m)` with `gcd(m, p) = 1`: the
   unipotent `u = [[1,1],[0,1]]` is conjugate by `diag(p, p^(-1))` to
   `u^(p^2)`, so `rho(u)` has spectrum stable under `z -> z^(p^2)`, hence
   finite order `N`; the normal closure of `u^N` has finite index
   (Peterson--Thom, arXiv:1303.4007, proof of Theorem 2.6, citing
   Bass--Milnor--Serre), and by Serre's congruence subgroup property for
   `SL_2` of S-integers with infinitely many units the quotient is a
   congruence quotient, whose level is prime to `p` because `p` is a unit.
2. `C` surjects onto every `SL_2(Z/m)`.  Hence the pair is
   finite-dimensionally co-dense: `pi^C = pi^A` for every finite-dimensional
   unitary `pi` of `A` (`pi` factors through a finite quotient on which `C`
   surjects).
3. **Uniform conjugation gap.**  For every finite-dimensional unitary
   representation `rho` of `A`, the conjugation representation
   `Ad rho|_C` of `C` on `(M_d, <,>_HS)` factors through the congruence
   quotient `SL_2(Z/m)` of `C`; by Selberg's theorem `C` has property
   `(tau)` with respect to congruence subgroups, so there is `kappa > 0`,
   depending only on the generating set of `C`, such that every vector
   `v in M_d` with `||rho(c) v rho(c)^* - v||_2 <= eps` for the generators
   `c` satisfies `||v - Ev||_2 <= eps/kappa`, `E` the projection onto
   `rho(C)'`.

So `(A, C)` satisfies every hypothesis of
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` in its `(tau)` form
except the flexible HS-stability of `A`, which for `p = 2` is exactly
`iwahori-local-global-defect-question`.  The HNN extension

```text
G_p = < SL_2(Z[1/p]), t | [t, SL_2(Z)] = 1 >
    = SL_2(Z[1/p]) *_(SL_2(Z)) ( SL_2(Z) x Z ),                     (SZ1)
```

finitely presented, with `w = [t, diag(p, p^(-1))] != 1` by Britton's
lemma, is nonhyperlinear whenever `SL_2(Z[1/p])` is flexibly HS-stable.
