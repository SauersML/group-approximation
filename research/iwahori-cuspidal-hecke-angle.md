---
rg: 2
id: iwahori-cuspidal-hecke-angle
kind: claim
title: On cuspidal cohomology the two Iwahori restriction maps have Petersson angle at least three minus two root two
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the full cochain-norm statement on all cocycle pairs; this is the cuspidal cohomology part in the Petersson norm, which is the piece Deligne's bound addresses directly.
---

Let `p` be an odd prime, `Gamma(p) <= SL_2(Z)` the principal congruence
subgroup, and `H^1_cusp(Gamma(p), C)` its cuspidal (interior) cohomology,
with the Petersson inner product under which the Hecke operator `T_2` is
self-adjoint.  Let `B(p) = Gamma^0(2) cap Gamma(p)` and let

```text
res_1, res_2 : H^1_cusp(Gamma(p), C) -> H^1_cusp(B(p), C)
```

be restriction and restriction composed with conjugation by
`t = diag(2, 1)`.  **Claim:** for all cuspidal `f, g`,

```text
|| res_1 f - res_2 g ||^2  >=  (3 - 2 sqrt 2) ( ||f||^2 + ||g||^2 ).          (CHA)
```

*Intended proof.*  The degeneracy maps satisfy `res_i^* res_i = 3` (index
of `B(p)` in `Gamma(p)` is `3`) and `res_1^* res_2 = T_2` on the cuspidal
part, so `||res_1 f - res_2 g||^2 = 3||f||^2 + 3||g||^2 - 2 Re <f, T_2 g>`;
Deligne's bound `|a_2(f)| <= 2 sqrt 2` for weight-two cusp forms of any
level (Ramanujan--Petersson, proved by Deligne) gives `||T_2|| <= 2 sqrt 2`
on cuspidal cohomology, whence `(CHA)`.

The same statement holds with coefficients in any finite-dimensional
representation `Ad rho` of `SL_2(F_p)` by passing to the isotypic
components of `H^1_cusp(Gamma(p), C)`, since `T_2` commutes with the
`SL_2(F_p)`-action.

## Attempts

- The identities `res_i^* res_i = 3` and `res_1^* res_2 = T_2` are the
  standard description of Hecke operators through the two degeneracy maps
  `X(p) <- X_0(2) cap X(p) -> X(p)`; what must be checked is that the
  adjoints are taken in the Petersson inner product on harmonic
  representatives, which is where the cuspidal restriction is needed.
- This proves nothing about Eisenstein classes
  (`iwahori-eisenstein-angle`) and says nothing about cochain norms
  (`iwahori-cochain-petersson-comparison`); those are the other two parts
  of `iwahori-uniform-infinitesimal-rigidity`.
