---
rg: 2
id: two-adic-tower-format-proof
kind: route
title: Read the exact relations of the genuine representation and compute the corner depth shift
target: two-adic-tower-format-of-surviving-lambda-exact-enemy
requires:
  - sl3-upper-unipotent-is-a-noncommutative-solenoid-field
---

All three parts are read off from `pi` being a genuine homomorphism
on the ultraproduct, plus one integer computation.

**Part 1.**  `h lambda h^(-1) in Lambda` for `lambda in Lambda_-` is
the definition of `Lambda_-`, and `V pi(lambda) V^(-1) =
pi(h lambda h^(-1))` is `pi` applied to a relation of `Gamma`.  For
the depth shift write `lambda = 1 + 2^b X` with `X` integral; then
`h lambda h^(-1) = 1 + 2^b h X h^(-1)` and `h X h^(-1)` has entries
`(d_i/d_j) X_(ij)` with `d = (2, 1, 1/2)`: the worst denominator is
`4` at the corner `(3,1)`, so `h lambda h^(-1) in Lambda(2^(b-2))`,
and membership of `h lambda h^(-1)` in `Lambda` needs exactly the
`Lambda_-` divisibilities (`2 | lambda_21` is `2 | 2^b X_21`,
automatic for `b >= 1`; `4 | lambda_31` automatic for `b >= 2`), so
for `b >= 2` the entry `X_31` is unconstrained and the shift
`2^(b-2) X_31` at the corner is sharp.  Since `sigma_m` factors
through level `2^(a_m)`, the shift acts trivially precisely below
the visible levels.

**Part 2.**  `w_13 h w_13^(-1) = h^(-1)`, `h' = w_12 h w_12^(-1)`,
`h'' = w_23 h w_23^(-1)`, `h h''^(-1) = h'` and `[h_x, h_y] = e` are
identities among diagonal and signed-permutation matrices of
`Gamma`, verified entrywise (`diag(2,1,1/2) diag(1/2,2,1) =
diag(1,2,1/2)`); `pi` transports them to the displayed unitary
relations exactly.

**Part 3.**  The commutation of the `D`-tuple is part 2, and its exact joint
Haar spectral measure follows because the regular character of `Z^2`
evaluates to `delta_e`.  The upper-unipotent group is NOT abelian: it is the
Heisenberg group with `[e_12(x),e_23(y)]=e_13(xy)`.  Its forced regular
restriction is therefore the noncommutative direct-integral datum recorded
in `sl3-upper-unipotent-is-a-noncommutative-solenoid-field`: Haar central
measure and the canonical trace on almost every noncommutative-solenoid
fiber.  The expansion cross-relations are again `pi` applied to
`h e_alpha(r) h^(-1) = e_alpha(2^(<alpha, mu_h>) r)` in `Gamma`.

The format statement is the conjunction; the enemy direction
(microstates produce this data) uses only that lifts of exact
relations hold asymptotically and exactly in the ultraproduct.  No
converse is asserted: assembling such a tower system back into an
enemy would additionally require the remaining finitely many
relations of a full Behr presentation of `Gamma` and the regular
trace on all mixed words, which is the open closure question named
in the claim.
