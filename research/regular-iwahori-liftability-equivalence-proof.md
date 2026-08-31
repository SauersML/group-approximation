---
rg: 2
id: regular-iwahori-liftability-equivalence-proof
kind: route
title: Exactify the modular vertices and compare with flexible exact global lifts
target: regular-iwahori-exactification-is-regular-branch-liftability
requires:
  - sl2-z-same-dimension-hs-stable
  - congruence-repair-bypasses-koopman-cycle-firewalls
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
  - regular-bs14-cores-align-with-congruence-endpoint-restrictions
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
---

Assume flexible regular relative congruence exactification, and let `phi_n`
be a regular microstate sequence of `Gamma` on dimensions `d_n`. Restrict
`phi_n` to the two modular vertices. By
`sl2-z-same-dimension-hs-stable`, perturb each restriction in dimension
`d_n` to exact representations

```text
pi_(n,+),pi_(n,-):SL_2(Z)->U(d_n).
```

The perturbation is `o(1)` on generators, so the Iwahori edge defect is
still `o(1)`. It also does not change the induced ultraproduct
representation, whose character remains `delta_e`. Flexible relative
congruence exactification gives common dimensions

```text
D_n>=d_n,       D_n/d_n->1,
```

and exact congruence vertex representations
`eta_(n,+),eta_(n,-):SL_2(Z)->U(D_n)` at generalized distance `o(1)`,
with edge defect `o(1)`.

Apply `congruence-repair-bypasses-koopman-cycle-firewalls` in dimension
`D_n`. Its level- and dimension-independent constant perturbs the `eta`
pair by `o(1)` to a literally compatible pair. The latter is a genuine
representation

```text
rho_n:Gamma->U(D_n).
```

Generalized triangle inequality puts `rho_n` at distance `o(1)` from
`phi_n`. This proves flexible regular-branch liftability.

Conversely, assume flexible regular-branch liftability and start with an
exact vertex pair in property 1 on dimensions `d_n`. Since the only
nonzero defining defects are the finitely many edge-identification
defects, the pair itself is a regular microstate sequence of `Gamma`.
Liftability gives dimensions `D_n>=d_n`, with `D_n/d_n->1`, and genuine
representations

```text
rho_n:Gamma->U(D_n)
```

at generalized distance `o(1)`. By
`finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence`, every
`rho_n` factors through an odd congruence quotient. Its two vertex
restrictions are the required congruence pair and have edge defect zero.
This proves flexible relative congruence exactification.

Flexible regular-branch liftability immediately implies the congruence-core
property, because that property is a special microstate family. For the
reverse implication, start with an arbitrary regular microstate. The
HS stability of the `BS(1,4)` skeleton, recorded in
`iwahori-square-root-presentation-is-bs14-plus-one-involution`, exactifies
its square-free core in the original dimension at `o(1)` cost. The trace
remains regular. Then
`regular-bs14-cores-align-with-congruence-endpoint-restrictions` conjugates
that exact core, still in the same dimension and at `o(1)` cost, onto the
core restriction of exact odd-congruence representations whose characters
tend to `delta_e`. Conjugate the supplied extending involution by the same
unitaries. This is precisely the input normal form of property 3, which
returns a flexible exact global lift. Hence property 3 implies property 2.

The dimension enlargement cannot be removed.
`regular-iwahori-strict-congruence-exactification-is-false` gives regular
SL2 vertex pairs for which all same-dimensional exact lifts stay a fixed
distance away. Its balanced even/odd Weil completion needs only one added
positive-central line, so `D_n/d_n->1`; it refutes the strict equivalence
but not any flexible implication above.
