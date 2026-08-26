---
rg: 2
id: model-characters-of-compressed-pairs-are-compression-invariant
kind: claim
title: The tracial state a unitary model induces on the subgroup of a compressed pair is a fixed point of every compression endomorphism, and its kernel lies in the finite core
distinct_from:
  tempered-gamma-part-of-a-model-is-compressor-invariant: that decomposes the model's standard space into compressor-invariant corners; this records the scalar shadow of the same invariance, a fixed-point condition on the induced tracial state, and uses it to state the open character question that decides whether the abstract-embedding regime is empty.
  kt-compression-fixed-tracial-states-are-atomic-or-regular: that is the open classification of such fixed points for the Kun--Thom subgroup; this is the established fact that model characters are among them.
---

Let `Gamma <= G`, `t in G` with `t Gamma t^(-1) <= Gamma`, write
`phi_t = Ad(t)|_Gamma : Gamma -> Gamma` (an injective endomorphism), and let
`pi : G -> U(N)` be a homomorphism into a von Neumann algebra with faithful
normal tracial state `tau`.  Put `chi = tau o pi |_Gamma`, a tracial state of
`C^*(Gamma)`.

**Theorem.**  (1) `chi o phi_t = chi` for every compressor `t`: the induced
tracial state is a fixed point of the map `phi_t^*` on tracial states.
(2) In the criterion form of `abstract-unitary-embedding-upgrades-to-hyperlinear`,
where `pi` need not be faithful but a lamp projection `q in pi(Gamma)' cap N`
must have `Ad pi`-stabilizer exactly `Gamma` (its conjugates over distinct
cosets must be distinct), `ker(pi) <= core_G(Gamma)`, the intersection of all
conjugates of `Gamma`.  For the Kun--Thom pair that core is `EL_r(F_q)`,
finite, so `chi` is faithful modulo a finite normal subgroup.

Proof of (1): `chi(t gamma t^(-1)) = tau(pi(t) pi(gamma) pi(t)^*) = tau(pi(gamma))`.
Proof of (2): `ker(pi)` acts trivially by conjugation, so it stabilizes
every conjugate `q_x` and lies in every conjugate of `Gamma`; the core of
`EL_r(F_q[x_1..x_d])` under the monomial substitutions is `EL_r` of the
polynomials lying in every cone `A . N^d`, i.e. the constants.

**Where this bites.**  By `finite-dimensional-gamma-part-of-a-model-is-compression-blind`
and `tempered-gamma-part-of-a-model-is-compressor-invariant`, every model
splits as `e (+) f (+) (1 - e - f)`, and the compression-detecting part of a
faithful model of `W`, `E` or `D` lives on `1 - e - f` or on `f`.  The
restriction of `chi` to the remainder corner is again a fixed point of every
`phi_t^*` (the corner projection commutes with `pi(t)`), it is weakly mixing
(no finite-dimensional constituent) and non-tempered.  So the abstract
embedding regime opened by `abstract-unitary-embedding-upgrades-to-hyperlinear`
is nonempty only if `Gamma` has compression-fixed tracial states that are
neither mixtures of finite-dimensional characters nor supported on the
center.  Whether it does is `kt-compression-fixed-tracial-states-are-atomic-or-regular`.
