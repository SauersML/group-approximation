---
rg: 2
id: kazhdan-free-leavitt-collapse-typing-dichotomy
kind: claim
title: The Kazhdan-free Leavitt collapse is trivial when typed by certificates and needs a non-MF Kazhdan-blind group when typed by images
distinct_from:
  property-t-free-leavitt-full-mf-radical: that is the goal, whose restriction is a sentence about proofs; this shows which group-level typings of that restriction are available, and what each one costs.
  leavitt-st20-t-free-holes-hold-via-kazhdan: that shows three hole sentences are theorems through (T); this shows the same happens to every certificate-level typing, because Kazhdan and non-Kazhdan certificates are both cofinal.
  full-mf-radical-has-fp-cover-same-generators: that produces one finitely presented cover with full radical; this studies the whole upward-closed family of finite certificates, shows its Kazhdan members are cofinal, and shows non-Kazhdan members exist after one inert generator.
  property-t-laplacian-sos-certificate: that is Ozawa's criterion for one group; this lifts one certificate to every sufficiently large finite presentation cover.
  thompson-commutator-full-defect-bars-t-free-collapse: that bars collapse proofs that factor through the full-defect hypothesis; this bars no proof technique, and instead fixes what a Kazhdan-free conclusion must exhibit.
---

**ESTABLISHED** by `kazhdan-free-leavitt-collapse-typing-dichotomy-proof`.
This is not a Kazhdan-free result: part (b) uses the (T) theorem
`binary-leavitt-all-ranks-full-mf-radical`. It makes the goal's typing
precise and does not prove the goal.

**Setting.**
- `R = L_(F_2)(1,2)`, `Delta = St_20(R)`, and `S` is a finite symmetric
  generating set. `pi : F(S) -> Delta` is the canonical map, `z = x_13(s_1 t_1)`,
  and `zhat` in `F(S)` is a fixed lift of `z`.
- For a finite `R_0` contained in `ker pi`, put `Gamma_(R_0) = F(S)/<<R_0>>`.
- `Cert = { R_0 : zhat in Rad_MF(Gamma_(R_0)) }`, the set of **finite
  certificates** for `z`.
- A group is **Kazhdan-blind** if every homomorphism from a Kazhdan group into
  it has finite image. Equivalently, every Kazhdan subgroup is finite.
  Haagerup groups are Kazhdan-blind.

**(a) Upward closure.** If `R_0` is in `Cert` and `R_0 <= R_1 <= ker pi` is
finite, then `R_1` is in `Cert`. Moreover `Cert` is nonempty iff
`z in Rad_MF(Delta)`.

**(b) Both kinds of certificate occur.** `Cert` is nonempty.
- There is a finite `R_T <= ker pi` such that `Gamma_(R_0)` is Kazhdan for
  every finite `R_0` with `R_T <= R_0 <= ker pi`. So the Kazhdan certificates
  are cofinal in `Cert`.
- With one inert generator `t` added to `S` and sent to `1`, every certificate
  `R_0` is also a certificate over `S u {t}`. Its group `Gamma_(R_0) * Z` is
  not Kazhdan.

**(c) Certificate typing is empty.** Any property of the certificate group
that `Gamma * Z` has for every `Gamma` is met by some certificate. Two
examples are "not Kazhdan" and "has infinite abelianization". Any property
that every Kazhdan quotient of `F(S)` has is also met by some certificate.
So a restriction "the certificate group is not Kazhdan" holds whenever the
(T) theorem holds. It cannot separate a Kazhdan proof from a Kazhdan-free
one.

**(d) Image typing.** Suppose `Gamma` is any group and `phi : Gamma -> Delta`
is a homomorphism with `phi(Rad_MF(Gamma)) != 1`. Then
`Rad_MF(Delta) = Delta`. If `Gamma` is Kazhdan-blind, no Kazhdan group maps
into `Gamma` with infinite image. Then `Gamma` is a non-MF Kazhdan-blind
group, because `Rad_MF(Gamma) != 1`.

**(e) What the typed goal costs.** So "some Kazhdan-blind group maps to
`Delta` with a nontrivial radical image" implies the goal's equation. It
also produces a non-MF Kazhdan-blind group. No non-MF Kazhdan-blind group,
and in particular no non-MF Haagerup group, is recorded in this graph. Every
recorded non-MF group comes through (T), for example the elementary groups of
`binary-leavitt-all-ranks-full-mf-radical`.

**Reading for the program.**
- The certificate reading (parts (b) and (c)) is already settled by the
  (T) theorem.
- The image reading (parts (d) and (e)) is as hard as finding the first
  non-MF group with no infinite Kazhdan subgroup.
- Kazhdan-blind witnesses can be subgroups, as in
  `property-t-free-leavitt-via-thompson-v-not-mf`, or covers, such as a
  Haagerup `Gamma_(R_0)`.
