---
rg: 2
id: leavitt-units-over-s-integers-are-finitely-presented
kind: claim
title: For every m >= 1 the unit group of L_Z[1/m](1,2) is finitely presented
distinct_from:
  leavitt-unit-group-finitely-presented: that is Khanh's theorem over F_2; this is the characteristic-zero coefficient rings Z[1/m], which are neither fields nor simple.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is tensor hosts over F_p with simple coefficients; this has non-simple coefficients, where the division and GE inputs of that proof fail.
  char-zero-leavitt-unit-groups-have-congruence-kernels: that shows these groups are not simple; this asks whether they are finitely presented.
---

**OPEN.** For `m >= 1` put `R_m = L_(Z[1/m])(1,2)`. Then `R_m^x` is finitely presented.

**What is known.**
- **R_m is a finitely presented ring.** Generators `s_0, s_1, t_0, t_1, u`, with the
  Leavitt relations and `m u = 1`. The inverse of the central `m` is central.
- **Krstić–McCool** (`khanh-acyclicity-and-steinberg-criteria`, item 6): `St_n(R_m)` is
  finitely presented for `n >= 4`.
- **Leaf coordinates.** `R_m^x ≅ GL_n(R_m)` for every `n >= 2`, by the complete prefix
  codes, as over any coefficient ring.
- **Stable K-theory.** Expected to vanish: `Z[1/m]` is regular Noetherian, and the
  Ara–Brustenga–Cortiñas computation gives `K_*(L_A(1,2)) = 0` for regular
  supercoherent coefficient rings `A`, since `1 - 2` is invertible. This is not
  checked at the source here. The repo's import
  `ara-cortinas-leavitt-tensor-k-theory-vanishes` is stated over fields only.
- **Not simple.** The group is not simple; it has congruence quotients
  `L_(F_p)(1,2)^x`, `p ∤ m`, which are finitely presented modulo scalars
  (`char-zero-leavitt-unit-groups-have-congruence-kernels`,
  `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`).

**What is missing.** The unstable comparison `St_n(R_m) ≅ GL_n(R_m)` for one `n >= 4`.
In Khanh's route (Theorem 5.1) its inputs fail or are unchecked here:
- **GE fails as stated.** `GL_(n-1)(R_m) = E_(n-1)(R_m)` was obtained from
  Menal–Moncasi for *simple* rings with strong division. `R_m` has neither: for a prime
  `p ∤ m`, the element `p` has no `a, b` with `a p b = 1`, because reduction to
  `L_(F_p)(1,2)` kills it.
- **Two inputs unchecked.** Simple connectivity of the frame complex `|X_n(R_m)|`, and
  `j_(n-1)(N_(n-1)(R_m)) = 1`, are not checked.
- **Signs.** The characteristic-two restriction of Theorem 5.1 is addressed by the signed
  transporters of `prime-field-leavitt-tensor-hosts-proof`, step 3, which uses the
  Steinberg relations alone. That step has not been rechecked for coefficients `Z[1/m]`.

**Why it matters for `gl-n-q-embeds-in-fp-simple-group`.** `L_Q(1,2)^x` is the ascending
union of the `R_(m!)^x`, and each contains `GL_N(Z[1/m!])` for every `N`, `V`, and
`SL_3(Z)`. A positive answer makes `GL_n(Q)` an ascending union of subgroups of finitely
presented, non-residually-finite groups, all sharing one Leavitt structure. That is
input for the union routes; it is not an embedding of `GL_n(Q)` itself.
