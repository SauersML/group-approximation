---
rg: 2
id: leavitt-corner-host-simple-unit-group-proof
kind: route
title: Transport St_20 to the unit group by Khanh and a prefix code, then use simplicity to make every charged embeddable character faithful
target: leavitt-corner-host-is-the-simple-leavitt-unit-group
requires:
  - leavitt-steinberg-map-iso-from-rank-three
  - binary-leavitt-elementary-group-is-simple
  - openai-leavitt-unit-nonsofic
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
  - character-diracization-limit
  - leavitt-unit-group-finitely-presented
  - toeplitz-supported-leavitt-corner-is-jacobson-hyperlinearity
---

Notation as in the target claim.

## Step 1. Host

**The Steinberg map.**  By `leavitt-steinberg-map-iso-from-rank-three`
(Khanh, arXiv:2609.08428, Theorem 5.4, `(KH2)`), `St_20(R) -> GL_20(R)` is an
isomorphism.  By Lemma 5.3 there, `GL_20(R)=E_20(R)`.

**The prefix code.**  The relations `t_is_j=delta_ij` and
`s_1t_1+s_2t_2=1` make `(t_1,t_2): R -> R^2` and `(s_1,s_2): R^2 -> R` inverse
isomorphisms of right `R`-modules.  So `R ~= R^2`, and by induction
`R^n ~= R^(n-1) (+) R ~= R^(n-1) (+) R^2 = R^(n+1)`.  Hence `R^20 ~= R`, and
`M_20(R) = End_R(R^20) ~= End_R(R) = R` as unital rings.  So
`GL_20(R) ~= R^x`.

**Properties.**

- Simplicity: `binary-leavitt-elementary-group-is-simple` (`n=20`).
- Finite presentation: `leavitt-unit-group-finitely-presented`.
- Nonsoficity: `openai-leavitt-unit-nonsofic`.
- Perfection: a nonabelian simple group is perfect.

## Step 2. Certificates

"CE" means approximate matricial microstates.  (F1)--(F4) refer to Step 0 of
`leavitt-corner-trace-gate-jacobson-proof`, the route of the required claim
`leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`.

**(=>)**  Let `tau` be a CE character of `Delta` with `tau(z) != 1`.

- **Diracize.**  By (F2), `|tau|^(2k)` is CE.  By
  `character-diracization-limit`, it converges pointwise to `1_(K_tau)`,
  where `K_tau = {g : |tau(g)|=1}` is normal.  By (F3), `1_(K_tau)` is CE.
- **The kernel is `1` or `Delta`.**  `Delta` is simple, so `K_tau` is `1` or
  `Delta`.
- **Not `Delta`.**  Suppose `K_tau=Delta`.  In the GNS algebra, `|tau(g)|=1`
  means `u_g=tau(g)1` (proof of `character-diracization-limit`).  So `tau` is
  a homomorphism `Delta -> T`.  `Delta` is perfect, so `tau=1`, which
  contradicts `tau(z) != 1`.
- **So `K_tau=1`.**  Then `delta_e=1_(K_tau)` is CE, and by (F4) with `N=1`,
  `Delta` is hyperlinear.

Simplicity replaces the facts `C_E(L)=1` and perfection of `L` used in the
Jacobson case.

**(<=)**  If `Delta` is hyperlinear, then by (F4) its regular character
`delta_e` is CE, and `delta_e(z)=0 != 1`.

## Step 3. Mutual exclusion

**Why LNC3 kills embeddable traces.**  As in
`leavitt-negative-root-bcs-corner-route-to-nonhyperlinear`:

- by `lin-explicit-fixed-bcs-gap-via-generic-conversion` and
  `paddock-slofstra-bcs-forbidden-projection-dictionary`, `A(B_loop)` has no
  Connes-embeddable tracial state;
- so `nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear` applies to
  any `LNC3` map.

**Every CE character sees `z` as `1`.**  Let `tau` be a CE character of
`Delta`.  Suppose `LNC3` holds with support `X`.

- Restricting microstates shows that `tau|<X,z>` is a CE character of
  `<X,z>`, with the same value at `z`.
- Item 1 (trace gate) of
  `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity` then gives
  `tau(z)=1`.

**The three implications.**

- If `LNC3` holds, then no embeddable `tau` has `tau(z) != 1`.  By Step 2,
  `R^x` is not hyperlinear, so `binary-leavitt-unit-group-hyperlinear` is
  false.
- Conversely, if `R^x` is hyperlinear, `delta_e` charges `P_z`, so `LNC3`
  fails.
- The "exactly" clause is Step 2: an embeddable-trace refutation is a
  character `tau` with `tau(z) != 1`, and such characters exist iff `R^x` is
  hyperlinear.

**The Toeplitz decision point.**  By
`toeplitz-supported-leavitt-corner-is-jacobson-hyperlinearity`,
`T_2=F_2<s_2,t_2> <= R` is isomorphic to `J`.  Entrywise inclusion gives
`EL_20(J) ~= EL_20(T_2) <= E_20(R) ~= Delta`.  Hyperlinearity passes to
subgroups, so hyperlinearity of `R^x` implies hyperlinearity of `EL_20(J)`.
