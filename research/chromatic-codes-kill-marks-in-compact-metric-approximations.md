---
rg: 2
id: chromatic-codes-kill-marks-in-compact-metric-approximations
kind: claim
title: "Bounded-area chromatic codes kill their mark in every metric ultraproduct of compact bi-invariant groups, so each open code leaf implies a non-hyperlinear, non-weakly-sofic group"
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that is the operator-norm corona statement, with a one-line remark that compact bi-invariant targets also work; this proves the uniform version for CCC and CDC at once and draws the consequences for the two open code leaves, which neither leaf records.
  bounded-area-conjugacy-difference-code-kills-mf-mark: that is the CDC criterion for norm matrix coronas only; this is its extension to all compact bi-invariant targets.
  high-chromatic-sections-force-area-divergence: that is the Carmichael order-three section criterion in normalized Hilbert-Schmidt norm; this covers the commutator and conjugacy-difference codes, which are the ones used by the lifted-T and Leavitt code leaves.
  binary-leavitt-bounded-area-chromatic-code: that is an open leaf; this proves the leaf is incompatible with binary-leavitt-unit-group-hyperlinear.
artifacts:
  - research/chromatic-codes-compact-metric-approximation-proof.md
---

**ESTABLISHED** by `chromatic-codes-compact-metric-approximation-proof`.

## Setting

A **compact metric target** is a family `(K_i, d_i)` of compact groups, each
with a bi-invariant metric `d_i`, together with an ultrafilter or the
"limsup" corona convention. Its metric ultraproduct is
`K_omega = prod K_i / {(g_i) : lim_omega d_i(g_i, 1) = 0}`. Examples:

- `U(n)` with operator norm (the norm matrix corona, MF);
- `U(n)` with normalized Hilbert-Schmidt norm (hyperlinear);
- `Sym(n)` with normalized Hamming distance (sofic);
- any finite groups with bi-invariant metrics (weakly sofic);
- `GL_n(F_q)` with normalized rank distance (linear sofic over finite fields).

For a finitely presented `Gamma` and a class `C` of targets, `Rad_C(Gamma)`
is the intersection of the kernels of all homomorphisms `Gamma -> K_omega`
with `K_omega` in `C`.

## Statement

Let `Gamma = <S | R>` be finitely presented and let `x` be a word.

1. **(CCC.)** Suppose the data of `infinite-chromatic-commutator-code-kills-mf-mark`
   exist: a graph of infinite chromatic number, words `c_v, h_v, a_v`, and
   constants with `Area_R([c_v,h_v](a_v x a_v^-1)^-1) <= A_Delta` and
   `Area_R([c_w,h_v]) <= A_0` on every oriented edge.
2. **(CDC.)** Or suppose the data of `bounded-area-conjugacy-difference-code-kills-mf-mark`
   exist: `Area_R(b_v^-1 b_w a_vw x^-1 a_vw^-1) <= A` on every oriented edge.

Then `x` lies in `Rad_C(Gamma)` for the class `C` of **all** compact metric
targets. In particular `x` is killed by every homomorphism to `U(R^omega)`
(hyperlinear), to a sofic group, to a weakly sofic target, and to a norm
matrix corona.

## Consequences for the open code leaves

The lifted-T nodes named below (`lifted-thompson-t-bounded-area-chromatic-code`
and `central-marks-escape-chromatic-codes`) come from the swarm-0917 w17 ptm
lane and had not landed on main when this was written. Add a `distinct_from`
entry for the leaf when it lands.

- **Lifted Thompson T.** The mark of a code in `T̄` is non-central
  (`central-marks-escape-chromatic-codes`). The normal subgroups of `T̄` are
  the subgroups of `<z>` and `T̄` itself, because `T̄` is perfect and `T` is
  simple. So `Rad_C(T̄) = T̄`. Since `T̄ -> T` is onto, `T` has no nontrivial
  homomorphism to any compact metric ultraproduct. Hence
  `lifted-thompson-t-bounded-area-chromatic-code` implies:
  - `T` is not hyperlinear, not sofic and not weakly sofic;
  - `V`, which contains `T`, is not hyperlinear, which is `thompson-v-not-hyperlinear`.
- **Binary Leavitt.** A code in `Delta = St_20(L_(F_2)(1,2))` with mark `z`
  gives `Rad_C(Delta) = Delta`, because `Delta` is simple. With the
  identification `Delta = GL_20(R) = R^x` used by the target, the leaf
  `binary-leavitt-bounded-area-chromatic-code` implies that the binary Leavitt
  unit group is not hyperlinear and not weakly sofic. So the leaf is
  **incompatible** with the OPEN claim `binary-leavitt-unit-group-hyperlinear`,
  and with `binary-leavitt-unit-group-is-weakly-sofic`. At most one of each pair
  can hold.

## What this kills

- **Invariant:** compactness of each `K_i` together with bi-invariance of `d_i`.
  **Step:** the finite colouring by an `eta`-net of `K_i`.
- **Class fenced:** every bounded-area chromatic-code proof (CCC or CDC) of
  non-MF. Such a proof never uses the operator norm. It proves the stronger
  fact that there is no compact metric approximation at all.
- So each code route to `property-t-free-leavitt-full-mf-radical` costs
  at least the existence of a non-hyperlinear group. For the lifted-T leaf,
  that group is Thompson's `T`, a Haagerup group.
- No code can exist in a group whose relevant quotient is hyperlinear, sofic
  or weakly sofic. The lifted-T leaf is false if `T` is sofic. The Leavitt leaf
  is false if the Leavitt unit group is hyperlinear.
- **Not killed:** MF-specific mechanisms. These are the steps that use the
  operator norm without compactness, for example eigencorners, K-theory and
  Voiculescu-type obstructions.

DERIVATION
chromatic-codes-compact-metric-approximation-proof
