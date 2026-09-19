---
rg: 2
id: jacobson-mf-characters-zero-one-law
kind: claim
title: MF characters of EL_n of the binary Jacobson ring obey a zero-one law, so the regular-character hole is exactly tracial head collapse in arbitrary MF models
distinct_from:
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: Theorem JH there is the same dichotomy for Connes-embeddable characters (2-norm microstates), whose regular alternative is hyperlinearity; this is the operator-norm (MF) version, whose regular alternative is the MF regular character, which is the hole on the goal's route.
  jacobson-regular-character-not-mf-without-property-t: that is the hole, excluding one named trace; this proves the hole equivalent to excluding every MF model in which the head keeps positive normalized Hilbert--Schmidt mass, with no regularity hypothesis on the model.
  leavitt-mf-survivor-yields-jacobson-regular-character: that transports a Leavitt MF survivor down to the regular MF character of EL_5(J); this is internal to EL_n(J) and classifies all its MF characters, using the same closure and Diracization steps.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that is the all-or-nothing statement for homomorphisms (head survives in norm iff faithful); this is the all-or-nothing statement for MF traces (head survives in trace iff regular trace is MF).
  torsion-normal-generator-mf-character-criterion: that turns a norm survivor of a normal generator into a positive-density model; the Jacobson head normally generates only the finitary kernel, and the gap recorded here is exactly that missing reblocking.
artifacts:
  - research/jacobson-mf-characters-zero-one-law-proof.md
  - experiments/jacobson-mf-zero-one-2026-09-17/check_transvection_facts.py
---

**ESTABLISHED** (route `jacobson-mf-characters-zero-one-law-proof`).
It uses no property `(T)`, no Kazhdan projection and no spectral-gap input.

**Setup.**
- `J = F_2<S,T | TS=1>`, `Q = 1-ST`, `n >= 2`, and `E = EL_n(J)`.
- `L = GL_fin(N x {1..n}, F_2)` is the finitary kernel, `p : E -> E/L` is the
  symbol quotient, and `w = x_12(Q)` (for `n >= 3`, equally `x_13(Q)`) is the
  head. Any nonidentity `w in L` works below.
- An **MF model** is a sequence of maps `rho_k : E -> U(d_k)` with
  `||rho_k(gh) - rho_k(g) rho_k(h)|| -> 0` in operator norm for all `g, h`.
- An **MF character** is a pointwise limit `tau = lim tr rho_k`, with `tr`
  the normalized trace.
- `||x||_2 = tr(x^* x)^(1/2)`.

**Theorem (MF zero-one law).** Exactly one of the following holds.

```text
(Z1)  every MF character of E is trivial on L, hence factors through p;
(Z2)  delta_e^E is an MF character of E.                                  (ZO)
```

More precisely, for every MF character `tau` with scalar kernel
`K_tau = {g : |tau(g)| = 1}`, either `L <= K_tau` and `tau|_L = 1`, or
`K_tau = 1` and then `delta_e^E` is MF.

**Corollary 1 (the hole is tracial head collapse).** The following are
equivalent:
1. `jacobson-regular-character-not-mf-without-property-t` holds for `E` (that
   is, `delta_e^E` is not MF).
2. (Z1).
3. **(THC)**: for every MF model `rho_k` of `E`,
   `||rho_k(w) - 1||_2 -> 0`, i.e. the normalized rank of the `(-1)`-eigenspace
   of the involution `rho_k(w)` tends to `0`.
4. No MF model of `E` has `limsup ||rho_k(w) - 1||_2 > 0`.

In particular, a single MF model of `E` in which the head keeps any positive
normalized Hilbert--Schmidt mass, however small, upgrades to a
regular-trace MF model. The upgrade uses conjugate tensor powers and a
diagonal limit.

**Corollary 2 (where HC and H1 differ).** Write (HC) for
`property-t-free-jacobson-head-collapse`. By
`binary-jacobson-head-retaining-homomorphisms-are-faithful`, (HC) says that
`E` is not operator-MF. So for `E = EL_5(J)`:

```text
(HC)   <=>  E is not MF
(H1)   <=>  delta_e^E is not MF   <=>  (THC)   <=>  (Z1)
(HC) ==> (H1),  and  (H1) without (HC)  <=>  E is MF but every faithful MF model has HS-null head.
```

The second alternative is exactly the situation of a norm-surviving head whose
`(-1)`-eigenspace has vanishing normalized rank. The corona-core reblocking of
`torsion-normal-generator-has-full-support-corona-core` would turn such a head
into one of positive density. It needs every generator of `E` to be a product
of conjugates of `w`, and `w` normally generates only `L`.

**Corollary 3 (class-kill: regularity is free).** Consider any constraint on
(H1)-models that follows from exact regularity of the limit trace. Examples:
- asymptotically regular isotypic multiplicities on finite windows of `L`;
- vanishing of `tau` off `L` (Corollary B of
  `jacobson-el-characters-are-symbol-or-finitary-extensions`);
- Haar or K-theoretic consistency data.

By Corollary 1, a model satisfying such a constraint exists as soon as any
MF model with `limsup ||rho_k(w) - 1||_2 > 0` exists. So an argument that
refutes (H1) gains nothing from the regularity hypothesis. It must show
that a positive-HS-mass head is impossible in operator-norm models.

It also cannot be a universal tracial identity, by
`jacobson-head-collapse-is-not-a-universal-tracial-identity`. It must use
operator-norm information that the tracial ultraproduct forgets.

**Rank two.** For `n = 2`, `E` is LEF (`binary-jacobson-el2-is-lef`), so
(Z2) holds: regular traces of finite groups realize `delta_e`. The law is
therefore sharp. For `n >= 4` the finite-model analogue of (Z1) holds: every
finite image kills the head (`cohn-elementary-group-is-not-lef`), so the
regular traces of finite groups never approximate `delta_e`. (ZO) asks
whether the same happens with operator-norm models.

**Verification.** The script
`experiments/jacobson-mf-zero-one-2026-09-17/check_transvection_facts.py`
checks the finite inputs:
- `x_13(Q)` and `x_13(SQ)` are commuting transvections with a transvection
  product;
- there is an explicit conjugator;
- all transvections of `GL_3(F_2)` and `GL_4(F_2)` form one class (21 and
  105 elements);
- all 63 nonzero elements of `<x_13(S^a Q) : a < 6>` are transvections.

The script exits 0.
