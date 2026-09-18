---
rg: 2
id: kl-kernel-lies-in-the-compact-unitary-width-radical
kind: claim
title: Every Kervaire--Laudenbach kernel lies in the compact unitary relator-width radical, the radical over quotients of algebraic unitary ultraproducts
distinct_from:
  nonsingular-equations-preserve-matrix-certificates: that bounds the operator and normalized HS displacement of a killed old word by the old-relator cost; this puts the killed word, in every dimension, inside a bounded product of U(d)-conjugacy classes of the relator images, which gives every conjugation-invariant length inequality at once (rank included), and it identifies the resulting radical exactly.
  nonsingular-adjunction-preserves-approximation-radicals: that conserves the MF and hyperlinear radicals separately; this is one radical contained in both, described by a finitary width condition and shown equal to the radical over abstract quotients of algebraic ultraproducts of unitary groups.
  fp-simple-weak-soficity-is-finite-field-linear-soficity: that is relator width over all finite groups, which bounds weak soficity; this is relator width over the compact groups U(d), with conjugators in U(d), which bounds a Kervaire--Laudenbach kernel. Neither width bound implies the other.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that is width in finite classical groups under a non-linear-soficity hypothesis; this is width in compact unitary groups, forced by a nonsingular equation that kills a coefficient.
  kl-leavitt-identity-size-is-bounded-by-hs-escapes: that reads the HS inequality as a size fence for Leavitt identities; this is the conjugacy-class form for every countable presented group, together with the matching radical characterization.
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

**ESTABLISHED** by `kl-kernel-compact-unitary-width-radical-proof`.

**Notation.** Let `Gamma = <S | R>` be a countable presented group and `a in F(S)`.
For `d >= 1`, `U in U(d)^S`, a finite `R_0 <= R` and `K >= 0`, let

```text
Cons_K(R_0(U)) = { products of at most K elements g r(U)^(+-1) g^(-1) : g in U(d), r in R_0 },
```

with the empty product `I`. Say `a` has **bounded compact unitary width** if
some finite `R_0` and some `K` satisfy `a(U) in Cons_K(R_0(U))` for **every** `d`
and **every** tuple `U in U(d)^S`. Let `Rad_cw(Gamma)` be the image in `Gamma` of the set of
such words.

## Statement

**(A) Finitary certificate.** Let `w in Gamma * <t>` have nonzero `t`-exponent sum,
and suppose `a` dies in `H = (Gamma * <t>)/<<w>>` through an identity in `F(S u {t})`,

```text
a = prod_(j=1..A+B) v_j f_j^(eps_j) v_j^(-1),     f_j in R_0 or f_j = w,
```

with `A` factors taken from a finite `R_0 <= R`. Then for every `d` and every `U in U(d)^S`,

```text
a(U) in Cons_A(R_0(U)).                                            (CW1)
```

In particular `ker(Gamma -> H) <= Rad_cw(Gamma)`, whatever the equation is.

**(B) The radical, intrinsically.** For countable `Gamma` and `a in F(S)`, the following are equivalent:
- (i) `a` has bounded compact unitary width;
- (ii) every homomorphism from `Gamma` to an abstract quotient `(prod_(i in I) U(d_i))/N` with
  `N >= N_omega = { x : {i : x_i = I} in omega }` for some ultrafilter `omega` on `I` kills `a`.

So `Rad_cw(Gamma)` is a normal subgroup that does not depend on the presentation. It is
the common kernel of all homomorphisms into quotients of algebraic ultraproducts of
finite-dimensional unitary groups.

**(C) Every invariant length at once.** If (i) holds with constants `(R_0, K)`, then for every
family of conjugation-invariant, symmetric, subadditive functions `l_d : U(d) -> [0, infinity]`
with `l_d(I) = 0`,

```text
l_d(a(U)) <= K max_(r in R_0) l_d(r(U))        for all d and U.   (CW2)
```

Conversely, if (CW2) holds with the same `(R_0, K)` for all such families, then (i) holds with
`(R_0, K)`: for fixed `d` and `U`, apply it to the covering length by `R_0(U)`-conjugates in `U(d)`.

## Consequences

- **Where a kernel can live.** Taking `l_d` as operator-norm distance, normalized HS distance,
  normalized or unnormalized rank of `g - I`, or Schatten-`p` norm of `g - I` (each is
  conjugation-invariant, symmetric and subadditive, since `gh - I = g(h - I) + (g - I)`), (CW2) shows
  `Rad_cw(Gamma) <= Rad_MF(Gamma) cap Rad_hyp(Gamma)`, and also inside the radical of every
  rank-ratio or Schatten-`p` unitary approximation. Section 7 of the artifact localizes a
  possible kernel in `Rad_MF cap Rad_hyp`. This sharpens that to one radical, below every
  unitary invariant-length radical, with a width description.
- **Simple coefficient groups: a dichotomy.** If `Gamma` is simple and nontrivial,
  `Rad_cw(Gamma)` is `1` or `Gamma`. Exactly one of the following holds:
  - `Gamma` embeds in a quotient of an algebraic ultraproduct of the groups `U(d)`, and then
    Kervaire--Laudenbach holds over `Gamma`;
  - every element of `Gamma` has bounded compact unitary width.
- **What a counterexample must do.** A nonsingular equation killing `a != 1` over any
  `Gamma` forces a single constant `K` such that `a(U)` is a product of `K` conjugates of
  relator images in **every** unitary tuple of **every** dimension. Near-representations in
  any unitarily invariant sense and low-rank near-representations are all excluded for `a`
  simultaneously.
- **Global form.** Radicals of this kind shrink on subgroups: a homomorphism from the
  bigger group restricts. So `Rad_cw(U_ac) = 1` for the universal finitely presented
  acyclic group of `kl-holds-iff-it-holds-over-one-fp-acyclic-group` would give the
  Kervaire--Laudenbach conjecture over every recursively presented coefficient group. No
  route to the conjecture node is recorded here.

## Model test

- *Trivial model.* For a hyperlinear or MF `Gamma`, near-representations make (CW2) fail
  for every `a != 1`, so `Rad_cw = 1` and (A) says nothing new, as expected.
- *Singular control.* `Gamma = C_2 = <a | a^2>`, `w = t a t^(-1)`: `a = t^(-1) w t` has `A = 0`.
  (CW1) would force `a(U) = I` for all `U`, which is false. This is consistent, because
  `deg_t w = 0` and no root exists: nonsingularity is used.
- *Converse limitation.* (B) characterizes the radical over ultraproduct-type quotients.
  Over an arbitrary normal subgroup of `prod U(d_i)` that contains no `N_omega`, the
  pattern-selection step of (i) => (ii) fails. For those targets only the inclusion
  `ker q <= Rad` of `nonsingular-adjunction-preserves-approximation-radicals` is recorded.
