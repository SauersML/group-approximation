---
rg: 2
id: ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient
kind: claim
title: A finite-phase projective-kernel face excluding CE traces gives a nonhyperlinear quotient
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  projective-kernel-face-gap-compactifies-phase-safely: that compactifies exclusion of finite-dimensional vector states but still needs a finite-game testability theorem; this uses the stronger CE-tracial exclusion and produces the group directly.
  phase-safe-toric-gap-implies-nonhyperlinear: that starts with a finite nonlocal game and obtains a CE contradiction from its qa gap; this needs no game and starts directly from a normal finite-phase character face.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that proves one non-CE trace need not exclude other CE states in its projective-kernel face; this assumes precisely that whole-face exclusion and identifies its group-theoretic payoff.
---

**ESTABLISHED.**  Let `G` be finitely presented, let `K normal G`, and let

```text
chi:K -> mu_q                                             (CEF1)
```

be conjugation invariant.  Let `T_CE(G)` be the weak-star compact set of
tracial states on `C*(G)` with Connes-embeddable GNS algebra.  If

```text
F_(K,chi) intersect T_CE(G)=empty,                       (CEF2)
```

then there is a finite `F subset K` for which

```text
Q_F=(mu_q x G)/normalClosure({(chi(k)^(-1),k):k in F})  (CEF3)
```

is a finitely presented nonhyperlinear group.  The central copy of `mu_q`
embeds in `Q_F`.

Indeed, compactness of `T_CE(G)` gives a finite `F` whose fixed face is
already disjoint from `T_CE(G)`.  The full graph of `chi` is normal and meets
`mu_q` trivially, so the normal closure in `(CEF3)` stays in that graph and
the phase embeds.

If `Q_F` were hyperlinear, `L(Q_F)` would be Connes embeddable.  Cut by the
central Fourier projection for the defining character of `mu_q`.  The
normalized corner trace pulls back to a CE tracial state on `C*(G)` satisfying

```text
phi(conjugate(chi(k))k)=1,       k in F,                (CEF4)
```

contradicting the finite face separation.  Thus `Q_F` is nonhyperlinear.

This theorem removes finite-game testability entirely, but it makes the true
cost explicit: proving `(CEF2)` already exhibits a finite phase-safe central
extension quotient whose character corner has no CE trace.  It is not a
formal consequence of one non-CE monomial trace.

