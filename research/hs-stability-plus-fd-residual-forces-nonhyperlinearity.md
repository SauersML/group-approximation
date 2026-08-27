---
rg: 2
id: hs-stability-plus-fd-residual-forces-nonhyperlinearity
kind: claim
title: Uniform normalized-HS stability plus a nontrivial finite-dimensional residual forces nonhyperlinearity
distinct_from:
  map-matricial-stability-non-mf: that assumes every finite-dimensional representation is trivial and concludes non-MF; this needs only one nontrivial word killed by every finite-dimensional unitary representation and targets canonical-trace hyperlinearity.
  schur-toeplitz-root-mark-is-fd-invisible: that proves finite-dimensional invisibility for one proposed Schur--Toeplitz mark but supplies no stability theorem for the ambient group.
  leavitt-steinberg-hs-stable: that asks for normalized-HS stability of one explicit group; this is the general implication that would turn such stability and one finite-dimensional-residual word into a nonhyperlinear witness.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

Let `Gamma=<S|R>` be finitely presented and uniformly flexibly stable in
normalized Hilbert--Schmidt norm: every sequence of finite-dimensional tuples
whose relator defects tend to zero is, after a relative dimension change
tending to zero, asymptotically close on `S` to genuine finite-dimensional
unitary representations of `Gamma`.

Suppose there is a word `w` such that

```text
w!=1 in Gamma,                                      (SFR1)
pi(w)=I for every finite-dimensional unitary pi.    (SFR2)
```

Then `Gamma` is nonhyperlinear.  Thus it is enough to find a finitely
presented uniformly HS-stable group whose finite-dimensional unitary residual
is nontrivial.  A nontrivial word in the ordinary finite residual suffices:
the image of a finitely generated group under a finite-dimensional linear
representation is residually finite, so every such representation kills that
word.

The statement is genuinely weaker than minimal almost periodicity.  Only the
chosen mark must disappear in exact finite matrices; other finite-dimensional
representations may be abundant.
