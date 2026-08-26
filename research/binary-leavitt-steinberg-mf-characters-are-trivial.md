---
rg: 2
id: binary-leavitt-steinberg-mf-characters-are-trivial
kind: claim
title: Every MF character of the binary Leavitt Steinberg group is trivial
distinct_from:
  simple-torsion-non-mf-iff-trivial-mf-characters: that is an established abstract equivalence under simplicity; simplicity of the literal Steinberg central cover is not an established input here, and the present claim is the unresolved character-rigidity statement itself.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that rules out nonzero finite parabolic character orbits; diffuse invariant measures, including the Haar profile, remain possible.
---

**OPEN.**  For

```text
R=L_(F_2)(1,2),              Delta=St_20(R),
```

prove that every pointwise trace limit of operator-norm asymptotic unitary
representations of `Delta` is the trivial character.

This is the exact character form of the Property-`(T)`-free MF endpoint.
Finite parabolic-orbit exclusion is insufficient: the row-root spectral
measure may be diffuse, and the regular/Haar profile satisfies every fixed
finite additive-rank window.  A proof must use operator-norm corona structure
and coefficient-sensitive relations strongly enough to exclude that profile.

This claim does not assert simplicity of `Delta` and does not identify its
Steinberg kernel with zero.

## Attempts

Diracization reduces any nontrivial MF character to one whose restriction to
a full root module is the Haar profile; see
`binary-leavitt-haar-row-excludes-mf-characters`.  The remaining leaf is
`binary-leavitt-haar-row-profile-is-not-mf-character-restriction`.  Generic
compression, finite character orbits, and bounded rank windows all fail on
the explicit countermodels in the Property-`(T)`-free audit.
