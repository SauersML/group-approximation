---
rg: 2
id: rstar-core-character-profiles-induce-an-exact-affine-cover
kind: claim
title: Core character profiles induce an exact finite affine cover of every R-star pp relation
distinct_from:
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that rules out one cap profile covering a full nonaffine relation; this identifies the exact finite union of affine pieces supplied by all core profiles.
  rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel: that reduces operator modification to the kernel; this describes the visible relations selected by its seven-character profiles.
  fano-cap-witness-sections-force-source-affine-safety: that gives the necessary hull condition for a positive support; this strengthens it, for a fixed gadget, to containment in one explicitly enumerable affine piece.
---

**ESTABLISHED.**  Fix a finite pp gadget over `R_*`, pin its visible
variables, and let its pinned two-tail kernel have `k` rows.  For each core
character profile

```text
beta in (F_2^3 minus {0})^k,                            (RAC1)
```

add the corresponding maximal-cap equation to every core row.  Reverse
two-tail peeling adds a fixed coordinate character to every noncore row.
Let `A_beta` be the projection to the visible variables of the resulting
binary affine system.  Then

```text
A_beta is affine,        A_beta subseteq C,
C = union_beta A_beta,                                      (RAC2)
```

where `C` is the relation pp-defined by the original gadget.

Moreover a set `S subseteq C` has a deterministic cap-valued witness section
through this gadget if and only if

```text
S subseteq A_beta                                         (RAC3)
```

for at least one core profile `beta`.  Thus the exact compatibility problem
is a finite affine-cover containment test on only the dense kernel.  The
weaker condition `Aff(S) subseteq C` is necessary but is not sufficient; see
`source-affine-safety-does-not-imply-rstar-profile-compatibility` for a
three-row certificate.

For the constraintwise Culf--Mastel lift, the same criterion applies to the
positive source support in each constant-size source context: containment in
one `A_beta` lets one choose witnesses below its positive source atoms and
build a perfect cap-supported lifted trace.  Auxiliary sets for distinct
source contexts are disjoint away from visible overlaps, so these local
choices preserve the classical homomorphism's overlap agreement.
