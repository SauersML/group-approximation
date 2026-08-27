---
rg: 2
id: hs-stable-finite-bi-index-kazhdan-pair-exists
kind: claim
title: There is an infinite finite-bi-index Kazhdan subgroup pair with a same-dimension HS-stable acting group
distinct_from:
  uniform-hs-site-coherence-for-finite-bi-index-pair: that states the operational rounding property needed by the Clifford tape; this asks for a structural package which implies it by a separate theorem.
  ck-envelope-simple-core-has-finite-bi-index: that asks to alter one Boone--Higman envelope so its simple core has finite bi-index; this additionally requires a Kazhdan stabilizer and normalized-HS stability of the ambient acting group.
---

Find an explicit finitely presented group `L` and an explicit finitely
generated infinite-index subgroup `H<L` such that

```text
|H\L/H| < infinity,
H has property (T),
L is same-dimension normalized-HS stable.                         (HFK1)
```

The stability statement must have a quantitative modulus uniform over matrix
dimension and must remain valid after restriction to an almost invariant
positive-density spectral block.

The ambient group is necessarily nonamenable by
`finite-bi-index-kazhdan-subgroup-forces-nonamenability`.  For a noncircular
solution it must also avoid the known Becker--Lubotzky obstruction: an
infinite hyperlinear property-(T) group is not same-dimension normalized-HS
stable.  Thus one is looking for a nonamenable, non-property-(T), HS-stable
ambient group containing the Kazhdan stabilizer, unless the ambient group is
already nonhyperlinear and the main problem has been solved earlier.
Moreover `H` cannot be a retract of `L` in the noncircular hyperlinear case:
same-dimension HS stability descends to retracts, while an infinite
hyperlinear property-(T) group is HS-unstable.

There is now a second compulsory screen.  By
`hyperlinear-hs-stable-is-residually-finite`, a hyperlinear ambient `L` with
the required strict stability must be residually finite.  Any proposed
non-residually-finite ambient already solves the root by itself if its
stability proof is correct; it is not a cheaper input to the tape.  This
excludes the standard infinite simple/highly transitive envelopes from the
noncircular search.

## Attempts

- Finite stabilizers are unusable: in an infinite transitive finite-rank
  action a finite point stabilizer cannot be transitive on an infinite
  off-diagonal orbit.
- Standard arithmetic parabolics have a finite Bruhat decomposition over the
  ambient field, but their intersections with finitely generated arithmetic
  groups generally acquire infinitely many integral double-coset invariants.
- Known finitely presented highly transitive groups provide finite pair-orbit
  actions, but no same-dimension normalized-HS stability theorem for the
  acting group or Kazhdan theorem for the point stabilizer is available.
- Higher-rank stability candidates provide the right spectral rigidity, but
  ordinary same-dimension stability of an infinite hyperlinear property-(T)
  ambient is ruled out by Becker--Lubotzky.  Flexible stability would require
  a new carrier-preserving version of the coherence theorem and is already
  close to the known conditional nonhyperlinear-central-extension route.
- Split extensions and free products with a retraction onto `H` are ruled out
  by `hs-stability-descends-to-retracts`; any viable inclusion must be
  genuinely nonsplit.
- Non-residually-finite highly transitive and Thompson-like ambient groups are
  also not neutral candidates: strict HS stability would make them
  nonhyperlinear immediately.  The genuinely auxiliary search is therefore
  for a residually finite, nonamenable, non-Kazhdan stable `L` with a
  nonretract Kazhdan stabilizer of finite bi-index.
