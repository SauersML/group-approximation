---
rg: 2
id: multiplicity-only-fanizza-row-selection-leaves-a-mirror
kind: claim
title: Every multiplicity-only Fanizza row selector leaves a balanced mirror on its selected block
invalidates:
  - finite-type-selector-authenticates-fanizza-row
distinct_from:
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that proves fixed congruence and divisibility conditions disappear after projectivizing the multiplicity cone; this permits an arbitrary nonfunctorial selector of the actual integer vector and defeats it after its choice is made.
  fixed-packet-hall-atlas-has-no-julia-cutoff-gap: that treats fixed linear rank and Hall inequalities over a rational packet polytope; this covers arbitrary selection rules, including dimension oracles, provided they only choose a reducing multiplicity block and add no chord-sensitive incidence there.
  existing-fanizza-mixed-menu-leaves-balanced-mirror-exit: that gives one global mirror for the already installed menu; this proves the mirror can be installed on whichever reducing block an arbitrary finite-coordinate type selector chooses.
---

**ESTABLISHED SELECTOR-ONLY NO-GO.**  Let a fixed exactified finite Fanizza
packet/reset chart act on a finite-dimensional space.  Permit a decoder to
inspect its complete integer multiplicity data and, by an arbitrary rule,
choose a nonzero reducing projection `Z` in the packet multiplicity algebra.
Assume the selected native cuts satisfy

```text
H_Z=HZ<=E_Z=EZ,       F_Z=E_Z-H_Z,
rank((1-E)Z)>=rank(HZ)>0.                              (MRS1)
```

The native reset ray has this complement capacity.  Suppose, as in the
current Fanizza menu, that no defining mixed relation acts nontrivially on
the chord's scalar multiplicity coordinate after `Z` has been chosen.  Then
there is an exact finite realization of all those relations for which

```text
||Z(R_F U R_E U^*-1)||_2^2=4 tr(HZ).                  (MRS2)
```

The conclusion is independent of how `Z` was selected.  In particular it
covers selectors based on the full irreducible multiplicity vector, fixed
integer flows, parity or divisibility, Hall solutions, lexicographic
first-hit rules, and the ambient matrix dimension itself.  Matrix-coordinate
selection alone therefore does not authenticate an oriented row.

This is not a no-go for a genuinely mixed finite-coordinate incidence.  It
identifies its necessary content: after selecting `Z`, some ordinary
presentation relation must see the chord action on `Z` and exclude the
equal-rank complement swap, while the exact infinite Hilbert-hotel model
must still satisfy that relation.  A decoder which merely selects a packet
block, followed by the existing relations, cannot work.

DERIVATION
multiplicity-only-fanizza-row-mirror-proof
