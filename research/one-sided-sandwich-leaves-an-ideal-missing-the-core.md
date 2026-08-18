---
rg: 2
id: one-sided-sandwich-leaves-an-ideal-missing-the-core
kind: claim
title: A one-relation sandwich makes the chosen element full and still admits a proper ideal disjoint from the coefficients
invalidates: [boone-higman-via-sandwich-ring-simplicity]
distinct_from:
  universal-sandwich-ring-is-finitely-presented-and-injective: that is the positive half -- adjoining the sandwich relation universally preserves the embedding and finite presentability; this is the negative half, that the same relation does not make the extension simple, and the two are stated separately because only the first is used constructively.
  division-ring-hosts-no-binary-leavitt-family: that forbids a binary Leavitt family inside a division ring, a nonembedding statement about a fixed class of hosts; this exhibits a proper ideal in a specific one-relation ring and says nothing about division rings.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness in the binary Leavitt algebra, an equation xy=1 with yx!=1 used as an approximation obstruction; this uses the same shape of one-sided inverse but to produce an IDEAL missing the coefficient core, and its conclusion is about simplicity, not direct finiteness.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Fullness of one element does not propagate to simplicity, and the witness is
the smallest possible case.

Let `k` be a field, `R = k`, `r = 1`, so that the universal sandwich ring of
`universal-sandwich-ring-is-finitely-presented-and-injective` is the Toeplitz
algebra

    T = k<p, q | p q = 1> .

Then `T` has a nonzero proper two-sided ideal `J` with `J ∩ k = 0`.

## Why it matters for the Boone-Higman ring lane

`normal-generation-makes-the-augmentation-ideal-one-generated` shows that
once one `1 - t` is full, every `1 - s` with `s` in the simple core is full.
It is tempting to read that as "the extension is simple, or nearly so".  It
is not.  Both statements control only ideals that **meet the coefficient
core**, and this claim exhibits an ideal that does not.

The structure is the exact ring mirror of
`proper-normal-subgroups-miss-the-normally-generating-core`: there, every
proper normal subgroup avoids the simple core, and the core's survival says
nothing about how large the proper normal lattice is; here, a proper ideal
avoids the coefficient ring, and fullness on the coefficients says nothing
about how large the proper ideal lattice is.  In both cases the core is
invisible to exactly the objects one needs to control.

## Why the obvious repair is not one

Adding the reverse relation `q r p = 1`, to make `r` genuinely invertible
rather than one-sided invertible, is dangerous rather than free.  Forcing a
noncommutative element such as `1 - g` to be invertible can collapse the
embedded group ring, particularly in the presence of torsion, and injectivity
of such a universal localization is a theorem to be proved case by case, not
a formal consequence of the universal property.  The factorization argument
of `universal-sandwich-ring-proof` does
not survive it: there is no longer a supplied target `B` in which both
relations hold.
