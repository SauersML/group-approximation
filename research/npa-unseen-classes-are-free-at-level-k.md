---
rg: 2
id: npa-unseen-classes-are-free-at-level-k
kind: claim
title: No row of a level touches that level's own exceptional alternating classes
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

For every `k >= 2`, every row of `Phi_k` has coefficient zero on each of the four
exceptional classes of the level-`k` shell,

```text
U_1 = (empty, r_(2k-1)),   U_2 = (empty, 0 r_(2k-1)),
U_3 = ((0), r_(2k-1)),     U_4 = ((1), r_(2k-1)).
```

Equivalently the corresponding coordinate directions are free: they may be varied
without leaving `ker Phi_k`.

**This is the lemma the whole programme stops at.**  It is asserted inside the
imported germ step -- "since unseen coordinates are free at level `k`,
extendability is never obstructed" -- on the basis of an exact analysis of the
transitions `2->3`, `3->4` and `4->5`, and it is asserted again, without proof,
at the point where the shell induction needs it for general `k`.  The dossier
that built the induction has since withdrawn its closure claim on exactly this
point.

The gap is specific and worth stating precisely, because it is easy to think the
triangular argument already covers it.  What the shell classification proves is
that the exceptional classes carry **no pivot**: no row has one of them as its
unique term of maximal degree.  What is needed is that no row **touches** them at
all.  These differ because `r_(2k-1)` has degree `2k-1`, strictly below the top
degree `2k` at level `k`, so a row may perfectly well lead at degree `2k` and
carry a nonzero tail on an exceptional class.

## Attempts

The proposed attack, from the dossier author and not yet written out: the support
words of the `T/D` relation lattice have an endpoint-parity property, and no
product of two such supports can produce one of the four exceptional alternating
classes without either leaving a trailing `0` -- which reduces the word and moves
the term off the class -- or admitting a cancellation that lowers the degree.
Making this precise means classifying, for each exceptional class `U`, all pairs
`(p,q)` of level-`k` basis words with `p* q` in `U` after reduction, and checking
that every one of them makes the corresponding coefficient of
`R_p^T Gamma_k R_q` cancel.  That is a finite parity computation per class and
looks tractable; nobody has done it.

Note the parity property has to do real work at *both* degrees, since `U_2` sits
at degree `2k` while `U_1, U_3, U_4` sit at `2k-1`, and the trailing-`0`
mechanism is what distinguishes them.

A cheaper falsification test, not run: for `k = 4, 5`, enumerate all rows of
`Phi_k` and grep the four exceptional columns for a nonzero entry.  If any is
nonzero the lemma is false as stated and the induction fails at the first
non-inductive step, which would be worth knowing before anyone writes the parity
argument.  The claim is currently supported only by the source's own
`explore_r1_induction.py` over three transitions, and the verifier supplied with
the dossier never tests it.

Superseding attack: see the pairing-against-kernel-vectors alternative recorded
in `npa-two-residual-rows-independent-mod-old-rows`, which would make this lemma
unnecessary for the upper bound.  If that works, this claim keeps only its
independent interest as a statement about the shell structure.
