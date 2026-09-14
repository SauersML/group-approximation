---
rg: 2
id: amenable-envelope-magnus-piece-one-relator-sofic
kind: claim
title: An amenable envelope of the Magnus piece over a Magnus subgroup makes a one-relator group sofic
distinct_from:
  peelable-extreme-one-relator-groups-are-sofic: that is the syllable criterion; this is the structural criterion it specializes, and it also covers unpeelable relators with nested conjugators such as four-syllable extremes.
  unpeelable-extreme-one-relator-groups-sofic: that is the open remainder after syllable peeling; this closes the part of that remainder whose Magnus piece embeds over a Magnus subgroup into an amenable-edge envelope.
  triangular-conjugate-bs-chains-are-sofic: that treats relators of Baumslag--Solitar conjugator shape over infinite generating sets; this is a criterion on the single Magnus piece of an arbitrary two-generator relator.
artifacts:
  - research/artifacts/amenable-envelope-magnus-piece-sofic-2026-09-11.md
---

ESTABLISHED (written proof; not Lean-checked). Let `G = <a,t | w>` be
torsion-free, with `t` of exponent sum zero in `w` and Magnus rewriting
`W_0(a_m,...,a_n)`, `m < n`. Put `B_0 = <a_m,...,a_n | W_0>` and
`F_- = <a_m,...,a_(n-1)>`.

An **amenable envelope** of `(B_0, F_-)` is an injective map `B_0 -> B'`,
where `B'` is obtained from the image of `F_-` by finitely many amalgams
`Y *_E X` over amenable `E` with sofic `X`, and HNN extensions over amenable
associated subgroups.

**Theorem.** If `(B_0, F_-)` or `(B_0, F_+)`, with
`F_+ = <a_(m+1),...,a_n>`, has an amenable envelope, then `G` is sofic.

The Magnus truncations `S_j = S_(j-1) *_(F_j) B_j` embed step by step into
`S'_j = S'_(j-1) *_(F_j) B'_j`, by amalgam monotonicity. Each `S'_j` comes
from `S'_(j-1)` by the envelope's amenable-edge moves, so it is sofic.

Peelable extremes are the case in which `B_0` is its own envelope. The
criterion also covers unpeelable relators such as
`a_n U a_n^(-1) X a_n U^(-1) a_n^(-1) Z`, with four top syllables, built by
two cyclic HNN extensions.

It stops at an exact wall. If `n - m >= 2` and `B_0` is not free, an envelope
forces a nontrivial splitting of `B_0` over amenable subgroups with `F_-`
elliptic. So Magnus pieces that are rigid relative to `F_-` are out of reach
of this method.
