---
rg: 2
id: commuting-lamp-quotient-not-mf
kind: claim
title: The commuting-lamp witness quotient is not MF
distinct_from:
  commuting-lamp-quotient-mf: That open claim asserts an injective corona representation of the same group exists; this one is its negation, established by composing two claims that were already in the graph.
  kun-thom-wreath-weak-mf: That claim concerns the Kun--Thom commuting-lamp wreath; this one settles the repository's own witness quotient, and its route applies verbatim to the Kun--Thom pair as well.
---

`W/<zeta>` is not MF: the two-lamp element
`ubar = c_{tau o} c_{v_1 tau o}` is nontrivial and lies in
`Rad_MF(W/<zeta>)`, so no corona representation is injective.

**Why this was invisible.**  The manuscript's wreath-product remark after
the involutive collapse theorem describes exactly this witness, and
`commuting-lamp-quotient-structure` identifies `W/<zeta>` as exactly such a
wreath product — but the two were never composed, because attention was
fixed on the `corona-commutant-no-growth` fork.  The fork was a false
dichotomy: its general form is refuted (`corona-commutant-growth-witness`)
AND the quotient is non-MF anyway, through the involutive collapse rather
than through commutant rigidity.

**Consequences.**  `Rad_MF(W) = q^{-1}(Rad_MF(W/<zeta>))` strictly exceeds
`<zeta>`; the level-one two-lamp defect is the first element beyond the
sign.  The same route decides `kun-thom-wreath-weak-mf` negatively —
`(sum_{G/Gamma} C_2) semidirect G` for any Kazhdan pair with a strict
one-sided compressor inside the ambient group.  The exact value of the
radical is the subject of `commuting-lamp-mf-radical-is-level-even`.
