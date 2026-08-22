---
rg: 2
id: finite-central-polynomial-commutant-no-go-proof
kind: route
title: Add a spectator factor outside every finitely named tape algebra
target: central-polynomial-tapes-do-not-exhaust-commutant
requires:
  - amplification-natural-words-cannot-read-packet-multiplicity
  - amplification-natural-block-size-selectors-cannot-be-tight
---

Under `U |-> U tensor I_l`, every fixed tape word and every matrix formed
from finitely many such words is tensored by `I_l`.  Therefore its abstract
generated algebra, PI degree, center, simple-factor list, and all fixed
central-polynomial evaluations are unchanged.  Schur's lemma, on the other
hand, gives the full commutant of the amplified packet as the old
commutant tensored with `M_l`.  The spectator factor is real ambient matrix
data but is absent from the named word algebra.

Induct on any finite sequence of newly named commuting tape packets.  Their
amplifications remain identity on the same spectator factor, so no finite
stage generates it.  This proves `(FCP3)--(FCP4)` and the failure of full
commutant authentication.
