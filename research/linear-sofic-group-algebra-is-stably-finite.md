---
rg: 2
id: linear-sofic-group-algebra-is-stably-finite
kind: claim
title: A group linear sofic over a field has a stably finite group algebra over that field
distinct_from:
  growing-rank-decoder-is-linear-soficity: that identifies faithful growing decoders of one coefficient algebra with algebra linear soficity; this is the group-to-algebra passage over an arbitrary field and its finiteness consequence.
  kun-thom-wreath-stably-finite: that proves stable finiteness of the Kun--Thom wreath group algebras without any approximation property; this derives stable finiteness from linear soficity.
---

ESTABLISHED.  Let `F` be any field and `G` a countable group.  If `G` is
`F`-linear sofic, then `F[G]` embeds unitally and injectively in a
rank-metric ultraproduct `prod_omega M_(m_k)(F) / Ker rho_omega`, and
`F[G]` is stably finite.

**Consequence used in this graph.**  If `K[G]` is not stably finite for some
field `K`, then `G` is not `L`-linear sofic for any field `L` containing
`K`: the one-sided inverse pair in matrices over `K[G]` also lies over
`L[G]`.  In particular a failure of Kaplansky's direct finiteness conjecture
over `F_2` for `G` makes `G` non-linear-sofic over every field of
characteristic two.

It gives no information over characteristic zero, where Kaplansky proved
`K[G]` stably finite for every group.  Nor does it pass from `C` to a fixed
finite field; that passage is Arzhantseva--Paunescu Question 8.6, and their
Question 7.9 asks whether complex linear sofic groups satisfy Kaplansky's
conjecture at all.

See [[linear-sofic-group-algebra-stably-finite-citation]].
