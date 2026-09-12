---
rg: 2
id: amplification-natural-selector-no-go-proof
kind: route
title: Amplify one exact packet and force two size labels onto the same carrier
target: amplification-natural-block-size-selectors-cannot-be-tight
requires:
  - amplification-natural-words-cannot-read-packet-multiplicity
---

Choose any exact packet representation with nonzero multiplicity `k` and
amplify it by `I_l`, `l>1`.  Schur multiplicity changes from `k` to `kl`,
whereas every amplification-natural decoded projection is merely tensored
by `I_l`.  Correct authentication at size `k` therefore keeps the old
`P_k` equal to the full amplified carrier, while correct authentication at
size `kl` requires the new `P_(kl)` to equal that same carrier.  They cannot
be orthogonal.  The normalized-word amplification theorem supplies
`(ANS1)` for every static group-word or finite word-statistic construction.

