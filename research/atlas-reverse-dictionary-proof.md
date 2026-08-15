---
rg: 2
id: atlas-reverse-dictionary-proof
kind: route
title: The same refinement mechanism, run backward through the join code
target: atlas-reverse-dictionary
requires: [atlas-rank-five-dictionary]
---

# The same refinement mechanism, run backward through the join code

Each atlas transvection is a rank-three root element
`1 + γ_i c γ_j^*` over the chart codes; refining through the join code
`E` rewrites `γ_i c γ_j^*` as a sum of terms `E_k b E_l^*` with `b` in
the five-letter coefficient set, i.e. as a product of commuting
`x_kl(b)` — the parent–suffix identity of `atlas-rank-five-dictionary`
read right-to-left.  For eight of the twelve generators the refinement
has a single term (the transvection's support is one join leaf on each
side), giving `x_kl(1)` on the nose; the four two-term cases split along
the two children of a rank-three leaf.  Commutation of the factors in
those four cases holds because the two terms share their row leaf and
have distinct column leaves (relation (St2) territory), so the product
is well defined without ordering care.

Verification is executable: `experiments/atlas_relator_rank5_reverse.py`
builds each candidate word, evaluates it by exact binary Leavitt
arithmetic, and compares with the atlas generator matrix; all twelve
pass.  The recipe table is in the artifact.
