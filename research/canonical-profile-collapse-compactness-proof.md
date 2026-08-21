---
rg: 2
id: canonical-profile-collapse-compactness-proof
kind: route
title: Diagonalize failed finite canonical windows into one canonical trace microstate sequence
target: canonical-profile-collapse-compactness
requires: []
---

Enumerate the relators and all words in `F(S)`. If the finite-window statement
fails for some `epsilon_0`, choose `U_n` with defect below `1/n` on the first
`n` relators, trace error below `1/n` from `tau_Gamma` on the first `n` words,
and `||p(U_n)||_2>=epsilon_0`. This is a canonical-profile microstate sequence
contradicting `(CPC1)`.

Conversely, any canonical-profile sequence eventually satisfies each fixed
finite window and tolerance. Applying the local implication for each
`epsilon>0` gives `(CPC1)`.

No algorithm must decide whether a word is trivial in `Gamma`: the canonical
values are used only in this semantic compactness proof, not by the later
proof-enumeration fixed-point program.
