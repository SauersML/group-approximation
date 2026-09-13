---
rg: 2
id: thompson-f-character-simplex
kind: claim
title: The extreme characters of Thompson's F are the regular character and the characters of its abelianization
distinct_from:
  thompson-v-character-simplex: that classifies the characters of the simple group V, where only the trivial and regular characters occur; this is F = F_(2,1), whose other extreme characters are the scalar characters of the abelianization Z^2.
---

**ESTABLISHED by citation.** Let `F = F_(2,1)` be Thompson's group, with abelianization
`ab : F -> Z^2`. Every indecomposable character of `F` is either the regular character `tau_reg`
or `g -> rho(ab(g))` for a homomorphism `rho : Z^2 -> T`.

So every character of `F` (normalized positive definite class function) is
`t tau_reg + (1 - t) chi_ab` with `t in [0,1]` and `chi_ab` a character through `ab`, by Choquet
decomposition. In particular every character takes one value `1 - t` on all of `F' \ {e}`.

Consumer: `thompson-f-sofic-iff-relator-system-unstable`.
