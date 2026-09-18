---
rg: 2
id: m2-envelopes-via-free-product-with-z
kind: route
title: Clapham envelope, then free product with Z; universality of one hyperaperiodic point of the envelope then gives (M2) for the new envelope
target: decidable-groups-embed-in-fp-groups-satisfying-m2
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-groups-have-universal-hyperaperiodic-points
  - free-products-with-z-inherit-m2-from-universal-points
---

**Route. OPEN.** One premise is open: `decidable-groups-have-universal-hyperaperiodic-points`.

**Argument.**
1. By `clapham-fp-embedding-preserves-word-problem`, `G` embeds in a finitely presented `Γ`
   with solvable word problem. Replace `Γ` by `Γ × Z` if `Γ` is finite; that is still finitely
   presented and decidable.
2. The open premise gives a computable point `y_Γ ∈ C^Γ` satisfying (H) and (U).
3. By `free-products-with-z-inherit-m2-from-universal-points`, `Λ := Γ * Z` carries a
   nonempty effectively closed minimal free subshift.
4. `Λ` is finitely presented. Its word problem is solvable, since free products of groups
   with solvable word problem are decidable by reduced normal forms. It contains `G`. ∎

**For GL_n(Q), BBMZ 5.3(5).** Take `Γ = St_10(R_L)`. It is finitely presented, has solvable
word problem (refereed, `leavitt-resolvent-k2-stability-holds`) and contains every `GL_n(Q)`.
The route gives (M2) for `St_10(R_L) * Z` as soon as `St_10(R_L)` has one (H)+(U) point.
`St_10(R_L)` itself is not residually finite (it has no finite quotients), so the Toeplitz
instance does not apply, and its own (M2) stays open.
