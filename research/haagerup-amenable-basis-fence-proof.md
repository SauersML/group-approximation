---
rg: 2
id: haagerup-amenable-basis-fence-proof
kind: route
title: Intertwine the rigid subfactor into the amenable base
target: haagerup-actor-amenable-basis-rigidity-fence
requires:
  - haagerup-factor-direction-strips-from-property-t-envelope
---

Apply `haagerup-factor-direction-strips-from-property-t-envelope` with the
complementary actor trivial.  If a property-`(T)` factor `Q` embeds in
`B rtimes Gamma`, Popa's Haagerup Fourier multipliers and intertwining
criterion give `Q prec B`.  Thus a nonzero corner of `Q` embeds normally in a
matrix amplification of a corner of `B`.

Amenability passes to matrix amplifications, corners, and von Neumann
subalgebras, so that corner of `Q` is amenable.  A factor is amenable iff one
nonzero corner is amenable; hence `Q` is amenable.  A diffuse property-`(T)`
finite factor is not amenable, contradiction.  Since `L(K)` is amenable for
amenable `K`, the group-basis application follows.

