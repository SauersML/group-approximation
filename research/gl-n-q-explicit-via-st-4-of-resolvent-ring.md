---
rg: 2
id: gl-n-q-explicit-via-st-4-of-resolvent-ring
kind: route
title: The single finitely presented group St_4(R_L) of the Leavitt resolvent ring contains GL_n(Q) for every n
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - one-steinberg-group-contains-every-gl-n-q
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - steinberg-finite-presentation-and-kazhdan-theorem
---

Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-and-contains-q`, with 6 generators
and 9 relations. Put `Γ = St_4(R_L)`, one group for every `n >= 2`.

1. **Finitely presented.** `R_L` is a finitely presented unital ring, so `Γ` is finitely
   presented (`steinberg-finite-presentation-and-kazhdan-theorem`, rank 4). By the same
   node it has property (T).
2. **Contains GL_n(Q).** `Q ⊆ R_L` unitally, and `(s_1, s_2, t_1, t_2)` is a Leavitt pair
   (`x_i = s_i`, `y_i = t_i`), both from the ring node. By
   `one-steinberg-group-contains-every-gl-n-q`, `SL_(4m)(Q)` embeds in `Γ` for every `m`,
   and so does `GL_n(Q) <= SL_(n+1)(Q) <= SL_(4m)(Q)` for `4m >= n+1`.
3. **Explicit.** `Γ` is the Steinberg group of a named ring with an explicit finite
   presentation, uniform in `n`. It is not produced by running an embedding algorithm on a
   presentation of `GL_n(Q)`. Existence of some finitely presented overgroup is classical
   (Higman), and Mikaelian (arXiv:2507.04347) announces explicit per-`n` overgroups. The
   claim is only that this construction is explicit, uniform in `n`, and plausibly natural;
   experts decide naturality.

This route differs from `gl-n-q-explicit-via-st-4-of-divisible-ring` only in the ring. It
uses `R_L`, whose ring node `gq-referee-b` checked, as `gq-referee-b` asked in its review of
`one-steinberg-group-contains-every-gl-n-q`.

What this route does not give:
- **Not simple.** `Γ` maps onto `E_4(R_L)`, whose centre contains `Q^x`
  (`non-ibn-rational-hosts-have-infinite-elementary-centre`). So it does not reach
  `gl-n-q-embeds-in-fp-simple-group`.
