---
rg: 2
id: gl-n-q-explicit-via-steinberg-group-of-resolvent-ring
kind: route
title: The Steinberg group St_(6n+7)(R_L) of the Leavitt resolvent ring is a finitely presented overgroup of GL_n(Q)
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - leavitt-pairs-embed-sl-n-q-in-steinberg-groups
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - steinberg-finite-presentation-and-kazhdan-theorem
---

Let `n >= 2`. Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
with 6 generators and 9 relations. Put `Γ_n = St_(6n+7)(R_L)`.

1. **Finitely presented.** `R_L` is a finitely presented unital ring and `6n+7 >= 4`, so
   `Γ_n` is finitely presented (`steinberg-finite-presentation-and-kazhdan-theorem`). By the
   same node it has property (T).
2. **Contains GL_n(Q).** `Q ⊆ R_L` unitally (part 1 of the ring node), and the generators
   `s_1, s_2, t_1, t_2` satisfy `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`, so they form a
   Leavitt pair (`x_i = s_i`, `y_i = t_i`). By `leavitt-pairs-embed-sl-n-q-in-steinberg-groups`
   with `N = n+1`, `SL_(n+1)(Q)` embeds in `St_(6n+7)(R_L)`. So does
   `GL_n(Q) ≤ SL_(n+1)(Q)`, via `g -> diag(g, det(g)^(-1))`.
3. **Explicit and natural.** `Γ_n` is the Steinberg group of a named ring given by an
   explicit finite presentation. It is not produced by running an embedding algorithm on a
   presentation of `GL_n(Q)`. That is the sense of "natural" in
   `gl-n-q-explicit-natural-fp-overgroup`.

What this route does not give:
- **Not simple.** `Γ_n` maps onto `E_(6n+7)(R_L)`, so this route does not reach
  `gl-n-q-embeds-in-fp-simple-group`.
- **Presentation.** The finite presentation of `Γ_n` is the one the Steinberg
  finite-presentation theorem builds from that of `R_L`. It is not written out here.

Status: the first requirement is OPEN pending review, so the target is not yet reached.
