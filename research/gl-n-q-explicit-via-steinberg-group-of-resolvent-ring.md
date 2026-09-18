---
rg: 2
id: gl-n-q-explicit-via-steinberg-group-of-resolvent-ring
kind: route
title: The Steinberg group St_(6n+7)(R_L) of the Leavitt resolvent ring is a finitely presented overgroup of GL_n(Q)
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - leavitt-pairs-embed-sl-n-q-in-steinberg-groups
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/gq-referee-a-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
  - research/artifacts/gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
  - research/artifacts/gq-steinberg-q-krstic-mccool-source.md
---

Let `n >= 2`, and let `R_L` be the six-generator, nine-relator ring of
`leavitt-resolvent-ring-is-fp-and-contains-q`. Put `Γ_n = St_(6n+7)(R_L)`.

1. **Finitely presented.** `R_L` is a finitely presented unital ring and `6n+7 >= 4`, so
   `Γ_n` is finitely presented (`steinberg-finite-presentation-and-kazhdan-theorem`;
   Krstić–McCool, Theorem 3, source record in
   `research/artifacts/gq-steinberg-q-krstic-mccool-source.md`). By the same node `Γ_n`
   has property (T).
2. **Contains GL_n(Q).** `Q ⊆ R_L` unitally, and `(s_1, s_2, t_1, t_2)` is a Leavitt pair.
   Apply `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` with `N = n+1`: `SL_(n+1)(Q)`
   embeds in `St_(6n+7)(R_L)`. So does `GL_n(Q)`, via `g -> diag(g, det(g)^(-1))`.

**Presentation.** By `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`,
`Γ_n = St_(6n+7)(F_6) / ⟨⟨x_12(ρ_1), …, x_12(ρ_9)⟩⟩`, where
`F_6 = Z⟨s_1, s_2, t_1, t_2, N, A⟩` and the `ρ_t` are the nine relators of `R_L`. Writing
`c(a,b) = [x_13(a), x_32(b)] = x_12(ab)`, the nine words are:
- `c(t_1,s_1) x_12(-1)`, `c(t_1,s_2)`, `c(t_2,s_1)`, `c(t_2,s_2) x_12(-1)`;
- `c(s_1,t_1) c(s_2,t_2) x_12(-1)`;
- `c(N,s_1) c(s_1,N)^(-1) x_12(-s_1)`, `c(N,s_2)`;
- `c(A,N) x_12(A) x_12(-1)`, `c(N,A) x_12(A) x_12(-1)`.

The finite presentation of `St_m(F_6)` itself is Krstić–McCool's. Its primary text was not
accessible (paywall), so it is not written out here.

**Remark on naturality.** `Γ_n` is the Steinberg group of a named ring with an explicit
presentation. It is not obtained by running an embedding algorithm on a presentation of
`GL_n(Q)`. Under the reading of "natural" recorded in `gl-n-q-explicit-natural-fp-overgroup`
(a matrix-type group over a named ring), it qualifies. How natural `R_L` itself is, is a
matter of taste.

**Not given.** `Γ_n` is not simple: it maps onto `E_(6n+7)(R_L)`. So this route does not
reach `gl-n-q-embeds-in-fp-simple-group`.
