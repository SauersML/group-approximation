---
rg: 2
id: bounded-factor-width-from-almost-simple-quotient-bound
kind: route
title: Bounded composition factors bound the almost simple quotients of the generated subgroup, so the Nikolov-Segal width bound applies
target: simple-nonsofic-width-over-bounded-composition-factor-groups
requires: [relator-width-bounded-by-almost-simple-quotients]
---

Let `G = <X | R>` be an infinite finitely presented simple group. Its only finite quotient is trivial, since a
nontrivial finite quotient would be all of `G`. Nonsoficity is not used.

Fix `m`. Let `M(m)` be the largest `|Aut(S)|` over non-abelian simple groups `S` of order `<= m`, or `1` if there are
none. Let `Q` be a finite group whose composition factors have order `<= m`, and `a in Q^X`.

- **The generated subgroup.** The composition factors of `<a>` are among those of `Q`, by Jordan--Hölder applied to a
  composition series of `Q` intersected with `<a>`. So they have order `<= m`.
- **Its almost simple quotients.** Let `<a>/T` be almost simple with socle `S`. Then `S` is a composition factor of `<a>/T`, hence of
  `<a>`, so `|S| <= m`. Also `<a>/T <= Aut(S)`, so `|<a>/T| <= M(m)`.
- **Apply item (c)** of `relator-width-bounded-by-almost-simple-quotients` with `M = M(m)`. It gives `w(a) <= Phi(G, M(m))`
  in `<a>`. Conjugators in `<a>` are conjugators in `Q`. So `K(G, m) = Phi(G, M(m))` works.
