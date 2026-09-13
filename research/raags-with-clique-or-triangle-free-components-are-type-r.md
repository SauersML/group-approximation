---
rg: 2
id: raags-with-clique-or-triangle-free-components-are-type-r
kind: claim
title: A RAAG whose defining graph has only complete or triangle-free components is of Rips type R
distinct_from:
  triangle-free-raags-are-rips-type-r: that covers graphs with no triangle at all; this also allows components that are complete graphs of any size, e.g. Z^3 * Z
---

Let `Γ` be a finite simplicial graph each of whose connected components is
either a complete graph or triangle-free. Then `(A_Γ, V(Γ))` is of type R:
`R_r(A_Γ, V(Γ))` is contractible for every sufficiently large `r`.

Examples: `Z^3 * Z`, `Z^4 * F_2 * (F_2 × F_2)`. The first case it does not
cover is a connected graph that contains a triangle and is not complete.

Proof: route `raags-with-clique-or-triangle-free-components-are-type-r-proof`.
