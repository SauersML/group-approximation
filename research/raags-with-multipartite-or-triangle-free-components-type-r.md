---
rg: 2
id: raags-with-multipartite-or-triangle-free-components-type-r
kind: claim
title: A RAAG whose graph components are complete multipartite or triangle-free is of Rips type R
distinct_from:
  raags-with-clique-or-triangle-free-components-are-type-r: that allows only complete components besides triangle-free ones; this allows every complete multipartite component, e.g. (F_2 × F_2 × F_2) * Z^3
---

Let `Γ` be a finite simplicial graph each of whose connected components is
complete multipartite or triangle-free. Then `(A_Γ, V(Γ))` is of type R.

Examples: `(F_2 × F_2 × F_2) * Z^3 * F_2`, `(Z^2 × F_2) * (F_2 × F_2)`.

UNREVIEWED (it rests on `complete-multipartite-raags-are-rips-type-r`).
Proof: route `raags-with-multipartite-or-triangle-free-components-type-r-proof`.

The first graphs not covered are connected, contain a triangle, and are not
complete multipartite. Equivalently, the complement graph has an induced path
on three vertices within the component. The smallest example is the triangle
with a pendant vertex, `A_Γ = Z × (Z^2 * Z)`.
