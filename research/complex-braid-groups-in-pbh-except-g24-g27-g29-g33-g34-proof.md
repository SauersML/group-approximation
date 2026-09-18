---
rg: 2
id: complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34-proof
kind: route
title: Run through the Shephard--Todd classification; rank two by the Hopf bundle, G(de,e,n) by coverings of Conf_n(C^×) and the one-cone-point bundle, exceptional types through Artin groups and Bessis's regular centralizers
target: complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34
requires:
  - imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class
  - spherical-artin-groups-satisfy-permutational-boone-higman
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

Write `P(W) = π_1(V^reg)` for the pure braid group. `W` acts freely on `V^reg`
(Steinberg), so `P(W)` has index `|W|` in `B(W)`. `B_A` is closed under subgroups,
finite products and finite-index overgroups
(`boone-higman-type-a-class-closed-under-finite-extensions`). So it suffices to put
either `P(W)` or `B(W)` into `B_A`.

Basic members of `B_A`:
- `F_r ≤ F_2 ≅ Inn(F_2) ≤ Aut(F_2)`, and `Z` likewise;
- `P_(n+1) ≤ B_(n+1) ≤ Aut(F_(n+1))`, by Artin's representation;
- all of these via `aut-free-groups-satisfy-permutational-boone-higman`.

**Reducible W.** If `W = W_1 × W_2` on `V_1 ⊕ V_2`, then
`V^reg = V_1^reg × V_2^reg` and `B(W) = B(W_1) × B(W_2)`. A trivial summand does not
change `V^reg` up to a contractible factor. So we may assume `W` is irreducible.

**Rank 1.** `W = Z/m` acts on `C` with `V^reg = C^×`, so `B(W) = Z`.

**Rank 2.** Let the `k` mirrors be lines through `0` in `C^2`.
- `V^reg` is the preimage, under the Hopf map `C^2 − 0 -> P^1`, of `P^1` minus `k`
  points.
- A principal `C^×`-bundle over a non-compact Riemann surface is trivial
  (`H^2(−; Z) = 0`). So `V^reg ≅ C^× × (P^1 − k points)` and `P(W) ≅ Z × F_(k−1)`,
  which lies in `B_A`.
- This covers every rank-2 group: `G(de,e,2)` and `G_4, …, G_22`.

**G(1,1,n) = S_n.** `B(W) = B_n ≤ Aut(F_n)`.

**G(de,e,n), d >= 2.**
- `G(m,p,n)` (`m = de`, `p = e`) contains `diag(ζ, 1, …, 1)` for `ζ^(m/p) = 1`, and
  `p < m`. So its mirrors are `{y_i = ζ y_j}` (`ζ^m = 1`) together with `{y_k = 0}`.
  These are the mirrors of `G(m,1,n)`, so
  `V^reg = {y : y_k ≠ 0, y_i^m ≠ y_j^m}`.
- `y ↦ y^m` (coordinatewise) is an unbranched `(Z/m)^n`-covering
  `V^reg -> Conf_n(C^×)`. So `P(W)` has finite index in `π_1(Conf_n(C^×))`.
- Translation gives `Conf_(n+1)(C) ≅ C × Conf_n(C^×)`, so
  `π_1(Conf_n(C^×)) ≅ P_(n+1) ∈ B_A`.

**G(e,e,n), e >= 2, n >= 3.** This is `imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class`.

**Real exceptional types** (`G_23, G_28, G_30, G_35, G_36, G_37`, i.e.
`H_3, F_4, H_4, E_6, E_7, E_8`). For complexified real `W`, `B(W)` is the Artin group of
`W` (Brieskorn, cited). It lies in `B_A` by
`spherical-artin-groups-satisfy-permutational-boone-higman`.

**Regular centralizers.** Bessis, *Finite complex reflection arrangements are K(π,1)*,
arXiv:math/0610777v4, read from the PDF, pp. 55–56.
- **Theorem 12.4(iii).** For `W` irreducible and well-generated, if `ρ` is a `d`-th
  root of the full twist `τ` with image `w`, then "the centralizer `C_(B(W))(ρ)` is
  isomorphic to the braid group `B(W')` of the centralizer `W' := C_W(w)`".
- So `B(W')` is isomorphic to a subgroup of `B(W)`. Real groups are well-generated.
- **G_31.** The proof of Bessis's Corollary 12.7 states: for `W = G_37` (`E_8`), "The
  number 4 is regular, with centralizer `W'` of type `G_31`", and
  `B(G_31) ≅ C_(B(W))(ρ^6)`. So `B(G_31) ≤ A(E_8) ∈ B_A`.
- **G_25, G_26, G_32.** These are the centralizers of `3`-regular elements of `E_6`,
  `E_7` and `E_8` (Springer 1974; cited, not read).
  - Consistency check: the degrees divisible by 3 are `{6,9,12}` for `E_6`,
    `{6,12,18}` for `E_7` and `{12,18,24,30}` for `E_8`. These are the degrees of
    `G_25`, `G_26` and `G_32`.
  - For each, 3 is regular: the number of degrees divisible by 3 equals the number of
    codegrees `d_i − 2` divisible by 3.
  - So `B(G_25) ≤ A(E_6)`, `B(G_26) ≤ A(E_7)`, `B(G_32) ≤ A(E_8)`, all in `B_A`.
  - (Independently, BMR identify these braid groups with the Artin groups
    `A(A_3)`, `A(B_3)`, `A(A_4)`, as Shephard groups; also cited, not read.)

**Envelope.** Every finitely generated group in `B_A` embeds in a finitely presented
simple group (`type-a-action-gives-boone-higman-for-subgroups`). ∎

**Not covered:** `G_24`, `G_27`, `G_29`, `G_33`, `G_34`, the five well-generated cases
whose K(π,1) property Bessis settled without a fibration. See
`complex-braid-groups-satisfy-permutational-boone-higman`.
