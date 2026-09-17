---
rg: 2
id: every-f-free-subgroup-of-thompson-f-is-amenable
kind: claim
title: Every subgroup of Thompson's group F with no subgroup isomorphic to F is amenable
distinct_from:
  every-subgroup-of-thompson-f-is-ea-or-contains-f: that is the Brin–Sapir dichotomy, which implies this claim; this asks only for amenability of F-free subgroups, and a Brin–Sapir counterexample could still be amenable.
  thompson-f-is-amenable: that implies this claim; this claim is implied by the Brin–Sapir conjecture as well, and is not known to imply amenability of F, since F itself is not F-free.
  f-free-groups-are-closed-under-recurrent-extensions: that proves closure properties of the class of F-free groups; this asks whether the F-free subgroups of F are amenable.
---

**OPEN.** If `K ≤ F` has no subgroup isomorphic to `F`, then `K` is amenable.

This is prerequisite P2 of `thompson-f-amenable-via-exotic-co-amenable-subgroup`.
- It is implied by `thompson-f-is-amenable`.
- It is implied by `every-subgroup-of-thompson-f-is-ea-or-contains-f`.
- A counterexample proves `thompson-f-is-not-amenable`.

Amenability passes to directed unions, so it is enough to treat finitely generated `K`.

## Attempts

- **Germ-kernel descent, amenable version (swarm-0917-w5-f-decomp, 2026-09-17).** In
  `plo-i-group-is-ea-iff-its-orbital-germ-kernels-are`, items 1–3 use no hypothesis on the class. The proof of
  items 4–5 uses only three things:
  - closure of the class under subgroups, quotients, extensions by abelian groups, finite products and
    directed unions;
  - `H ↪ ∏_i H_{A_i}`;
  - `K_A(H)_A` being a quotient of `K_A(H) ≤ H`.

  Amenability has all of these, so the same argument gives the following.
  - A finitely generated `H ≤ PL_o(I)` is amenable iff each `K_{A_i}(H)_{A_i}` is amenable.
  - A non-amenable one has an infinite compactly nested descent `(D_i, A_i)` with `D_{i+1} ≤ K_{A_i}(D_i)`
    and every `(D_i)_{A_i}` non-amenable.
  - If `H` is `F`-free, `f-free-plo-i-groups-have-equal-end-germ-kernels` makes every step synchronized:
    `(D_i)_{A_i} / K_{A_i}(D_i)_{A_i} ≅ Z^{r_i}` with `r_i ≥ 1`, through the left germ alone.

  So P2 is equivalent to: no finitely generated `F`-free subgroup of `F` carries an infinite synchronized
  descent of non-amenable germ kernels. It is the Brin–Sapir descent with "EA" replaced by "amenable".
  - *Dies:* at terminating the descent. For EA the descent carries an ordinal rank, but ranks are unbounded
    below `ε_0` (`f-has-ea-subgroups-of-every-class-below-epsilon-zero`). For amenability there is no rank
    at all. Along the descent, the only information about copies of `F` that gets recorded is
    synchronization, and no known argument turns an infinite synchronized descent into a copy of `F` or
    into a paradoxical decomposition. The step at which every descent-based proof dies is the absence of a
    well-founded invariant that decreases along synchronized descents.
  - This dies at the same step as the germ-kernel attempt on `every-subgroup-of-thompson-f-is-ea-or-contains-f`.
    What it adds is that the weaker P2 gains nothing from giving up elementary amenability: the descent is
    the same object.
