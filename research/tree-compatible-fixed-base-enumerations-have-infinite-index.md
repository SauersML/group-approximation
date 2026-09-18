---
rg: 2
id: tree-compatible-fixed-base-enumerations-have-infinite-index
kind: claim
title: If the input generators act by automorphisms of the boundary tree, the near shift group of a fixed-base enumeration has infinite index in the odometer Nekrashevych group, and the normal-form enumeration of C_2*C_3 is such a case
distinct_from:
  finite-index-odometer-near-shift-groups-pass-the-germ-gate: that says finite index of R_nu in B passes the germ gate; this proves that a whole natural class of fixed-base enumerations, those whose input generators are tree automorphisms, can never reach finite index, because the shift and every local odometer are tree automorphisms too.
  a5-arithmetic-shell-envelope-is-not-finitely-presented: that kills one explicit fixed-base enumeration of A_5*A_5, whose near shift group acts on a tree; this isolates a mechanism that forces a tree action for every tree-compatible enumeration of every input, and applies it to C_2*C_3.
  fixed-base-finite-subgroups-satisfy-a-cylinder-count-congruence: that gives necessary torsion congruences and a seed; this is a necessary condition of a different kind, on how the regular action may be encoded.
artifacts:
  - research/artifacts/gq-bh-bh-shell-germ-tree-compatible-search.md
---

**ESTABLISHED** by `tree-compatible-fixed-base-infinite-index-proof` (lane proof,
elementary, not independently reviewed; no novelty claimed). The attached bounded search
is evidence only.

## Setting

`B = V_(h,r)(<a>)` acting on `X`, `r` copies of the `h`-adic Cantor set, and by near
permutations on `N`, as in `odometer-prefix-groups-have-fg-index-kernels`. Let `T` be the
tree with boundary `X`: the `r` rooted `h`-ary trees with their roots joined to one extra
central vertex, and for `r = 2` that vertex smoothed into an edge. Every element of `B` acts
on `T` by an almost automorphism. Write `Aut_B(T)` for the elements of `B` that act by
genuine automorphisms.

## Statement

1. **The shift is a tree automorphism.** The cofinite shift `s`, the odometer and every
   local odometer lie in `Aut_B(T)`.
2. **Tree-compatible enumerations fail the finite-index criterion.** Let `nu` be a
   fixed-base enumeration of an infinite input `P` with generating set `S`. If each
   `lambda_g`, `g in S`, lies in `Aut_B(T)` near infinity, then `R_nu <= Aut_B(T)`, and
   `[B : R_nu] = infinity`. So item 1 of
   `finite-index-odometer-near-shift-groups-pass-the-germ-gate` never applies to such an
   enumeration.
3. **The modular group instance.** Take `h = 2`, `r = 1` and `P = C_2 * C_3 = <v> * <w>`.
   Encode an element `v^(e_0) w^(eps_1) v ... v w^(eps_k) v^(e_1)` in normal form as
   `n = e_0 + 2t`, with `t = 0` for `k = 0` and otherwise `t` the number whose binary
   digits, lowest first, are `x_1 ... x_k e_1 1` (`x_i = 1` iff `eps_i = +1`). This is an
   injection onto `N` minus the six points `2, ..., 7`; composing with a bijection that
   equals `s^-6` near infinity gives an enumeration `nu'`. Near infinity:
   - `lambda_v` is the root swap `[0] <-> [1]`;
   - `lambda_w` is `[1] -> [01] -> [00] -> [1]`.
   Both are automorphisms of `T_3`: an edge flip and a rotation of order 3 about a vertex.
   So `R_nu'` is conjugate by `s^6` to `<lambda_v, lambda_w, s> <= Aut_B(T_3)`, and it has
   infinite index in `B`. The regular action realizes `C_2 * C_3` as its Bass--Serre
   action on `T_3`.

## Design consequence

A fixed-base enumeration aiming at finite index must give some generator a near class
that is an almost automorphism of `T` but not an automorphism, such as a local rotation
supported in a proper cylinder. The normal-form encoding of a free product is always
tree-compatible, so a successful enumeration of a virtually free input needs a different,
non-normal-form encoding.

## Evidence

A bounded search (artifact) of `<lambda(C_2*C_3), finitary swaps of depth <= 2>`
covered all words of length at most 10, about 3.04M elements. Among the 71 transpositions
of depth at most 3 it found exactly the 11 that are `T_3`-automorphisms, and no local copy
of Thompson's generator. Its calibration target was recovered.

## Scope

- Nothing is claimed about finite presentation of `R_nu` itself, only its index in `B`.
- Item 2 needs `lambda_g` in `Aut_B(T)` for the given tree `T`. An enumeration may be
  tree-compatible for no tree and still fail.

## Attempts

**Attempt 1 (twisted enumeration of C_2*C_3): escapes this node, generation undecided.**
- *Criterion (proved, elementary).* For `h = 2, r = 1`, the shift is the odometer `a` and
  `B = <V, a>`, while `V` is infinite and simple. So a fixed-base near shift group `R`
  containing `s` satisfies `[B : R] < infinity` iff `V <= R` iff `R = B`.
- *The twist.* For `g in V`, `nu' = g o nu` is again an enumeration, because `V` acts on `N`
  by genuine permutations. Then `R_nu' = g <lambda(P), g^-1 s g> g^-1`. With `g = x_1`
  (Thompson's second generator, not a `T_3`-automorphism), `lambda(P) = <tau, w>` lies in
  `Aut(T_3)` while `x_1^-1 a x_1` does not. So item 2 no longer applies, and by the
  criterion `[B : R_nu'] < infinity` iff `<tau, w, x_1^-1 a x_1>` contains `V`.
- *Bounded search (artifact, second section; evidence only).*
  - All words of length at most 10: 777k elements.
  - Of the 3482 elements with trivial odometer labels up to length 9, 3328 are neither
    `T_3`-automorphisms, nor automorphisms of the twisted trees `x_1^(+-1)(T_3)`, nor in
    Thompson's `T`. So no tree invariant of the obvious kind survives.
  - No generator of `V` was found: not `x_1`, nor the swaps `v_0`, `v_1`, `v_10`, nor
    `a` itself. A bootstrapped search, over products of three of the 80 shortest
    label-free elements, also found none.
  - The planted calibration element was recovered at word length 4.
- *Status.* OPEN. The twisted enumeration is the natural next candidate for the first
  finite-index fixed-base near shift group. Deciding it needs either a generation proof, or
  an invariant preserved by `tau`, `w` and `x_1^-1 a x_1` that `V` violates.
