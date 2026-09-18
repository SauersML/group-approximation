---
rg: 2
id: sl2-q-embeds-in-fp-simple-group
kind: claim
title: SL_2(Q) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q) for every n >= 2, which implies this; this is the smallest case, a subgroup of GL_2(Q).
  gl2-q-embeds-in-fp-simple-group: that is GL_2(Q), which contains SL_2(Q) and implies this; this is its determinant-one subgroup.
  psl2-q-embeds-in-fp-simple-group: that is the simple quotient PSL_2(Q) = SL_2(Q)/{±I}; neither statement is known to imply the other.
  rational-linear-groups-satisfy-boone-higman: that covers finitely generated subgroups such as SL_2(Z[1/m]); this is the whole countable group, which lies in no residually finite group.
---

**OPEN.** There is a finitely presented simple group containing `SL_2(Q)`.

This is the smallest linear case of `gl-n-q-embeds-in-fp-simple-group`
(BBMZ arXiv:2306.16356v3, Problem 5.3(5)). It follows from
`gl2-q-embeds-in-fp-simple-group` by `sl2-q-bh-via-gl2`.

## Structure

- **Union.** `SL_2(Q)` is the ascending union of the finitely generated groups
  `SL_2(Z[1/m!])`. Each of these embeds in a finitely presented simple group
  (Zaremsky, arXiv:2405.09722, Theorem 1.2), but with hosts that depend on `m`.
- **Amalgams.** For each prime `p`, with `Z_(p) = Q ∩ Z_p` the valuation ring of
  `v_p` on `Q`, Ihara's theorem (Serre, *Trees*, Ch. II §1.4) gives
  `SL_2(Q) = SL_2(Z_(p)) *_(Γ_0) SL_2(Z_(p))^d`. Here `d = diag(p, 1)` and
  `Γ_0` is the subgroup with lower-left entry in `pZ_(p)`.
- **Product of trees (elementary).** `SL_2(Q)` acts on the restricted product
  of the trees of `(Q, v_p)` over all primes `p`, taken relative to the base
  vertices `[Z_(p)^2]`. This is a median graph, the 1-skeleton of an
  infinite-dimensional CAT(0) cube complex, and it is not locally finite. The
  stabilizer of the base vertex is `SL_2(Z)`. Every vertex stabilizer is
  `SL(L) ≅ SL_2(Z)` for a Z-lattice `L ⊆ Q^2`.
- **Subgroups that constrain hosts.**
  - the unipotent copy of `(Q,+)`, which is divisible;
  - `BS(1,4) = <diag(2,1/2), [[1,1],[0,1]]>`, since conjugating the unipotent by
    `t = diag(2,1/2)` gives its 4th power, which is exponentially distorted;
  - `SL_2(Z)`, which is virtually free.

  Finite subgroups have orders dividing 4 or 6.

## Host status (n = 2)

- **Excluded:**
  - every residually finite group (O1 of the root);
  - `V`, `T-bar`, Brin's `A`, `VA` and their subgroups (O3, and O4 by distortion);
  - central lifts, and covering lifts with Q-free deck group, of Q-free groups
    (`lifts-add-no-unipotent-divisibility`).
- **Natural piecewise-projective actions are excluded.** Let `G` be finitely
  generated, acting on `RP^1` by homeomorphisms that are piecewise `PSL_2(R)`
  with finitely many pieces. The pieces of the generators generate a finitely
  generated subgroup `Λ ≤ PSL_2(R)`. By analytic continuation, every element of
  `G` that is globally a Möbius map lies in `Λ`. `Λ` is finitely generated and
  linear, hence residually finite, so it has no divisible subgroup. So no copy
  of `(Q,+)`, and in particular no copy of `PSL_2(Q)`, can act inside `G` by its
  natural Möbius maps. Any embedding has to be non-natural.
- **Fixed-point arguments exclude nothing** (`gl2-q-fa-subgroups-are-finite`).
  Every FA or FW subgroup of `SL_2(Q)` is finite. So, unlike `n >= 3`, no
  cube-complex fixed-point argument (as in survey Remark 4.12) can remove a host.
- **Not excluded here:**
  - Brin--Thompson groups `nV`: they contain `(Q,+)` for `n >= 2` (Kojima--Sheng,
    arXiv:2603.18410v3). Whether `nV` contains `BS(1,4)` or `SL_2(Z[1/p])` is not
    settled here.
  - Type (A) actors and twisted Brin--Thompson groups
    (`gl-n-q-in-permutational-boone-higman-class`).
  - Finite germ extensions whose germ groups have distorted elements (not `VA`).

## Attempts

1. **Fixed-point obstructions (2026-09-17): vacuous for n = 2.** This is
   `gl2-q-fa-subgroups-are-finite`.
2. **VA and its subgroups:** dead by O4 (the `BS(1,4)` distortion).
3. **Natural piecewise-projective hosts:** dead by the analytic-continuation
   argument above.
