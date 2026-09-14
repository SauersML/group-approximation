---
rg: 2
id: torsion-free-nonsingular-equations-at-nonamenable-shapes-inject
kind: claim
title: Over torsion-free groups, nonsingular equations of non-amenable t-shape inject their coefficients
distinct_from:
  torsion-free-amenable-t-shape-adjunctions-are-aspherical: that is the Forester--Rourke theorem at amenable t-shapes; this is exactly the complementary set of shapes, where their method does not apply.
  klyachko-kl-holds-for-torsion-free: that is exponent sum ±1, every shape of which is amenable; this asks for shapes of exponent sum at least 2 in absolute value that are not amenable.
  kervaire-laudenbach-nonsingular-conjecture: that quantifies over all coefficient groups; this is its torsion-free slice at the shapes no known torsion-free theorem reaches.
artifacts:
  - research/artifacts/kl-nonamenable-shapes-2026-09-13.md
---

**OPEN.** Let `G` be torsion-free and `w in G * <t>` cyclically reduced with
`deg_t(w) != 0`, whose `t`-shape is neither a pure power nor amenable in the
sense of Fenn--Rourke. Then `G -> (G * <t>)/<<w>>` is injective.

This is the part of Levin's torsion-free conjecture, in its nonsingular
one-variable form, that no theorem pinned in this graph reaches. Forester--Rourke
(arXiv:math/0306088, `pi-two.tex` l.213–225) state that "the adjunction problem is
still open for torsion-free groups". They add that the Klyachko methods "will need
to be extended considerably if they are to work for a t–shape which is a proper
power".

## What is already known over torsion-free coefficients

- **Amenable shapes:** `torsion-free-amenable-t-shape-adjunctions-are-aspherical`,
  which includes every shape of exponent sum ±1 (Klyachko).
- **Pure power shapes `t^q`:** Levin's positive-equation theorem, cited by
  Forester--Rourke (l.836–837) as settling one of their examples. It holds over
  every group and is not imported as a node.
- **Locally indicable `G`, every shape:**
  `howie-locally-indicable-nonsingular-equations-are-solvable`. Through
  `nonsingular-coefficient-kernel-in-locally-indicable-residual`, this
  extends to residually locally indicable `G`.
- **Hyperlinear or MF `G`, every shape:** `kervaire-laudenbach-holds-for-hyperlinear`
  and `kervaire-laudenbach-holds-for-mf`.
- **Proper-power relators `u^k` with `u` of amenable shape:**
  `nonsingular-injectivity-passes-to-proper-power-relators`.
- **Variable length at most 5, over every group:** Howie, Edjvet--Howie and
  Evangelidou, as recorded by `length-five-kl-fence-citation`. For torsion-free
  coefficients at length at most 6, Klyachko--Thom list the title "Solving equations
  of length at most six over torsion-free groups", J. Group Theory 3 (2000), 329--337.
  That paper was not read, so its exact scope is not pinned here.

## The shapes this claim is about

An exact census (`research/artifacts/kl-nonamenable-shapes-2026-09-13/`, run on
MSI) classifies every nonsingular cyclic `t`-shape of length `L <= 12` up to
rotation and inversion. It uses Forester--Rourke's definitions verbatim, and checks
their two stated facts: every exponent-sum ±1 shape is amenable, and no proper power
is.

| L | nonsingular | pure power | amenable | non-amenable (proper powers) |
|---|---|---|---|---|
| 1–5 | 1, 1, 2, 2, 4 | 1 each | 0, 0, 1, 1, 3 | 0 |
| 6 | 5 | 1 | 3 | 1 (1) |
| 7 | 10 | 1 | 8 | 1 (0) |
| 8 | 13 | 1 | 9 | 3 (1) |
| 9 | 30 | 1 | 24 | 5 (1) |
| 10 | 41 | 1 | 30 | 10 (3) |
| 11 | 94 | 1 | 79 | 14 (0) |
| 12 | 136 | 1 | 106 | 29 (5) |

The smallest non-amenable shapes are:
- `L = 6`: `(t t t^-1)^2`;
- `L = 7`: `t^3 t^-1 t^2 t^-1`, of exponent sum 3, the first one that is not a proper
  power.

Every non-amenable shape in the census is its own root. Each root has two or more
clumps, e.g. two for `t^3 t^-1 t^2 t^-1` and three for `(t t t^-1)^3`.

## Attempts

1. **Proper-power relators.** *Settled for amenable roots* by
   `nonsingular-injectivity-passes-to-proper-power-relators`. The residue at
   proper-power shapes is the words of shape `S^k` whose `k` blocks carry different
   coefficients.
2. **Residual local indicability.** *Reduces* the claim to coefficient groups that
   are not residually locally indicable. A violating element dies in every locally
   indicable, MF-approximable and hyperlinear quotient
   (`nonsingular-coefficient-kernel-in-locally-indicable-residual`).
3. **Changing variables to reach an amenable shape.** *Dead at proper-power shapes.*
   - The Magnus derivative deletes the occurrences of `t t^-1` in the cyclic word.
     In `S^k` those positions are `k`-periodic, so `D(S^k) = D(S)^k`, and the root
     of a proper power is a proper power.
   - Substituting `t = s^j` only produces solutions of the original equation, and
     it sends `S^k` to `(S(s^j))^k`.
   - Automorphisms `t -> g t^(±1) h` of `G * <t>` fixing `G` change the shape at
     most by inversion.
   So none of these moves leaves the proper powers, which Forester--Rourke show are
   never amenable.
4. **What a counterexample needs.**
   - `G` torsion-free, not residually locally indicable, and not known to be
     hyperlinear or MF. Some `1 != g in ker(q)` lies in
     `Rad_LI(G) intersect Rad_MF(G) intersect Rad_hyp(G)`.
   - `w` of non-amenable shape and not a proper power of an amenable-shape relator.
   - If the Ivanov--Klyachko title is accurate as to scope, variable length at least
     7, starting at `t^3 t^-1 t^2 t^-1`.
