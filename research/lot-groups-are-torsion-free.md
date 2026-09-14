---
rg: 2
id: lot-groups-are-torsion-free
kind: claim
title: Every LOT group is torsion-free
distinct_from:
  lot-complexes-with-vanishing-first-l2-betti-are-aspherical: that proves asphericity of a LOT complex from vanishing first L2-Betti number of its group; this is the open, weaker statement that the group never has torsion.
  contractible-2-complex-minus-a-cell-is-aspherical: that is the one-cell case of Whitehead's conjecture, which contains asphericity of every LOT complex and so implies this; this asks only for torsion-freeness of LOT groups.
  balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free: that is the implication showing why this matters for Kervaire--Laudenbach; this is the open group-theoretic input.
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

**OPEN.** For every labelled oriented tree `Gamma`, the LOT group
`G(Gamma) = < V | iota(e) lambda(e) tau(e)^-1 lambda(e)^-1 (e an edge of Gamma) >`
(notation of `lot-complexes-with-vanishing-first-l2-betti-are-aspherical`) has no
nontrivial element of finite order.

**Status at source.** A. N. Barreto and E. G. Minian, *Local indicability of
groups with homology circle presentations*, arXiv:2308.07447v1, p. 2, verbatim:
"Local indicability of LOT groups is an open problem (that would imply asphericity
of the associated presentations). In fact, it is not even known whether all LOT
groups are torsion-free."

**Implied by.**
- Asphericity of every LOT complex. A finite aspherical 2-complex has a
  torsion-free fundamental group.
- Local indicability of every LOT group.
- Known local indicability cases (not re-read here beyond the abstract and
  introduction of Barreto--Minian and of M. A. Cerdeiro, *A class of locally
  indicable LOT groups*): LOTs whose Howie graphs `I(Gamma)` or `T(Gamma)` have
  at most one cycle (Barreto--Minian, Corollary 3.1), and LOTs of diameter at
  most 3 (Howie, as quoted there).

**Implies.** With `stable-andrews-curtis-conjecture`, the killing form of
Kervaire--Laudenbach over nonnegative deficiency, through the route
`kervaire-killing-form-via-stable-ac-and-torsion-free-lots`. It also implies that no
LOT group other than `Z` splits as `H * Z` (`lot-group-free-splittings-force-torsion`).

## Attempts

- **Second source for the open status** (2026-09-14, lane hl-lot-torsion). S. Rosebrock,
  *The Whitehead conjecture – an overview*, Siberian Electron. Math. Rep. 4 (2007), p. 445,
  verbatim: "Is there a LOT-group with a nontrivial element of finite order? This also is
  still open." Just before: if `g ∈ π_1(K)` has finite order, `g^k = 1` and `g^k` is
  trivialized by `r`, then `(1 − g)[r]` is nontrivial in `π_2(K)`.
- **Proved classes.**
  - `crossing-pair-two-cycle-lot-groups-are-locally-indicable` (2026-09-14): locally
    indicable, hence torsion-free, when `T(Γ)` (or `I(Γ)`) has cyclomatic number two and a
    separated crossing pair. It goes beyond Corollary 3.1 of Barreto--Minian when both graphs
    have at least two cycles.
  - LOTs with at most seven vertices are torsion-free, because their complexes are aspherical
    (`lot-complexes-with-at-most-seven-vertices-are-aspherical`).
- **Open route.** `lot-torsion-free-via-concatenable-tietze-presentations` waits on
  `reduced-lots-have-concatenable-tietze-presentations`.
- **Where torsion could still live.**
  - A reduced LOT on at least eight vertices, not injective, with both `T(Γ)` and `I(Γ)` having
    at least two independent cycles.
  - No side of cyclomatic number two may carry a separated crossing pair.
