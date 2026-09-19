---
rg: 2
id: virtually-torsion-free-host-no-ce-augmentation-corner
kind: claim
title: Realize a no-CE algebra in a finite-subgroup augmentation corner of a virtually torsion-free recursively presented host, off the finite radical
refuted_by:
  - virtually-torsion-free-mf-radical-is-torsion-free
distinct_from:
  nonhyperlinear-bloop-finite-augmentation-corner: that allows any countable host and any finite subgroup, and feeds the explicit-witness endpoint; this additionally demands a finitely generated recursively presented virtually torsion-free host and a finite subgroup with infinite normal closure, which is exactly what makes the same corner feed the torsion-free seed.
  agent-leavitt-not-bcs-negative-root-corner: that fixes the binary-Leavitt Steinberg host, which has no proper finite-index subgroup and so can never be virtually torsion-free; this excludes that host by hypothesis.
  full-mf-radical-abelianized-cover-is-not-mf: that descends a full radical across an amenable non-radical kernel; this needs no descent, only the finite-index trace of the radical.
artifacts:
  - research/virtually-torsion-free-infinite-mf-radical-gives-seed.md
  - research/nonhyperlinear-finite-augmentation-corner-kills-mf.md
---

**OPEN HOLE, NO PROPERTY `(T)` PERMITTED.**  Construct the following:

- a unital star algebra `B` with no Connes-embeddable tracial state, for
  example `A(B_loop)` from `lin-explicit-fixed-bcs-gap-via-generic-conversion`;
- an explicit finitely generated, recursively presented group `H`;
- a torsion-free subgroup `E <= H` of finite index;
- a finite subgroup `K <= H` whose normal closure in `H` is infinite, or
  equivalently `K` not contained in the finite radical `W(H)`;
- finite group-ring expressions giving a unital star homomorphism

```text
Phi : B -> q_K C[H] q_K,       Phi(1) = q_K,       q_K = 1 - |K|^-1 sum_(k in K) k.
```

By `virtually-torsion-free-infinite-mf-radical-gives-seed`, a solution gives
`property-t-free-torsion-free-fp-non-mf-seed` directly.  It needs neither the
Leavitt collapse nor the abelianized-cover hole.  The same solution also
solves `nonhyperlinear-bloop-finite-augmentation-corner` when `B = A(B_loop)`,
so one construction feeds two endpoints.

**Necessary conditions a candidate must meet.**

- `H` is not MF: `K <= Rad_MF(H)`.  So `H` is not residually finite, not
  linear, not virtually special, not amenable, and not LEF.
- `E` itself is torsion-free and not MF.  Any torsion-free obstruction
  therefore applies to `E`, for example the small-kernel kill in
  `torsion-free-seeds-need-kernel-descent-or-trace-corner`.
- `K` meets `E` trivially, so the corner is never visible inside `E` as a
  torsion corner.  It becomes visible only after inducing up to `H`.

## Attempts

- 2026-09-18 (swarm-0917-w12-w12-ptm-last1): created as the single hole of
  `property-t-free-seed-via-virtual-torsion-corner`.  There is no candidate
  host yet.  Natural test hosts are finite extensions `H = Gamma x| F` of
  non-residually-finite irreducible lattices `Gamma` in products of trees
  (Burger--Mozes, Wise), with `F` a finite group of tree automorphisms.
  - A finite normal `N` meets `Gamma` trivially, so it centralizes `Gamma`.
    So `W(H) = 1` whenever `Gamma` is centreless and no nontrivial element
    of `F` acts on `Gamma` by an inner automorphism.  Any nontrivial `K <= F`
    then has infinite normal closure.
  - Whether these hosts are MF is unknown.
  - The wreath-host obstruction recorded in
    `nonhyperlinear-bloop-finite-augmentation-corner` (exact finite-window
    models) uses residual finiteness of the base.  For the simple
    Burger--Mozes lattices, which have no finite quotients, it does not
    obviously apply.  That is untested.
- 2026-09-19 (swarm-0917-w14-w14-ptm-last1, finite-models): REFUTED by
  `virtually-torsion-free-mf-radical-is-torsion-free`.
  - Death step: `K` meets the torsion-free core `N = Core_H(E)` trivially,
    so it injects into the finite group `H/N`.
  - The left-regular representation of `H/N` sends `q_K` to a nonzero
    projection of rank `n(1 - 1/|K|)`.
  - So any `Phi` gives `B` a matrix, hence Connes-embeddable, tracial
    state.  This holds for every host and every `K != 1`.
  - The class kill `radical-calculus-misses-virtually-torsion-free-groups`
    closes the whole (C)+(I) gate, including multi-host derivations.
- 2026-09-18 (swarm-0917-w14-w14-ptm-last1, finite-models): **REFUTED**
  for every host, by `virtually-torsion-free-mf-radical-is-torsion-free`.
  - `K` is finite and nontrivial, and it meets the torsion-free normal core
    `N = Core_H(E)` trivially.  So `K` embeds in the finite quotient `H/N`.
  - Let `lambda` be the regular representation of `H/N`, of dimension
    `d = [H:N]`.  Then `lambda(q_K)` is a projection of rank
    `d(1 - 1/|K|) > 0`.
  - `tr o lambda o Phi` is therefore a matrix, hence Connes-embeddable,
    tracial state on `B`, which contradicts the hypothesis on `B`.
  - Equivalently, `Rad_MF(H) <= N` is torsion-free, because finite quotients
    are MF.  So the corner theorem's conclusion `K <= Rad_MF(H)` forces
    `K = 1`.
  - The necessary-conditions list above missed this finite-quotient
    obstruction.
  - Where it dies: at the very first step.  Any virtually torsion-free host
    detects `K` in a finite quotient.
  - The route `property-t-free-seed-via-virtual-torsion-corner` is dead.
  - The class version,
    `virtually-torsion-free-residual-kills-radical-calculus`, shows that no
    combination of torsion conclusions with finite-index trace reaches a
    torsion-free non-MF group.  The seed needs the descent hole
    `full-mf-radical-abelianized-cover-is-not-mf` or an intrinsic analytic
    torsion-free non-MF theorem.
