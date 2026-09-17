---
rg: 2
id: thompson-f-cohomology-certificates-cannot-prove-nonamenability
kind: claim
title: "Cohomological and index certificates cannot prove Thompson's F non-amenable: l2-Betti numbers vanish, F has fixed price 1, F is outside C_reg and D_reg, and nonzero bounded cohomology needs a non-separable dual module with vectors fixed by an end-tail subgroup"
distinct_from:
  amenable-normalish-kills-l2-betti-bounded-cohomology: that is the general BKKO import for any group with an amenable normalish subgroup; this applies it to F through an explicit subgroup, adds cost, separable coefficients and a sharper coefficient gate, and records the dead certificate class for the root.
  thompson-f-bounded-cohomology-vanishes-separable-duals: that is Monod's vanishing for separable dual modules alone; this combines it with the tail gate, which also covers non-separable modules, and with the l2 and cost invariants.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills bounded flows read through finite automata on the positive monoid; this kills certificates through cohomological, l2 and orbit-equivalence invariants.
  thompson-f-moment-data-cannot-certify-nonamenability: that kills finite cogrowth data; this kills invariants that vanish on groups with an amenable normalish subgroup.
---

**ESTABLISHED.** Let `T = ⟨h_n : n ≥ 0⟩ ≅ ⊕ Z` and its tails `T_(≥M)` be as in
`thompson-f-has-an-amenable-normalish-tail-subgroup`: the `h_n = x_0^n h_0 x_0^(-n)` are translates of a
bump `h_0` supported in `[1/4,1/2]`. Then:

1. **l2.** `β_n^(2)(F) = 0` for every `n ≥ 0`.
2. **Cost.** `F` has fixed price 1: every essentially free p.m.p. action of `F` has cost 1.
3. **Separable coefficients** (Monod). `H_b^n(F,E) = 0` for all `n > 0` and every separable dual Banach
   `F`-module `E`. In particular `F` is boundedly acyclic.
4. **Tail gate.** Let `E` be a dual Banach `F`-module (the setting of BKKO's Proposition
   `thm:trivial-bdd-cohomology`). If `E^(T_(≥M)) = 0` for every `M`, then `H_b^n(F,E) = 0` for every
   `n ≥ 0`. This covers every mixing module, for example `ℓ^p(F)` with `1 ≤ p < ∞`.
5. **Negative curvature.** `F ∉ C_reg` (`H_b^2(F, ℓ^2 F) = 0`) and `F ∉ D_reg`. By the inclusions quoted
   in BKKO, `F` has no non-elementary proper isometric action on a Gromov-hyperbolic graph of bounded
   valency, and none on a proper CAT(-1) space. BKKO also list "a non-elementary simplicial action on some
   simplicial tree" without a properness hypothesis. That cannot be literally right: `F_2 × Z` acts
   non-elementarily on the tree of `F_2` but has an amenable normal `Z`. So no tree consequence is drawn.

**The certificate class that dies.** Each of the following would prove `F` non-amenable, because
amenable groups have the opposite value:
- (a) `β_n^(2)(F) > 0` for some `n` (Cheeger–Gromov);
- (b) some free p.m.p. action of cost `> 1` (Ornstein–Weiss, Levitt);
- (c) nonzero `H_b^n(F,E)`, `n > 0`, for a dual `E` (Johnson), for instance a nontrivial quasimorphism, or
  `F ∈ C_reg`;
- (d) an unbounded quasi-cocycle into `ℓ^2(F)`, or a non-elementary action of the kinds in item 5.

By items 1–5, (a), (b) and (d) are impossible. (c) is impossible for every separable `E` and every
`T`-tail-mixing `E`.

**Where every member dies.**
- *Invariant:* the amenable normalish subgroup `T`, together with its commensurating chain
  `T ⊂ ⟨T, x_0⟩ ⊂ ⟨T, x_0, x_1⟩ = F`.
- *Step:* the evaluation of the invariant.
  - For (a) and (d), BFS/BKKO vanishing along an amenable normalish subgroup.
  - For (b), Gaboriau's chain criterion started at the amenable group `T`.
  - For (c), cocycles on `(F/T)^(n+1)` take values in the vectors fixed by `⋂ t_i T t_i^(-1) ⊇ T_(≥M)`.

**Survivors** (sharp). A cohomological proof must use a non-separable dual module `E` with a nonzero
vector fixed by some end-tail subgroup `T_(≥M)`, and a cocycle that is not cohomologous to zero on
`(F/T)^(n+1)`. Johnson's module `(ℓ^∞(F)/C)^*` has such vectors: a difference of two distinct
`T_(≥M)`-invariant means, supported on different cosets. It is the module in Johnson's criterion (recalled,
[Joh72, Thm. 2.5]). So what survives of the cohomological class is Johnson's invariant-mean module, and no
separable or tail-mixing shadow of it is left.

**Calibration: the vanishing is not evidence for amenability.**
- `F_2 × Z` is non-amenable. Its normal `Z` is an amenable normalish subgroup, and
  `Z ⊂ ⟨Z, a⟩ ⊂ ⟨Z, a, b⟩` is a commensurating chain. So items 1, 2, 4, 5 hold for it by the same proof.
- Monod warns (verbatim in `thompson-f-bounded-cohomology-vanishes-separable-duals`) that item 3
  also holds for his non-amenable piecewise-projective groups.

So none of these invariants separates `F` from known non-amenable groups. What they detect is an amenable
normalish subgroup with a commensurating chain. `F` gets one from its global fixed point, where the germ
group is cyclic, and many non-amenable groups have one too.

**Not covered.**
- Spectral gap of `λ_F` itself, i.e. the root.
- Non-separable, non-tail-mixing coefficients (the survivors above).
- Certificates through non-free or non-p.m.p. actions (see `thompson-f-interval-orbit-relation-is-hyperfinite`
  for the dyadic affine relation).
- Numerical invariants that do not vanish on groups with amenable normalish subgroups, such as the
  spectral radius or cogrowth of a fixed generating set.

**Credit.** Items 1 and 4 (mixing case) are BKKO / Bader–Furman–Sauer applied to `T`. Item 3 is Monod.
Item 2 is Gaboriau's criterion. Vanishing of the l2-Betti numbers of `F` is also known through other
arguments. The contribution here is the explicit subgroup `T`, the tail gate beyond mixing modules, the
survivor characterization, and recording the whole class as dead on the root.

Proof route: `thompson-f-cohomological-certificates-proof`.
