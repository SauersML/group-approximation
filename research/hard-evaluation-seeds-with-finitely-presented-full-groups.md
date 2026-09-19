---
rg: 2
id: hard-evaluation-seeds-with-finitely-presented-full-groups
kind: claim
title: For every recursive bound there is a seed SFT whose seed configuration is harder to evaluate along words, whose topological full group is finitely presented, and whose seed stabilizer in it is finitely generated
distinct_from:
  seed-full-groups-act-oligomorphically-on-the-seed-orbit: that proves the action on the seed orbit is faithful, highly transitive and reads the seed; this is the existence statement for hard seeds with the two finiteness properties that turn that action into a type (A) action.
  type-a-actors-with-arbitrarily-hard-word-problem: that asks for hard type (A) actors of any kind; this asks for them in one concrete shape, and implies that claim.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `seed-full-groups-act-oligomorphically-on-the-seed-orbit`, `seed-evaluation-is-bounded-by-the-forcing-radius`.

**OPEN.** For every recursive `T: N → N` there are:
- a finitely presented `Γ`;
- an SFT `Y ⊆ A^Γ` with a seed `y_*`, in the sense of `seed-full-groups-act-oligomorphically-on-the-seed-orbit`;
- a generator `s` of `Γ`,

such that three conditions hold.
1. **Hard evaluation.** The two-cell predicate `E_s(y_*)` is not decidable in time `C·T(C·ℓ) + C`
   for any `C`, where `ℓ` is the length of the word.
2. **Finite presentation.** The topological full group `F = [[Γ ⋉ Y]]` is finitely presented.
3. **Stabilizer.** `Stab_F(y_*)` is finitely generated.

## What is known

- **Rung Γ = Z.** It is empty: isolated points of `Z`-SFTs have eventually periodic tails, so (1)
  fails.
- **Computing configurations.** A start-row seed with a deterministic machine above it, over
  `Z^2` or a non-amenable `Γ`, satisfies (S1), (S2) and (1).
  - *What is open.* (S3), that `Y` equals the orbit closure; this is the SFT-closure problem for
    seeded computations. And conditions (2) and (3).
  - *Where (2) sits.* Condition (2) is the P2′-type rigidity gate of the master route, for a
    groupoid with isolated points.
- **CAP.** The SEED TOWER team's CAP question bounds the word problems of the groups `Γ ∈ 𝒞`.
  This claim needs instead that the *seed configurations* of fp full groups are not uniformly
  easy.

## Attempts

1. **Necessary condition (bh-invent-11, 09-18).** `seed-evaluation-is-bounded-by-the-forcing-radius`
   gives the necessary condition.
   - Evaluation is at most exponential in `|B_(R(n))|`. So over `Z^2`, `F_2 × F_2` or any
     polynomial-growth `Γ`, a witness for large `T` must have super-polynomial forcing radius.
   - Forward-deterministic machine seeds, i.e. a start row plus deterministic rows, are locally
     forced and fail (1).
   - **Candidate shape.** A seed whose cells near the origin are checked by backward signals from
     computation zones that run arbitrarily far away. Every agent is pinned by an ordered
     `L…L H R…R` field, the design rule for (S3).
   - **Status.** Not constructed. (S3) and conditions (2) and (3) are untested for this shape.
2. **Condition 3 is free; split full groups die (w14-bh-last1, 2026-09-18).**
   `seed-stabilizer-gate-is-free-and-split-seed-full-groups-die`.
   - *Condition 3 is implied by condition 2.* `F ⊇ FSym(O)` acts faithfully on the countably
     infinite `O`, so `fp-finitary-permutation-overgroups-are-type-a-actors` makes every
     `Stab_F(o)` finitely generated as soon as `F` is finitely generated. This claim is exactly
     conditions 1 and 2.
   - *Condition 2 is not a boundary property.* If `F = FSym(O)·Γ`, which always holds when `∂` is
     one point, then `F` is the lampshuffler `FSym(Γ) ⋊ Γ`, which is not `FP_2` for virtually
     indicable `Γ`. The seed `…0001000…` over `Z` has `F = H_2` and `F_∂ = Z`. So finite
     presentation of the boundary full group is necessary but not sufficient.
   - *What a witness needs.* Over `Z^2` or any virtually indicable `Γ`, the full group must be
     non-split: some element must follow different elements of `Γ` near different parts of `∂`.
     The extension `1 → FSym(O) → F → F_∂ → 1` is a gate of its own. No invariant detecting it
     is known beyond the split case.
3. **Hierarchical verification: a design in which lemma CB looks structural (bh-invent-11,
   2026-09-19; heuristic, not proved).**
   - *The design.* Use a fixed-point (Durand–Romashchenko–Shen) tile set with growing zoom and an
     origin mark. The mark pins the origin to a corner of blocks at every level, via sign fields
     and axis tiles; the fixed-point property lets the level-1 alignment rules act at every level.
     Every block of level `k` carries a prefix of one sequence `x`. Parents and children must
     agree on common prefixes. A block of level `K` checks its prefix against a decider `D`
     within its time budget. The checked set of sequences is the singleton `{χ_D}`.
   - *Hard evaluation.* Choose `D` hard on unary inputs relative to `T(N^n)`. A cell at distance
     about `N^k` from the origin reads `x_k = D(k)` from its level-`k` block, and `x_k` is fixed
     only by an ancestor of level `K(k)`, where the check of `D(k)` fits. So the forcing radius
     is about `N^(K(k))`, and `E_s(y_*)` is hard. This is consistent with
     `seed-evaluation-is-bounded-by-the-forcing-radius`.
   - *Why CB looks automatic.* Every point lies in a finite block of every level, including
     points of configurations with infinite blocks (half-planes, quadrants). So every prefix is
     checked in every configuration, and each infinite block carries exactly `χ_D`. The
     verification data therefore have **no free choice in any configuration**, boundary
     included, and there are no free basins for the clustering lemma
     (`rigid-anticipation-needs-scale-bounded-fault-detection`). Hierarchical computation is the
     scale-bounded fault detection that item (SW) of that node demands.
   - *What this leaves.*
     1. Quantum rigidity of the fixed-point skeleton with origin, i.e. the master route's
        fixed-point E2 gate (bh-free-35, bh-g2-fixedpoint-a). This includes whether the
        non-local but freedom-free forcing of `x` survives at the level of operators, not only
        classically.
     2. Condition 2 (finite presentation) over a non-amenable transplant. Over `Z^2` the
        infinite-type obstruction of the master route is expected to apply.
   - *Unchecked details.* Uniqueness of the seed configuration and the exact orbit closure (S3)
     are recalled from the DRS constructions, not re-verified.
4. **The finiteness engine and the first non-split calibration (bh-invent-11, 2026-09-19).**
   - *Seed full groups are locally defined groups.* Every seed full group `F` is a *locally
     defined group* `Γ_S` of Farley–Hughes (J. Comb. Algebra 8 (2024) 279–357, abstract and
     introduction read). Here `S` is the inverse semigroup of partial translations between
     cylinders. Their framework covers Houghton groups, `V` and `nV`, and supplies a
     contractible complex for `F`.
   - *Tree seeds are FSS groups.* When the cylinders form a ball tree, as for tree and
     hyperbolic seeds, `F` is a finite-similarity-structure group (Farley–Hughes,
     Proc. Edinb. Math. Soc. 58 (2015); Theorem 1.1 read). That theorem gives `F_∞` when there
     are finitely many ball classes and the structure is *rich in simple contractions*.
   - **Calibration T0.** Take `Γ = F_2 = ⟨a, b⟩` with the geodesic-to-origin seed. Then
     `Y = T^0 ⊔ ∂T`, and the balls are the cones `C(v)` and the singletons.
     - *The type counts.* A cone of type `t`, its last letter, splits into its apex and three
       cones, of every type except `t^(-1)`. So `H_0` is free abelian on `s, c_a, c_b`, with
       `c_a + c_(a^(-1)) = c_b + c_(b^(-1)) = -s` and `[Y] = -s`. Hence every partition of `Y`
       into pieces of ball type has `n_a = n_(a^(-1))`, `n_b = n_(b^(-1))` and
       `n_s = n_a + n_b − 1`.
     - *What a contraction needs.* A simple contraction needs a singleton, both cones of one
       letter, and one cone of the other letter.
     - *Where richness fails.* So Theorem 1.1 applies only if pieces of arbitrarily large height
       made of singletons and `a^(±1)`-cones alone cannot occur. The height-2 partition
       `{a^(-1)·C(a), C(a^(-1))}` shows that they do occur at small height. Richness is
       therefore not automatic, and Theorem 1.1 is not verified for T0.
     - *The question.* Is this "Houghton group of the free group" finitely presented? `F` is
       non-split, since elements follow different translations on different cones, so the
       obstruction of Attempt 2 does not apply. The expectation is yes, by analogy with `H_n`
       for `n >= 3`, since `∂T` is a Cantor set of ends. This is the first calibration for
       condition 2.
