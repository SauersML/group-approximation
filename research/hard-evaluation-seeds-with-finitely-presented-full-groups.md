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
