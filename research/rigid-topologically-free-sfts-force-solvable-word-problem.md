---
rg: 2
id: rigid-topologically-free-sfts-force-solvable-word-problem
kind: claim
title: A finitely presented group carrying a quantum-rigid minimal topologically free subshift of finite type has solvable word problem
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that premise P1 consumes decidability through Jeandel's theorem for strongly aperiodic SFTs; this is an algebraic analogue that needs quantum rigidity but no freeness, so decidability is still consumed after the relaxation to topological freeness.
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that gives finite presentation of the crossed product; this combines it with simplicity to decide the word problem of the acting group.
  master-route-needs-only-topological-freeness: that relaxes freeness to topological freeness in both master routes; this shows the relaxed crux object still forces a solvable word problem.
---

**ESTABLISHED** (lane bh-g3-topfree, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed).

## Statement

Let `Λ = <S | R>` be finitely presented. Let `X ⊆ A^Λ` be a nonempty SFT, with forbidden patterns on
`B_r`, that is `D`-quantum rigid over `F_2` for some `D >= r`. Suppose `Λ` acts on `X` minimally and
topologically freely. Then `Λ` has solvable word problem.

In particular, no finitely presented group with unsolvable word problem carries such a shift.

## Proof

1. **`B` is finitely presented.** By `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`,
   `B = LC(X, F_2) ⋊ Λ` is a finitely presented `F_2`-algebra. Its finite presentation is explicit from
   `S`, `R`, `A` and the forbidden patterns.
2. **`B` is simple.** `X` is compact, Hausdorff and zero-dimensional, and the action is minimal and
   topologically free. So `free-minimal-cantor-crossed-products-are-central-simple` makes `B` simple,
   with `Z(B) = F_2`. In particular `B ≠ 0`.
3. **Finitely presented simple algebras have solvable word problem.** This is Kuznetsov's argument
   for algebras. Let `b` be a noncommutative polynomial in the generators.
   - `b = 0` in `B` is recursively enumerable, by enumerating consequences of the finitely many
     relations.
   - Since `B` is unital and simple, `b ≠ 0` iff the two-sided ideal `BbB` is `B`, iff
     `1 = Σ_{i<=n} x_i b y_i` for some `n` and polynomials `x_i`, `y_i`. That is also recursively
     enumerable, by enumerating `n`, `x_i`, `y_i` and consequences of the relations.
   - Running both searches in parallel decides `b = 0`.
4. **The group embeds with a computable image.** `λ ↦ u_λ` is a homomorphism `Λ -> B^x`, injective
   because the `u_λ` form a free `LC(X, F_2)`-basis and `X ≠ ∅`. A word `w` in `S` maps to the
   explicit monomial `u_w`. So `w = 1` in `Λ` iff `u_w - 1 = 0` in `B`, which step 3 decides. ∎

## Calibrations

- **Free groups.** `F_n` with its end shift satisfies the hypotheses
  (`free-group-boundary-shifts-are-quantum-rigid`), and `F_n` has solvable word problem.
- **Comparison with Jeandel.** Jeandel's theorem (arXiv:1501.06831, recalled; used as context in
  `boone-higman-via-v-times-aperiodic-sft-full-groups`) deduces solvable word problem from a strongly
  aperiodic SFT, with no rigidity. The statement here needs rigidity and minimality instead of
  freeness. It applies to free groups, where there are no strongly aperiodic SFTs.
- **Non-rigid shifts.** Without rigidity the crossed product need not be finitely presented, and
  step 1 fails. For example the golden–silver shift is minimal, free and of finite type but not rigid.

## Lesson for general BH

Relaxing the master route's crux from "free" to "topologically free" does not smuggle undecidable
acting groups in. Any fp group carrying the relaxed crux object already has solvable word problem, so
decidability is consumed at the rigidity gate, exactly where BH needs it. The mechanism is a
Kuznetsov argument: rigidity makes the crossed product finitely presented, topological freeness plus
minimality makes it simple, and fp simple algebras decide their own word problem.
