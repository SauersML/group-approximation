# Kourovka 21.44: lane state (bh-k2144, 2026-09-19)

**Problem.** Eberhard asks whether the infinite iterated wreath product `W` of `A_5` contains a
finitely generated dense subgroup of subexponential growth. The text is confirmed verbatim at
Kourovka v46, p. 174 (bh-ref-t0, d69136082d).

**Status: OPEN.** Details are in
`research/kourovka-21-44-spinal-groups-over-a5-dense-regime.md`. Nothing below has been
reviewed unless marked.

## What is on main

| Item | Content | Status |
|---|---|---|
| Prop N | The normal subgroups of `W_m` are the level stabilizers | referee PASS (d69136082d) |
| Prop G | No dense f.g. subgroup has growth `⪯ exp(n^β)`, `β = 1/40` | EMST's own stated result (arXiv:2604.15303v2, p. 33); pure attribution |
| Prop S | A spinal group over `A_5` is dense ⇒ every level map is onto ⇒ Bartholdi–Šunić's `Ω̂` is empty. Onto plus `K_i ⊄ K_{i+1}` ⇒ dense. Bartholdi–Šunić's standing `G_B` hypothesis already excludes `A_5` | referee PASS (d69136082d) |
| Prop D | `H = ⟨A_5, d_s = (s,1,1,1,d_s)⟩ ≤ P` is dense; no letter ever vanishes | referee PASS (15b37f96f8); may be a special case of Segal (2001), unchecked |
| Obstruction | Type-weighted length reduction fails at depths 1–2 for `H`; at least `c·324^k` merge-free words | lane proof |
| Correction | Iterated wreath products of cyclic groups have no f.g. dense subgroups | elementary |

## Test objects

- `P`, the period-2 spinal group over `A_5 × A_5`. It is dense and amenable (bounded automaton
  group; Bartholdi–Kaimanovich–Nekrashevych, recalled).
- `H ≤ P`, the `A_5` analogue of Fabrykowski–Gupta. It is dense and 4-generated.
- 21.44 is YES if `H` (or `P`) has subexponential growth. If `H` has exponential growth, so does
  `P`, and the single-spine spinal route is weakened, though not closed, since other spinal
  groups remain.

## Next steps for a fresh lane, in order

1. **Depth-3/4 merge density**, a finite-state mean-payoff computation.
   - The states are, per stream, a prefix in `A_5` and a pattern of last types.
   - If the minimum mean merge rate is positive at some depth `k`, a Grigorchuk-type argument
     gives subexponential growth of `H`, which answers 21.44 YES. Check the argument carefully:
     it must cover all geodesic words.
   - If the rate is zero, look for a free subsemigroup in `H` among the merge-free words, which
     would give exponential growth.
   - This needs a small acn112 run; ask the coordinator first.
2. **Literature.** Look for intermediate-growth theorems for spinal or GGS-type groups with a
   nonabelian rooted group on trees of degree ≥ 4. The known ones are ternary: Francoeur
   (arXiv:1702.08047) and Fabrykowski–Gupta. Also check whether Eberhard, or
   Eberhard–Maini–Sabatini–Tracey, discuss `H`.
3. **Open checks.**
   - Referee the depth-1/2 length-reduction obstruction, which is unreviewed.
   - Check Segal (2001) at source for `H`, or its density.
