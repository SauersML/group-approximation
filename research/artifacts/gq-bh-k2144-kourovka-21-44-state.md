# Kourovka 21.44: lane state (bh-k2144, 2026-09-19)

**Problem.** Eberhard asks whether the infinite iterated wreath product `W` of `A_5` contains a
finitely generated dense subgroup of subexponential growth. The text is confirmed verbatim at
Kourovka v46, p. 174 (bh-ref-t0, d69136082d).

**Status: OPEN.** Details are in
`research/kourovka-21-44-spinal-groups-over-a5-dense-regime.md`. Nothing below has been
reviewed unless marked. Updated 2026-09-19 by bh-k2144-b.

## What is on main

| Item | Content | Status |
|---|---|---|
| Prop N | The normal subgroups of `W_m` are the level stabilizers | referee PASS (d69136082d) |
| Prop G | No dense f.g. subgroup has growth `⪯ exp(n^β)`, `β = 1/40` | EMST's own stated result (arXiv:2604.15303v2, p. 33); pure attribution |
| Prop S | A spinal group over `A_5` is dense ⇒ every level map is onto ⇒ Bartholdi–Šunić's `Ω̂` is empty. Onto plus `K_i ⊄ K_{i+1}` ⇒ dense. Bartholdi–Šunić's standing `G_B` hypothesis already excludes `A_5` | referee PASS (d69136082d) |
| Prop D | `H = ⟨A_5, d_s = (s,1,1,1,d_s)⟩ ≤ P` is dense; no letter ever vanishes | referee PASS (15b37f96f8). `H` is the constant-sequence group of Neumann–Segal type (JNS arXiv:1305.2637 §4.3.2); the density source (Segal 2001 or Neumann 1986) was not settled |
| Merge-freeness | `144^k` reduced words are merge-free at every depth, so merge-only length reduction fails for `H` at all depths (`kourovka-21-44-neumann-a5-group-is-merge-free-at-every-depth`) | referee PASS (f2e0b60e78) |
| **Exponential growth** | `H` and `P` have exponential growth, via the solvable, not virtually nilpotent subgroup `K = ⟨Stab_{A_5}{1,5}, d_t⟩` and Milnor–Wolf (`kourovka-21-44-neumann-a5-group-has-exponential-growth`) | **referee PASS (e9969f5692)** |
| Correction | Iterated wreath products of cyclic groups have no f.g. dense subgroups | elementary |

## Status of the test objects

**The spinal test family `H ≤ P` is ruled out.** Both have exponential growth, so neither
witnesses 21.44. 21.44 itself stays open.

## Constraints on a next candidate

Any new dense subgroup of `W` built from rooted elements and directed elements
`d_t = (t at i, d_t at j)` must avoid two things:
- **The Stab({i,j}) configuration.** If the rooted part contains `Stab_{A_5}({i,j})` and the
  directed part contains `d_t` for `t` in it, the proof above gives an abelian-by-`D_∞` subgroup,
  hence exponential growth.
- **Non-regular rooted action.** Merge-only length reduction needs the rooted group to act
  regularly on the 5 points. In `A_5` the only regular subgroups are the cyclic groups `ℤ/5`.

A rooted `ℤ/5` alone is not dense, since by Prop S density forces every level map onto `A_5`.
So a candidate would need a regularly acting rooted `ℤ/5`, with directed elements supplying the
rest of `A_5` at deeper levels, as in a GGS-type or non-constant spinal group. Whether such a
group can be dense and still avoid the configuration above is the open design question. Nobody
has checked it.

## Next steps for a fresh lane

1. **Design.** Look for dense subgroups of `W` whose rooted part is `ℤ/5` acting regularly,
   such as GGS-type groups over `ℤ/5` with directed components in `A_5`. Then check density
   against Prop S, and check that they avoid the Stab({i,j}) configuration.
2. **Literature.** Look for intermediate-growth theorems for GGS or spinal groups on the 5-ary
   tree, extending Fabrykowski–Gupta and Francoeur (arXiv:1702.08047), and check whether any has
   dense closure in `W`.
