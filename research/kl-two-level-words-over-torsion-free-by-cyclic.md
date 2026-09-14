---
rg: 2
id: kl-two-level-words-over-torsion-free-by-cyclic
kind: claim
title: Degree-one words whose letters occupy two coset levels inject over a torsion-free subgroup of finite cyclic index
distinct_from:
  kl-pivot-letter-words-inject-over-torsion-free-by-finite: that proves the case where the base level carries exactly one letter and the other level has exponent sum zero; this asks for every distribution of letters over the two levels, where no letter can be eliminated and the cyclic chain of equations has a closing equation.
  kervaire-laudenbach-nonsingular-conjecture: that is the conjecture over all groups and all shapes; this is the smallest case of the torsion-free-by-finite route with a genuinely coupled system, one cycle of n equations with two unknowns each.
  kl-p-square-system-equations-are-individually-solvable: that shows each single equation and every variable-disjoint subsystem is solvable; this asks for the whole cycle, whose consecutive equations share unknowns.
artifacts:
  - research/artifacts/hl-kl-howie-overlap-2026-09-14.md
---

Let `P` be a group, `H <= P` torsion-free, and `a in P` normalizing `H` with
`a^n in H`, `n >= 2` minimal. Let `W in H * F(u, v)` with
`deg_u W + deg_v W = ±1`, and put

    w = W(t, a t a^(-1))  in  P * <t>.

**Conjecture.** `P -> (P * <t>)/<<w>>` is injective.

These are exactly the degree-`±1` words all of whose letters sit at the coset
levels `1` and `aH`. After rewriting over the kernel of `P * <t> -> P/H`, one
gets `r_i = W^(i)(t_i, t_(i+1))` for `0 <= i < n`, with `t_n = a^n t_0 a^(-n)`
and the coefficients of `W` conjugated by `a^i`. This is a single cycle of `n`
equations, each sharing one unknown with the next.

## Known cases

- `u` occurs exactly once in `W` and `deg_v W = 0`. This is
  `kl-pivot-letter-words-inject-over-torsion-free-by-finite`, by Tietze
  elimination along the cycle.
- `H` locally `p`-indicable, with `n` a power of `p`. This is
  `krstic-p-nonsingular-equations-inject-locally-p-indicable-groups`, since `P`
  is then locally `p`-indicable.
- `P` hyperlinear. This is `kervaire-laudenbach-holds-for-hyperlinear`.
- `P` torsion-free, so that every coefficient has infinite order. This is Klyachko.

## Why the tools stop

- **Adjunction.** Starting from `H * <t_(n-1)>`, one can adjoin `t_(n-2)`
  through `r_(n-2)`, then `t_(n-3)`, and so on. Each step is Klyachko or the
  layered theorem of Forester--Rourke, whenever `t_i` has exponent `±1` in
  `r_i`, and each step keeps the group torsion-free (Bogley--Pride--Serre). The
  last relator `r_(n-1)` then introduces no new unknown: it is a pure constraint,
  and no pinned theorem controls it.
- **Elimination.** When every unknown occurs at least twice in its equation,
  there is no Tietze move.
- **Change of variables.** The Forester--Rourke remark covers systems that some
  change of variables makes layered. A layered system needs a first equation in
  one unknown, while every `r_i` involves two.

See the artifact for the pins.

**OPEN.** It is implied by `kervaire-laudenbach-nonsingular-conjecture` and by
Howie's systems conjecture over torsion-free groups.
