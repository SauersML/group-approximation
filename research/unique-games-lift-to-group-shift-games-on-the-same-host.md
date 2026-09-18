---
rg: 2
id: unique-games-lift-to-group-shift-games-on-the-same-host
kind: claim
title: Every unique game with alphabet k lifts, on the same weighted loopless graph and in polynomial time, to at most k left-shift games over transitive groups of order at most k!, losing a factor at most k! in completeness and nothing in soundness, so on any host class general UG is easy exactly when group-shift games over all finite groups are easy
distinct_from:
  unique-games-reduce-to-shifts-over-their-holonomy-group: that identifies an orbit game with a shift game only when the holonomy acts regularly, with no loss; this handles the non-regular (coset) orbits, which that node names as the exact survivor, by passing to the regular cover at loss |Stab|.
  ugc-is-equivalent-to-affine-ugc: that is KKMO, which reaches abelian shift games but rebuilds the constraint graph; this keeps the graph and its weights and pays with non-abelian groups.
  general-unique-games-easy-on-globally-hypercontractive-graphs: that is the open algorithmic question on the Bafna--Minzer hosts; this is a host-independent reduction which turns that question into its group-shift form.
artifacts:
  - experiments/ugc-coset-lift-2026-09-17/check_coset_lift.py
  - experiments/ugc-coset-lift-2026-09-17/output.txt
---

**ESTABLISHED.** Route: `unique-games-coset-lift-proof`.

**Setting.** This follows `unique-games-reduce-to-shifts-over-their-holonomy-group`,
cited below as HOL.

* `U` is a unique game with alphabet `[k]` on a connected weighted graph
  `G = (V, E, w)`. Let `lambda(U)` be the total weight of its self-loops, as a
  fraction of all the weight.
* `g` is the tree gauge and `H = Mon_r(U)` is the holonomy group (HOL 2).
* `O_1, ..., O_t` are the orbits of `H`, and `U_i` is the orbit game (HOL 4).
* Fix `o_i in O_i`. Put `H_i = H|_(O_i)`, a transitive group, and
  `K_i = Stab_(H_i)(o_i)`.
* The **lift** `L_i` is the left-shift game over the group `H_i`, with alphabet
  `H_i`, on the same graph with the same weights, with constraint
  `h_v = gamma_e h_u` on `e = (u, v)`, where `gamma_e = pi_e^g|_(O_i)`.
  Here `gamma_e` lies in `H_i` by HOL 2.

A **left-shift game over a finite group `A`** is a unique game with alphabet
`A` whose every constraint reads `x_v = b_e x_u` for some `b_e in A`.

**Theorem.**

1. *(Projection.)* The map `p_i : H_i -> O_i`, `a -> a(o_i)`, is onto. Its
   fibres are the left cosets `a K_i`, and `p_i(gamma a) = gamma(p_i(a))`.
   Hence every labeling `h` of `L_i` gives the labeling
   `sigma_v = g_v^(-1)(p_i(h_v))` of `U`. This `sigma` satisfies every edge
   that `h` satisfies, so `val_U(sigma) >= val_(L_i)(h)`. In particular
   `val(L_i) <= val(U_i) <= val(U)`.
2. *(Random lift.)* Let `tau` be any labeling of `U_i`. Choose each `h_v`
   uniformly and independently in the fibre `p_i^(-1)(tau_v)`. Then every
   non-loop edge that `tau` satisfies is satisfied by `h` with probability
   exactly `1/|K_i|`, and no edge that `tau` violates is satisfied. So
   `val(L_i) >= (val(U_i) - lambda(U)) / |K_i|`.
3. *(Sizes.)* `|H_i| <= |O_i|!`, `|K_i| = |H_i|/|O_i| <= (|O_i| - 1)!`,
   `t <= k`, and `t |K_i| <= k!`. On a loopless graph, items 2 and 4 of HOL give
   `max_i val(L_i) >= val(U) / k!`.
4. *(Polynomial time.)* For fixed `k`, the gauge, the orbits, the groups
   `H_i`, their multiplication tables and all `t` lifts are computed in time
   `poly(|E|)`. Each `H_i` is the closure of at most `|E|` generators and has
   at most `k!` elements.
5. *(Equivalence on a host class.)* Let `C` be any class of weighted loopless
   graphs. Say that **UG is easy on `C` at `(k, c)`** if some `delta > 0` and a
   polynomial-time algorithm find, on every unique game with alphabet `k` on a
   graph in `C` with value `>= c`, a labeling of value `>= delta`. Say that
   **`A`-shift games are easy on `C` at `c`** in the same way, for left-shift
   games over `A`. Then the following are equivalent:
   - (a) UG is easy on `C` at every `(k, c)` with `c > 0`;
   - (b) for every finite group `A`, `A`-shift games are easy on `C` at every
     `c > 0`.

   More precisely, if `A`-shift games are easy at `c/k!` for every transitive
   permutation group `A` of degree at most `k`, then UG is easy at `(k, c)`.
   Conversely, UG easy at `(|A|, c)` makes `A`-shift games easy at `c`.
6. *(Gap form.)* For every `c > s`, the map `U -> (L_1, ..., L_t)` is a
   host-preserving disjunctive reduction from `Gap-UG_k[c, s]` to
   `Gap-Shift[c/k!, s]` over groups of order at most `k!`. On YES instances some
   `L_i` has value `>= c/k!`. On NO instances every `L_i` has value `<= s`.
   Every holonomy class is preserved. Solvable, nilpotent or abelian `H` gives
   solvable, nilpotent or abelian `H_i`.

**Why a loss is needed.** A transitive orbit game with non-regular `H_i` is a
coset game on `H_i / K_i`, not a shift game (HOL 5). The lift is the passage
from the covering of `G` defined by `U_i` to the associated principal
`H_i`-bundle. Its satisfied edges are exactly those satisfied in the covering
with the correct element of `K_i`. The factor `1/|K_i|` is exact for the random
fibre choice (item 2). This node does not determine whether a better choice
than random fibres always loses less. That does not matter for the equivalence
(item 5), because the algorithms concerned work at every constant
completeness.

## What it changes (impact types 2 and 3)

**New decomposition.** Consider the Bafna--Minzer question, footnote 2 on
page 4 and Problem 1 on page 11 of arXiv:2304.07284: is general UG easy on
their globally hypercontractive hosts? By item 5, it is *exactly* the question
whether their algorithm extends from `Z_q` to shift games over arbitrary finite
groups. The permutation constraints no longer matter; only the group
structure of the alphabet does. The holonomy ladder R1--R4 of
`general-unique-games-easy-on-globally-hypercontractive-graphs` becomes a
ladder over group classes:

* R1 is cyclic groups (proved);
* R2 is abelian groups;
* R3 is solvable groups;
* R4 is all finite groups.

Each rung keeps its own host. The step from coset games to shift games, which
HOL left as the survivor, costs only a constant.

**Class kill (conditional form).** Any host-preserving UG hardness proof on a
host class `C` at constant completeness `c`, with alphabet `k`, yields the same
hardness for shift games over transitive groups of degree `<= k` on `C`, at
completeness `c/k!` (item 6). So, on any class where group-shift games are
easy, no such proof exists, whatever its constraint permutations. The
invariant is the group `H_i` up to isomorphism. The step where every member
dies is completeness: the YES instance lifts to a shift game of value
`>= c/k!`, which the shift-game algorithm then rounds.

**What it does not say.** It gives no algorithm by itself. The shift-game side,
for non-cyclic groups on the Bafna--Minzer hosts, is
`group-shift-games-easy-on-globally-hypercontractive-graphs`, which is OPEN.
The lift also does not preserve the completeness regime `1 - eps`: it lands at
`(1 - eps)/k!`. So it transfers low-completeness algorithms (Bafna--Minzer
Theorems 1.6--1.8), not Theorem 1.5.

**Artifact.** `check_coset_lift.py` Part A runs in about 5 s. It covers 30
disguised unique games whose holonomy is `S_3` on 3 points, `S_4`, `A_4` or
`D_4` on 4 points, or intransitive `S_3 x Z_2` on 3 + 2 points. 23 of the 30
have a non-regular orbit. On each it checks items 1--3 by exhaustive search over
all labelings of `U`, `U_i` and `L_i`, and checks item 2 by averaging exactly
over every fibre choice.
