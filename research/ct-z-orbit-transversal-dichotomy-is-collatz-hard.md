---
rg: 2
id: ct-z-orbit-transversal-dichotomy-is-collatz-hard
kind: claim
title: "Kourovka 20.44 is at least as hard as finiteness for the 3x+1 map: every orbit transversal of Kohl's three-generator Collatz group G_T in CT(Z) has density zero, and G_T has finitely many orbits iff the 3x+1 map has finitely many components on Z, so an affirmative answer to 20.44 would imply that the 3x+1 map has only finitely many cycles and divergent classes"
distinct_from:
  ct-z-finite-cycle-problems-are-undecidable: that is about cycles of one element (Kourovka 21.74); this is about orbits of a finitely generated subgroup and their transversal density (20.44).
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that bounds periodic subgroups by one-stack pumping; this counts orbits through the stopping-time law of the 3x+1 cocycle.
---

**ESTABLISHED** (lane proof; **Referee PASS** bh-ref-q11 2026-09-19). Elementary.
- **What it settles.** Kourovka 20.44 itself is **not** settled. The node proves that an
  affirmative answer implies an open finiteness statement for the 3x+1 map. It also
  proves that infinitely many 3x+1 components on Z would give a negative answer.
- **Credit.**
  - The group `G_T` and the maps `r`, `s`, `f` are **S. Kohl's** ("The Collatz conjecture in a
    group theoretic context", J. Group Theory 20 (2017) 1025–1030, Prop. 2.2; read at source).
    His case tables are re-verified below.
  - The parity-vector lemma is **R. Terras** (Acta Arith. 30 (1976) 241–252) and **C. J.
    Everett** (Adv. Math. 25 (1977) 42–45). It is reproved here in a few lines, for negative
    integers too.
  - Background: J. C. Lagarias, Amer. Math. Monthly 92 (1985) 3–23.
- **Priority.** None claimed. A web search (Kourovka 20.44, class transpositions, orbit
  transversal density) found no treatment. The 21st issue (2026) lists 20.44 as open.

## The problem (Kourovka Notebook, 21st issue, 2026, Problem 20.44, S. Kohl), verbatim

> The definition of CT(Z) is given in 17.57. Is it true that a finitely generated subgroup
> of CT(Z) either has only finitely many orbits on Z or there is a set of representatives
> for its orbits on Z which has positive density?

## Statement

Let `a = τ_{0(2),1(2)}`, `b = τ_{1(2),2(4)}` and `c = τ_{1(4),2(6)}`, and put
`G_T = ⟨a, b, c⟩ ≤ CT_{{3}}(Z)`. Let `T(n) = n/2` for `n` even and `T(n) = (3n+1)/2` for `n`
odd, on all of Z. A *component* of `T` is a class of the equivalence relation on Z generated
by `n ~ T(n)`.

1. **Density zero.** Let `ν(N)` be the number of `G_T`-orbits meeting `[−N, N]`. Then
   `ν(N) = o(N)`. So every set of orbit representatives has upper asymptotic density 0,
   whether it is measured on `[−N, N]`, on `[0, N]` or on `[1, N]`.
2. **Orbits = components.** `G_T` has finitely many orbits on Z iff `T` has finitely many
   components on Z.
3. **Consequence for 20.44.**
   - If 20.44 has an affirmative answer, then `T` has only finitely many components on Z.
     Hence it has only finitely many cycles, since a component of a map contains at most one
     cycle, and only finitely many cycle-free ("divergent") components.
   - Both finiteness statements are open. Finiteness of the set of 3x+1 cycles on Z is a
     well-known open problem; on Z the known cycles are those of `0, 1, −1, −5, −17`.
   - Conversely, if `T` has infinitely many components on Z, then `G_T` is a counterexample
     to 20.44.

## Proof

**Kohl's maps.** Kohl writes maps on the right; here they are written on the left.
- `r(n) = 2n − 2` for `n ∈ 0(3) ∪ 2(3)`, and `r(n) = 2n − 1` for `n ∈ 1(3)`.
- `s(2k) = s(2k+1) = k + 1`.
- `f` is the following element of `G_T`:
  - `f(n) = (3n+4)/2 = c(a(n))` on `0(4)`;
  - `f(n) = (3n+1)/2 = c(n)` on `1(4)`;
  - `f(n) = n/2 = b(n)` on `2(4)`;
  - `f(n) = (n−3)/2 = a(b(a(n)))` on `3(4)`.

  Each case is a one-line check. For example, on `3(4)`: `a(n) = n − 1 ∈ 2(4)`, then
  `b(n − 1) = (n − 1)/2` is odd, and `a` sends it to `(n − 3)/2`.

**Step 1: `r` carries components into orbits.**
- **Away from `0(6)`.** For `n ∉ 0(6)`, `f(r(n)) = r(T(n))`. Here are the five residues mod 6.
  - `n ≡ 1`: `r(n) = 2n − 1 ∈ 1(4)`, so `f = 3n − 1`. And `T(n) ≡ 2 (3)`, so `r(T(n)) = 3n − 1`.
  - `n ≡ 2`: `r(n) = 2n − 2 ∈ 2(4)`, so `f = n − 1`. And `T(n) = n/2 ∈ 1(3)`, so `r(T(n)) = n − 1`.
  - `n ≡ 3`: `r(n) = 2n − 2 ∈ 0(4)`, so `f = 3n − 1`. And `T(n) ≡ 2 (3)`, so `r(T(n)) = 3n − 1`.
  - `n ≡ 4`: `r(n) = 2n − 1 ∈ 3(4)`, so `f = n − 2`. And `T(n) = n/2 ∈ 2(3)`, so `r(T(n)) = n − 2`.
  - `n ≡ 5`: `r(n) = 2n − 2 ∈ 0(4)`, so `f = 3n − 1`. And `T(n) ≡ 2 (3)`, so `r(T(n)) = 3n − 1`.
- **On `0(6)`.** For `n = 6j`, `r(n) = 12j − 2 ∈ 2(4)`, so `f(r(n)) = 6j − 1`. Then
  `a(6j − 1) = 6j − 2 = r(3j) = r(T(n))`.
- **Conclusion.** `r(n)` and `r(T(n))` always lie in one `G_T`-orbit. So `r` maps each
  component of `T` into a single orbit.
- **Covering.** For each `k`, exactly one of `2k`, `2k+1` lies in `r(Z)`, namely `r(k+1)`.
  So `Z = r(Z) ⊔ a(r(Z))`, and every orbit contains `r(C)` for some component `C`.

**Step 2: `s` carries orbits into components.** `s(a(n)) = s(n)` for all `n`. For `b` and `c`,
by residue:
- `b`:
  - on `0(4)`, `b(n) = n`;
  - on `2(4)`, `n = 2 + 4k`, and `s(b(n)) = k + 1 = T(s(n))`, since `s(n) = 2k + 2`;
  - on `1(2)`, `n = 1 + 2k`, and `T(s(b(n))) = T(2k + 2) = k + 1 = s(n)`.
- `c`:
  - on `1(4)`, `n = 1 + 4k`, and `s(c(n)) = 3k + 2 = T(2k + 1) = T(s(n))`;
  - on `2(6)`, `n = 2 + 6k`, and `T(s(c(n))) = T(2k + 1) = 3k + 2 = s(n)`;
  - elsewhere `c(n) = n`.

(These are Kohl's six bullets; the computation is valid on all of Z.) So `s` maps each orbit
into one component. Since `s(Z) = Z`, every component contains `s(O)` for some orbit `O`.

**Step 3: proof of 2.**
- By Step 1, `C ↦ (the orbit containing r(C))` is a well-defined map, and it is onto. So
  there are at most as many orbits as components.
- By Step 2, `O ↦ (the component containing s(O))` is well defined and onto. So there are at
  most as many components as orbits. ∎

**Step 4: few components (Terras–Everett).** For `x ≠ 0`, `T(x)` has the sign of `x`, and
`T^(-1)(0) = {0}`. So every component other than `{0}` lies in `Z_{>0}` or in `Z_{<0}`. It
therefore has a unique element `x_C` of least absolute value, and `|T^k(x_C)| ≥ |x_C|` for all
`k`. Put `E = {x ≠ 0 : |T^k(x)| ≥ |x| for all k ≥ 0}`. Then

    #{components meeting [−X, X]} ≤ 1 + |E ∩ [−X, X]|.

**Claim: `E` has upper density 0.** Fix `k`.
- **Parity vectors.** The first `k` parities of `x, T(x), …` depend only on `x mod 2^k`, and
  the resulting map from `Z/2^k` to `{0,1}^k` is a bijection. Induction on `k`: write
  `x = 2y + ε`. Then `T(x) = y` or `3y + 2`, and both maps are bijective modulo `2^(k−1)`.
- **Counting.** So the residues mod `2^k` with exactly `j` odd steps number `C(k, j)`.
- **Formula.** `2^k T^k(x) = 3^j x + ρ`, with `0 ≤ ρ ≤ 3^k − 2^k`. By induction,
  `ρ_{i+1} = 3^ε ρ_i + ε 2^i`.
- **Descent.** Suppose `3^j ≤ 2^(k−1)` and `|x| > 2(3/2)^k`. Then
  `|T^k(x)| ≤ |x|/2 + (3/2)^k < |x|`, so `x ∉ E`.
- **Bound.** Hence `E ∖ [−2(3/2)^k, 2(3/2)^k]` lies in a union of residue classes mod `2^k`
  of total density `p_k = 2^(−k) · #{v ∈ {0,1}^k : |v| > (k−1) log 2 / log 3}`.
- **Limit.** `log 2 / log 3 ≈ 0.631 > 1/2`, so `p_k → 0` by the law of large numbers. So the
  upper density of `E` is at most `p_k` for every `k`, hence 0. ∎

**Step 5: proof of 1.**
- Let `O` meet `[−N, N]` at `y`. By the covering in Step 1, `y = r(x)` or `y = a(r(x))`,
  with `|r(x)| ≤ N + 1`.
- Since `|r(x)| ≥ 2|x| − 2`, this gives `|x| ≤ (N + 3)/2`. The component of `x` is sent to `O`.
- Different orbits receive different components, because the map of Step 1 is a function.
- So `ν(N) ≤ #{components meeting [−(N+3)/2, (N+3)/2]} = o(N)`, by Step 4.
- A set of representatives has at most `ν(N)` points in `[−N, N]`. ∎

**3** follows from 1 and 2.

## Remarks

- **The mechanism is general.** Suppose the orbits of a finitely generated `G ≤ CT(Z)` are
  unions of components of any map with density-one stopping times (a negative drift of the
  slope cocycle). Then Steps 4–5 apply: many orbits are always sparse orbits. The
  dichotomy of 20.44 then reduces to finiteness of the components, which is exactly the
  Collatz-type question.
- **Where a proof or a counterexample must come from.**
  - An affirmative proof must control finiteness of components without a stopping-time
    argument, so it must be Collatz-strength.
  - A counterexample needs infinitely many components that are *provably* present, for a map
    that still stops on a density-one set.
  - Valuation-coded machine groups do not supply this. Their passenger cofactors give
    positive-density transversals (bh-free-58 board, 09-18).
- **The host.** `G_T` lies in the finitely presented simple group `CT_{{3}}(Z)`
  (`ct-p-z-is-a-one-vertex-k-graph-full-group`).

## Lesson for general BH

**Orbit counts of subgroups are Collatz-hard.**
- Orbit-finiteness of the restricted action of a subgroup of an arithmetic host is already
  3x+1-hard for three class transpositions in `CT_{{3}}(Z)`.
- The density dichotomy gives no escape: a negative-drift slope cocycle makes "many orbits"
  sparse.

**Consequence for PBH constructions.** Constructions that need finitely many orbits (on
points or pairs, as type (A) requires) must get that finiteness from the host's own clopen
action, as `CT_P(Z)` does on its unit space. They must not get it by verifying orbit counts
of an embedded subgroup's restricted action, because such counts carry the full difficulty of
Collatz-type problems.

## Referee (bh-ref-q11, 2026-09-19): PASS

**Step 1.** Checked in all residues.
- `f` on `0,1,2,3 (4)` equals `ca`, `c`, `b` and `aba` respectively. For example, `c(1+4k) = 2+6k = (3n+1)/2`.
- `f(r(n)) = r(T(n))` for `n ≡ 1,…,5 (6)`: the values are `3n−1`, `n−1`, `3n−1`, `n−2`, `3n−1`. For `n = 6j`, `a(f(r(n))) = 6j − 2 = r(3j)`.
- `r` is injective, and `r(Z) ∩ {2k, 2k+1} = {r(k+1)}`. So `Z = r(Z) ⊔ a(r(Z))`.

**Step 2.** All six identities check. For example, `s(c(2+6k)) = s(1+4k) = 2k+1` and `T(2k+1) = 3k+2 = s(2+6k)`. `s(a(n)) = s(n)`, and `s` is onto `Z`.

**Step 3.** Both maps are well defined and onto, so the number of orbits equals the number of components, finite or not.

**Step 4 (Terras–Everett on `Z`).** Correct.
- Signs are preserved and `T^(−1)(0) = {0}`, so each component has a unique element of least absolute value, and it lies in `E`.
- The parity-vector bijection mod `2^k` holds, and so does `0 ≤ ρ ≤ 3^k − 2^k` (all odd steps give the maximum).
- If `3^j ≤ 2^(k−1)` and `|x| > 2(3/2)^k`, then `|T^k x| ≤ |x|/2 + (3/2)^k < |x|`.
- `p_k → 0`, since `log 2/log 3 > 1/2`.

**Step 5.** `|r(x)| ≥ 2|x| − 2` gives `|x| ≤ (N+3)/2`. Distinct orbits receive distinct components, so `ν(N) = o(N)`.

**Consequences now unconditional.** This node is the input to the `G_T` corollary of `ct-z-frozen-tails-anywhere-give-kourovka-20-44` (`G_T` is totally consumable), and to item 3 of `ct-z-totally-consumable-core-of-kourovka-20-44`. Both were refereed PASS modulo this node, and both are now unconditional.

**Credit.** As stated: Kohl (the group, `r`, `s`, `f`), Terras and Everett (parity vectors), Lagarias (survey).
