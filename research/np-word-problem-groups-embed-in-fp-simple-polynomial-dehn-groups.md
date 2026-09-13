---
rg: 2
id: np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups
kind: claim
root: true
title: Every finitely generated group with word problem in NP embeds in a finitely presented simple group with polynomial Dehn function
distinct_from:
  quantitative-higman-embedding-with-dehn-control: that is the Birget-Ol'shanskii-Rips-Sapir embedding, refined by Chornomaz-Wagner, into a finitely presented group with polynomial Dehn function and no simplicity; this asks for a simple host.
  boone-higman-conjecture: that asks for a finitely presented simple overgroup of every decidable input, with no metric control; this asks it only for inputs with word problem in NP, but demands a polynomial Dehn function, so neither implies the other.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups beyond every recursive time bound; every host here has word problem in NP, so this problem lives under one recursive bound.
  twisted-btb-groups-poly-dehn-only-if-np-eq-conp: that rules out twisted Brin-Thompson hosts on infinite sets under NP != coNP; this is the open problem those hosts cannot solve.
artifacts:
  - research/artifacts/simple-bors-2026-09-13.md
---

**OPEN.** For every finitely generated group `G` whose word problem is in NP,
there is a finitely presented **simple** group `S` with polynomially bounded
Dehn function and `G <= S`.

**Why NP is the right class.** By Birget--Ol'shanskii--Rips--Sapir,
arXiv:math/9811106, Theorem 1.1 (TeX l.235--236): "the word problem of a
finitely generated group is in NP if and only if this group is a subgroup of a
finitely presented group with polynomial isoperimetric function". So any
polynomial-Dehn host, simple or not, can only contain inputs with word problem
in NP. This statement is that theorem with "simple" added to the host.

**What it would give.** Boone--Higman for every input with word problem in NP,
with polynomial Dehn control and a geometric certificate: van Kampen diagrams
of polynomial area in a simple group. That class contains every structured case
on main with polynomial-time word problem.

## Test case: BS(1,2)

`BS(1,2)` has word problem in P. BORS, TeX l.231: the word problem of every
finitely generated matrix group over Q is solvable in quadratic time, and
`BS(1,2) <= GL(2,Q)`. It satisfies Boone--Higman
(`baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`). The generator `a`
of `BS(1,2)` is exponentially distorted, since `a^(2^l) = t^l a t^(-l)`. As far
as this lane found, **no finitely presented simple group with polynomial Dehn
function containing BS(1,2) is known.** Every family checked is excluded or
unknown; see the Attempts below.

## Attempts

1. **Twisted Brin--Thompson envelopes (BFFHZ, Zaremsky): excluded unless
   NP = coNP.** `twisted-btb-groups-poly-dehn-only-if-np-eq-conp`. They
   contain `2V`, whose word problem is coNP-complete (Birget), so their Dehn
   functions aren't polynomially bounded unless the classes collapse. This
   holds for every actor, so no choice of type (A) action repairs it.
2. **Röver--Nekrashevych envelopes: the Dehn function dominates the host's.**
   - Zaremsky, arXiv:2305.15176, TeX l.258, verbatim: "Let $G\le\Aut(\tree_d)$ be a finitely generated,
     persistent, weakly diagonal, rational, self-similar group. Then $V_d(G)$ is
     virtually simple by virtue of $[V_d(G),V_d(G)]$ being simple and finite
     index, and there exists a quasi-retraction $V_d(G)\to G$."
   - With the Alonso citation at TeX l.177--178 (a quasi-retract `H` of `G` has
     `δ_H ≼ δ_G`), the envelope's Dehn function is at least the host's.
   - Zaremsky's own self-similar `BS(1,n)` hosts give fp simple groups with
     "Dehn functions [that] are at least exponential" (abstract, TeX l.102).
   - So this route needs a self-similar host `G` with his four properties,
     containing the input and having polynomial Dehn function.
   - Subgroups of `Aut(T_d)` are residually finite, since level stabilizers
     have finite index. So this route only reaches residually finite inputs.
   - For `BS(1,2)`, the polynomial affine hosts on main
     (`polynomial-parameter-affine-groups-are-self-similar`) contain it, but
     their Dehn functions and the four properties are unchecked.
3. **`T`, `T_n`, `V`: they only contain inputs with undistorted cyclic subgroups.**
   - `T` and every Higman--Thompson `T_n` have quadratic Dehn function
     (arXiv:2410.23088, abstract TeX l.19).
   - Cyclic subgroups are undistorted in `V`. This was read through
     arXiv:2605.09763 TeX l.48 ("cyclic subgroups are undistorted in $V,$ so
     any subgroup of $V$ must also have undistorted cyclic subgroups"); the
     primary source wasn't re-read.
   - The same paper proves undistortion for the finitely presented simple
     Belk--Hyde--Matucci group `VA` (TeX l.54--57).
   - All of these exclude `BS(1,2)`.
4. **CAT(0) simple lattices (Burger--Mozes type): quadratic Dehn function, but
   no distorted cyclic subgroups.** Excluded for `BS(1,2)` by the solvable
   subgroup theorem. That import wasn't read at primary source in this lane.

5. **Röver--Nekrashevych over Cornulier--Tessera's quadratic host: reduces the
   BS(1,2) test case to two upper bounds** (lane `solve-bh-poly-dehn`,
   2026-09-13).
   - **Parameter hosts are not rational.** The polynomial parameter hosts with
     `k >= 1` (`polynomial-parameter-affine-groups-are-self-similar`) have
     infinitely many states: the elementary matrix with entry `t` gets states
     with `t`-coefficient `p^j` at depth `j`. So Zaremsky's Corollary at TeX l.258
     does not apply to them.
   - **A host that works.** Cornulier--Tessera's
     `Gamma_2 = Z[1/2]^2 x|_(2I,[[2,1],[1,1]]) Z^2` (arXiv:1003.0148, Theorem
     `gaga`, quadratic Dehn function, contains `BS(1,2)`) is a rational, weakly
     diagonal self-similar group on the 9-ary tree
     (`cornulier-tessera-host-is-rational-weakly-diagonal-self-similar`).
   - **The envelope.** `S = [V_10(Gamma_2), V_10(Gamma_2)]` is finitely
     presented and simple, and contains `BS(1,2)`
     (`bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host`). Only
     `δ_S ≽ n^2` is known.
   - **What's left.** The test case `bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function`
     now needs `rover-nekrashevych-dehn-polynomial-in-host-and-vd` (Zaremsky's
     stated suspicion, TeX l.128) and
     `higman-thompson-vd-has-polynomial-dehn-function` at `d = 10`. Both are
     open.

**Remaining gap.** A family of finitely presented simple groups with polynomial
Dehn function that contains distorted cyclic subgroups, and more generally the
BORS S-machine hosts. None was found in the checked literature. A literature
search found no simple version of Birget--Ol'shanskii--Rips--Sapir stated or
asked; it wasn't exhaustive.
