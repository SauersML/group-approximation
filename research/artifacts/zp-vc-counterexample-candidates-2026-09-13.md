# Counterexample candidates for Zaremsky Problem 1.7 (2026-09-13)

Lane `z1-07-vc-counter`.  This is the counterexample side of the
Juan-Pineda--Leary conjecture (Conjecture A) and the von Puttkamer--Wu
conjecture (Conjecture B).  For each candidate it records the hypothesis
that kills it.  Root: `zaremsky-1-07-juan-pineda-leary-conjecture` (lane
z1-07-vc-proof); known classes are in `zp-jpl-bvc-known-classes-2026-09-13.md`.

## Sources and how bounded the check was

- Read from the PDF: T. von Puttkamer and X. Wu, arXiv:1607.03790v2 (6 Apr 2019),
  pp. 1--18.  That covers Conjectures A and B, the BVC definition,
  Proposition 1.1, Lemmas 1.3--1.19, Lemma 2.4, Theorems 2.11 and 2.12,
  Proposition 3.2, Corollaries 3.3 and 3.4, Proposition 3.6, and Section 4 up
  to Lemma 4.15.
- Linear groups (vPW arXiv:1704.05304) and residually finite groups
  (Barnea--Camina--Ershov--Lewis arXiv:2210.15746) are recorded by the root
  node.  Not re-read by this lane.  This lane did no literature search after
  2019: the web search budget was exhausted and the arXiv API returned
  HTTP 429.
- In-repo: `every-wp-group-embeds-in-fp-conjugacy-finite-group` and
  `conjugacy-finite-recursive-presentation-solvable-wp` (Boone--Higman region).

## Structure

- A "no" to A forces a "no" to B (`bvc-counterexample-from-jpl-counterexample`).
- A "no" to B would follow from either of these unknown objects:
  - an infinite finitely presented torsion-free group with finitely many
    conjugacy classes
    (`bvc-counterexample-from-fp-torsion-free-few-class-group`);
  - a finitely presented infinite torsion group with BVC
    (`bvc-counterexample-from-fp-torsion-group-with-bvc`, which is Problem 1.11
    plus BVC).

## Candidate table

| Candidate | BVC? | Finitely presented? | Killed by |
|---|---|---|---|
| Osin's f.g. torsion-free groups with 2 conjugacy classes | yes (vPW Remark (a)) | no | finite presentation: a strict direct limit of quotients of a f.g. free group is infinitely presented |
| `O x Z`, `O` as above | yes, witnessed by `<(1,1)>`, `<(x_0,0)>`, `<(x_0,1)>` | no | finite presentation (`O = (O x Z)/Z` would be f.p.) |
| Higman--Neumann--Neumann countable groups with all nontrivial elements conjugate | yes | no, not even f.g. | finite generation |
| Small-cancellation torsion groups with few conjugacy classes | BVC not checked | no | finite presentation (limits); Problem 1.11 |
| Thompson's F | no | yes | `H_1 = Z^2` (vPW Ex. 1.16); `line-groups-with-bounded-support-lack-bvc` |
| `[F, F]` (simple) | no | no | `line-groups-with-bounded-support-lack-bvc` |
| T, V, `nV`, `V_{n,r}`, Röver--Nekrashevych groups | no | yes | unbounded finite subgroups (vPW Lemma 1.7) |
| Higman's group `<a,b,c,d | a^b=a^2, b^c=b^2, c^d=c^2, d^a=d^2>` | no | yes | `bvc-amalgams-have-two-transitive-vertex-actions` (`C\A/C` infinite) |
| `BS(1,n)`, virtually solvable groups | no | yes | vPW Prop. 1.12 |
| Non-ascending HNN extensions, e.g. `BS(m,n)` with `|m|, |n| >= 2` | no | varies | vPW Lemma 2.4 |
| HNN extensions of f.g. free groups, one-relator groups | no | yes | vPW Thm 2.11, Thm 2.12 |
| Hyperbolic, relatively hyperbolic, acylindrically hyperbolic, `MCG`, `Out(F_n)` | no | varies | vPW Prop. 3.2, Cor. 3.3, 3.4 |
| CAT(0) cube groups (incl. Burger--Mozes lattices on products of trees) | no | yes | vPW Thm 4.13 with Lemma 4.15 |
| Residually finite groups; f.g. linear groups | no | -- | as recorded in the root (BCEL 2210.15746; vPW 1704.05304) |

Checks for the `O x Z` row (`O` torsion-free, all nontrivial elements
conjugate, `x_0 != 1`):
- `(1, m)` lies in `<(1,1)>`;
- `(x, 0)` is conjugate to `(x_0, 0)`;
- for `x != 1` and `m != 0`, `x` is conjugate to `x_0^m != 1`, so `(x, m)` is
  conjugate to `(x_0, 1)^m`.

So BVC is compatible with an infinite cyclic quotient and with the
twisted-class condition of vPW Lemma 1.19.  Only finite presentation separates
this group from Conjecture B.

## What a Conjecture B witness must look like

`G` finitely presented, not virtually cyclic, with BVC.  Then:

1. `H_1(G; Z)` is finitely generated of rank at most one (vPW Cor. 1.15).
2. Finite subgroups have bounded order and lie in finitely many conjugacy
   classes (vPW Lemma 1.7).
3. No torsion-free quotient without BVC (vPW Lemma 1.14); in particular no
   acylindrically hyperbolic quotient (vPW Cor. 3.4).
4. BVC passes to finite-index subgroups (vPW Lemma 1.11).
5. Splittings:
   - HNN splittings are ascending (vPW Lemma 2.4).
   - If `G = H x|_phi Z`, then `H` has finitely many `phi^m`-twisted conjugacy
     classes for every `m != 0`.  Apply vPW Lemma 1.19 to the index-`m`
     subgroup `H x|_{phi^m} Z`, which has BVC by Lemma 1.11.
   - Amalgam splittings `A *_C B` are 2-transitive on both sides; with `C`
     finite the group is virtually free and dies
     (`bvc-amalgams-have-two-transitive-vertex-actions`).
6. No realization as a group of homeomorphisms of `R` without global fixed
   point with a compactly supported element having finitely many support
   components (`line-groups-with-bounded-support-lack-bvc`).
7. In the torsion-free subcase with finitely many conjugacy classes
   (`some-infinite-fp-torsion-free-group-has-finitely-many-classes`):
   - property FA;
   - every stable translation length vanishes in every isometric action, so
     every infinite-order element is distorted.

## Sharpest next targets

- **(T1)** Finitely presented, not virtually cyclic, not residually finite,
  with every infinite-order element distorted and property FA: a necessary
  shape for the torsion-free, finitely-many-classes route.  No such group is
  known to this lane.
- **(T2)** Ascending HNN extensions `H *_phi` with `H` not finitely generated,
  finitely many twisted classes for every power of `phi`, and bounded torsion.
  Every f.g. free base is excluded (vPW Thm 2.11).  The base must avoid
  property `R_infinity` for every power of `phi` (vPW Cor. 1.20).  This is the
  only HNN shape left.
- **(T3)** 2-transitive amalgams over infinite edge groups, e.g. vertex groups
  `k^+ x| k^x` acting on the affine line, or `PGL_2(k)` acting on the projective
  line.  Do they escape the necklace count at finer invariants?  Untested.
