---
rg: 2
id: residual-solvability-reduces-cgp-question-1-to-question-3
kind: claim
title: If Cornulier--Guyot--Pitsch Question 3 has a positive answer then every finitely generated residually solvable group, in particular every Baumslag--Solitar group, is a limit of isolated groups; so a single Baumslag--Solitar group that is not such a limit answers Questions 1 and 3 negatively at once
requires:
  - limits-of-isolated-groups-basic-closure
  - baumslag-solitar-groups-are-free-by-metabelian
distinct_from:
  every-fg-solvable-group-is-a-limit-of-isolated-groups: that is Question 3 itself; this shows it already implies Question 1 on all residually solvable groups, and names the pivot test groups.
  every-decidable-group-is-a-limit-of-isolated-groups: that is Question 1; this reduces its residually solvable case to Question 3.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed).

**Statement.** Let `L` be the class of finitely generated groups that are limits of isolated
groups in the space of marked groups (Cornulier--Guyot--Pitsch, arXiv:math/0511714v2).
1. `L` is closed in each space `G_m` of marked groups, and membership does not depend on the
   marking.
2. If every finitely generated solvable group lies in `L` (a positive answer to CGP Question 3,
   `every-fg-solvable-group-is-a-limit-of-isolated-groups`), then every finitely generated
   residually solvable group lies in `L`.
3. In particular, a positive answer to Question 3 puts every Baumslag--Solitar group `BS(m,n)`
   (`m, n ≠ 0`) in `L`.
4. Contrapositive. If some `BS(m,n)` is not a limit of isolated groups, then Question 1 fails
   at `BS(m,n)` (it has solvable word problem), and Question 3 fails at one of its solvable
   quotients `BS(m,n)/BS(m,n)^(k)`.
5. For `G = BS(m,n)` not residually finite (`|m|, |n| ≥ 2` and `|m| ≠ |n|`, Meskin; e.g.
   `BS(2,3)`), the solvable quotients `G/G^(k)` are not LEF for all large `k`. So the test groups
   in item 4 are finitely generated solvable non-LEF groups, exactly the part of Question 3 that
   the residually finite case does not reach.

**Proof.**
1. `L` is by definition the closure of the set of isolated marked groups, hence closed. Marking
   independence is item 1 of `limits-of-isolated-groups-basic-closure`.
2. Let `G = ⟨S⟩` be residually solvable. Its derived series satisfies `⋂_k G^(k) = 1`, so the
   marked quotients `(G/G^(k), S)` converge to `(G, S)` (a word is trivial in `G/G^(k)` for all
   large `k` iff it is trivial in `G`). Each `G/G^(k)` is finitely generated and solvable, so it
   lies in `L` by hypothesis, and `G ∈ L` because `L` is closed.
3. `BS(m,n)` is residually solvable by `baumslag-solitar-groups-are-free-by-metabelian`.
4. `BS(m,n)` has solvable word problem (it is a one-relator group, Magnus). If it is not in
   `L`, then by the argument of item 2 not all `G/G^(k)` lie in `L`.
5. The class of LEF marked groups is the closure of the finite marked groups, hence closed. A
   finitely presented LEF group is residually finite, so a finitely presented non-residually-finite
   `G` is not LEF. Its complement being open, `G/G^(k) → G` forces `G/G^(k)` to be non-LEF for all
   large `k`.

**Reading.** `BS(2,3)` is therefore a pivot. A proof that it is a limit of isolated groups is
implied by (and weaker than) a positive answer to Question 3. A proof that it is not would settle
Questions 1 and 3 negatively at once, and would locate the Question 3 counterexample among its
derived quotients.
