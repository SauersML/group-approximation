---
rg: 2
id: fp-rf-groups-with-non-primitive-recursive-word-problem
kind: claim
title: There are finitely presented residually finite (solvable, class 3) groups whose word problem is decidable but not primitive recursive; this answers Kourovka Problem 5.15 positively, from Kharlampovich–Myasnikov–Sapir
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED** as a literature answer. The main input is cited and was read at source:
Kharlampovich–Myasnikov–Sapir, *Algorithmically complex residually finite groups*,
arXiv:1204.6506v5 (Bull. Math. Sci. 2017), TeX in the swarm scratchpad at
`gq/src/kms/KMS-322.tex`. The deduction below is a lane proof, not reviewed.

The Kourovka Notebook, 21st issue (2026), still lists 5.15 among the unsolved problems,
with no comment. No priority is claimed for the observation that KMS answers it.

## Statement

Kourovka 5.15 (F. B. Cannonito) asks: do there exist finitely presented residually
finite groups with recursive, but not primitive recursive, solution of the word
problem? **Yes.**

## Inputs from KMS (read at source)

- **Theorem `t:rfg`.** For every recursive function `f` there is a residually finite,
  finitely presented group `G`, solvable of class 3, with Dehn function greater than
  `f`. In addition one can assume that the word problem in `G` "is at least as hard
  as the membership problem in a given recursive set of natural numbers `Z`".
- **How that hardness is produced.**
  - Theorem `t:rfg1`: for a sym-universally halting Minsky machine `M`, `G(M)` is
    residually finite and its word problem is at least as hard as the halting problem
    for `M`.
  - Theorem `t:MM` (b), (d): for recursive `Z` there is a sym-universally halting
    3-glass Minsky machine that, started on the configuration `(1; m, 0, …, 0)`, halts
    iff `m ∈ Z`.
  - Theorem `tmm` (b): the halting question becomes an equality in `G(M)` of explicit
    words `x_{q_i A_0} * a_1^{(m_1)} * … * A_K^{(α_K)}`, one built from each
    configuration.

## Proof

1. **A recursive set that is not primitive recursive.** Let `φ_0, φ_1, …` be an
   effective enumeration of the unary primitive recursive functions. Put
   `Z = {n : φ_n(n) = 0}`.
   - `Z` is recursive, since the `φ_n` are total and uniformly computable.
   - `Z` is not primitive recursive: if `χ_Z = φ_k`, then `k ∈ Z ⟺ φ_k(k) = 0 ⟺ k ∉ Z`.
2. **The group.** Apply KMS Theorem `t:rfg` to this `Z`, giving a finitely presented,
   residually finite, solvable group `G`.
   - Its word problem is decidable, by McKinsey's algorithm: finitely presented plus
     residually finite (KMS §1).
   - The reduction of `Z` to the word problem sends `m` to the explicit pair of words
     attached by Theorem `tmm` (b) to the configuration `(1; m, 0, …, 0)` and to the
     halting configuration.
   - This map `m ↦ (word pair)` is primitive recursive: the words are built from `m`
     by the operations `f*a_i = f^{-1} f^{a_i} f^{-a_i^{-1}} f^{(a_i')^{-1}}` and
     `f*A_i = [f, A_i]` of KMS §`s:4` (relation G8), with `t*a^{(m)}` the `m`-fold
     iterate. Each `*a_i` multiplies length by at most 4, so the words have length
     `O(4^m)` and are primitive recursive in `m`. This is checked by inspection of the
     definitions, not by a KMS statement.
3. **Conclusion.** Suppose the word problem of `G`, for some finite presentation and a
   standard Gödel numbering of words, had a primitive recursive characteristic
   function. Composing it with the primitive recursive reduction would make `χ_Z`
   primitive recursive, contradicting step 1.
   - The class of primitive recursive predicates is independent of the finite
     presentation, since changing generators is a primitive recursive substitution.
   - So `G` has recursive but not primitive recursive word problem. ∎

## Remarks

- **Time complexity.** KMS also give this through time complexity. Their introduction
  states: for every recursive `f`, the time complexity of both the "yes" and "no"
  parts of the word problem is at least `f(n)`, for any finite presentation. Taking
  `f` to be the Ackermann function gives the same conclusion, because a primitive
  recursive decision procedure runs in primitive recursive time.
- **Link to 7.19.** Kourovka 7.19 (an explicit finitely presented *simple* group with
  word problem not primitive recursive) now reduces to one question: does one of
  these explicit KMS groups `G(M)` embed in an explicit finitely presented simple
  group?
  - Inclusion of generators is a primitive recursive substitution, so any such simple
    host inherits the non-primitive-recursive word problem.
  - The `G(M)` are finitely presented, solvable of class 3, in `A_p^2 A ∩ Z N_{K+1} A`
    (KMS Theorem `tmm` (a)). A grep of main found no Boone–Higman node for them.
