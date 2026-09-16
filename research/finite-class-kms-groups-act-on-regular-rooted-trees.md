---
rg: 2
id: finite-class-kms-groups-act-on-regular-rooted-trees
kind: claim
title: "KMS machine groups with stop relations and finite semigroup classes are residually bounded-prime solvable and act faithfully on a regular rooted tree"
distinct_from:
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that is the open hole asking for a finitely presented residually finite group with no faithful regular-tree action; this shows that one family of candidates, the corrected KMS groups of finite-class machines (including universally halting clocked machines), does act faithfully on a regular rooted tree, so it cannot witness the hole.
  pumped-halting-clocked-minsky-group-is-residually-finite: that proves residual finiteness of the pumped groups G_0(P(M)), whose semigroup classes are infinite, with no control on the primes of the finite quotients; this bounds those primes for the finite-class groups G_0(M), imports only that claim's clause 1 as a source of finite classes, and does not cover the pumped groups.
  kms-hard-fp-rf-groups-lie-in-apapa-variety: that imports membership of the hard KMS groups in the variety A_p^2 A, which does not bound the prime divisors of their finite quotients; this bounds them and derives a regular-tree action.
  kms-group-with-stop-relations-simulates-all-words: that identifies the abelian normal subgroup of G_0(M) with the basis group of the KMS model; this uses that identification to build finite solvable quotients with bounded primes.
artifacts:
  - research/artifacts/kms-groups-bounded-factors-2026-09-16.md
---

Let `M` be a Minsky machine with `K >= 1` glasses, deterministic or not, and let
`p` be a prime. Let `G_0(M)` be the KMS group of arXiv:1204.6506v5 §4.1 with the
stop relations `x_(q_0 w) = 1` added, as in
[[kms-group-with-stop-relations-simulates-all-words]]. It is finitely presented.

**Hypothesis (FC), finite classes.** Every nonzero `q`-element of the semigroup
`S(M)` is represented by only finitely many elements of the machine-free
semigroup `Š` (the semigroup `S(M)` without its Minsky relations).

**Constants.**

```text
chi(x)  = x^3 - 2x^2 + x + 1,    chi(x+1) = x^3 + x^2 + 1,
n_0(p)  = lcm of the multiplicative orders of the roots of chi(x) and chi(x+1) in F_p-bar,
q_p     = 4 if p = 2,   q_p = p if p is odd,
pi(p)   = {p} u primes(n_0(p)) u primes(q_p - 1),
d(p)    = max pi(p).
```

`n_0(p)` divides `lcm(p-1, p^2-1, p^3-1)`.

**Claim.** Clauses 1 and 2 assume (FC). Clause 3 does not.

1. **Bounded-prime residual solvability.** For every `g != 1` in `G_0(M)` there
   is a finite solvable quotient of `G_0(M)` in which `g` survives, and whose
   order has all prime divisors in `pi(p)`.
2. **Regular tree action.** `G_0(M)` acts faithfully on the rooted
   `d(p)`-regular tree: on `T_7` for `p = 2` and on `T_3` for `p = 3`. So
   condition (N1) of `every-fp-rf-group-embeds-in-fp-self-similar-group` holds
   for `G_0(M)` with `d = d(p)`.
3. **Where (FC) holds, and where it fails.**
   - (FC) holds when `M` is a simple deterministic Minsky machine clocked by a
     glass `tau` (as in `pumped-divergent-minsky-word-lies-in-profinite-kernel`)
     and universally halting, by clause 1 of
     `pumped-halting-clocked-minsky-group-is-residually-finite`. For such `M`,
     `G_0(M)` is finitely presented, residually finite and acts faithfully on
     `T_(d(p))`. None of these groups witnesses
     `some-fp-rf-group-acts-on-no-regular-rooted-tree`.
   - (FC) does not follow from sym-universal halting. The 2-glass machine

     ```text
     1; e_1 > 0 -> Sub(1); 1        1; e_1 = 0 -> 2
     2; e_2 > 0 -> Sub(2); 1        2; e_2 = 0 -> 0
     ```

     has stop configuration `(0; 0, 0)`. It is deterministic and
     sym-universally halting. In `S(M)` the element
     `q_1` is nonzero and equals `q_1 a_1^x` for every `x >= 0`. So `q_1` has
     infinitely many representatives in `Š` and infinitely many divisors
     `a_1^x`, and KMS v5 Lemma 3.5(a) (`l:fd`) is false as stated.

| p | n_0(p) | pi(p) | d(p) |
|---|---|---|---|
| 2 | 7 | {2, 3, 7} | 7 |
| 3 | 8 | {2, 3} | 3 |
| 5 | 62 | {2, 5, 31} | 31 |
| 7 | 114 | {2, 3, 7, 19} | 19 |
| 11 | 60 | {2, 3, 5, 11} | 11 |
| 13 | 168 | {2, 3, 7, 13} | 13 |

**Not covered.**
- The group `G(M)` as displayed in KMS, without the stop relations.
- The pumped groups `G_0(P(M))` of
  `pumped-halting-clocked-minsky-group-is-residually-finite`, whose classes are
  infinite.
- Machines without (FC), such as the machine in clause 3.
- The sym-universally halting machines behind KMS Theorems 4.17 and 4.18, and
  the machines `M_n` of the proof of KMS Theorem 4.19. Whether they satisfy
  (FC) was not checked. KMS derive the finiteness they need from Lemma 3.5(a),
  which clause 3 refutes in general.

Proof, experiment and weakest points:
`research/artifacts/kms-groups-bounded-factors-2026-09-16.md`, with the check
script in `experiments/kms-groups-bounded-factors-2026-09-16/`.

DERIVATION
[[finite-class-kms-groups-act-on-regular-rooted-trees-proof]]
