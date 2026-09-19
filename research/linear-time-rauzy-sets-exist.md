---
rg: 2
id: linear-time-rauzy-sets-exist
kind: claim
title: There is a symmetric set A of integers, closed but not effectively closed in the profinite topology, whose complement is decidable in linear time from the unary input
distinct_from:
  effective-residual-finiteness-separator-for-boone-higman: that uses Rauzy's set, whose membership test factors the input and runs a machine; this gives a simpler set, symmetric under x -> -x, with a linear-time test in the value of the input, which is the form a machine element of a Brin-Thompson group can read.
  fp-simple-group-containing-a-non-efrf-residually-finite-group: that is the embedding question for Rauzy-type Dyson groups; this supplies the lamp set that makes it answerable.
---

**ESTABLISHED** (lane proof, elementary; no priority claimed). It is a variant of the lemma of
Rauzy, arXiv:2002.02540 (read at source, `gq/src/bh-invent-11/rauzy.tex`, lines 248–357). The
difference is that the sectors are 2-adic valuation classes and the halting information is stored
in one period.

## The set

- Fix a standard enumeration `M_0, M_1, ...` of Turing machines.
- Let `N_n ∈ N ∪ {∞}` be the number of steps `M_n` takes to halt on the empty input.
- For `n >= 0`, define a set `J_n` of odd integers:
  - if `N_n = ∞`, then `J_n` is the set of all odd integers;
  - if `N_n = N < ∞`, then `J_n = { j odd : j ≡ r (mod Q) for some r with |r| <= M }`, where
    `M = 2N+1` and `Q = 8(N+1)`.
- Put `B = { 2^n j : n >= 0, j ∈ J_n }` and `A = Z ∖ B`.

## Claim

1. `B = -B` and `0 ∉ B`.
2. `B` is open in the profinite topology of `Z`, so `A` is closed.
3. `A` is recursive. More precisely, `S = B ∩ Z_{>=1}` is decided by a deterministic multi-stack
   machine that reads `1^s` and halts within `c·s` steps, for a constant `c`.
4. `B` is not effectively open, so `A` is not effectively closed. In particular `A` is not
   periodic.

By Proposition 1 of Rauzy (Dyson's groups, TeX lines 200–232), the amalgam
`L(A) = L *_{U_A} L` of two lamplighters along the lamps in `A` is finitely generated and
residually finite, has solvable word problem, and is not effectively residually finite. Rauzy's
§3 argument (lines 365–413) uses only that `A` is closed and not effectively closed, so it applies
here: the depth function of `L(A)` is not bounded by any recursive function.

## Proof

**(1).** `j ↦ -j` preserves each `J_n`, since the residue window `[-M, M]` is symmetric. Also
`0` has no odd part, so `0 ∉ B`.

**(2).** Each `J_n` is a union of classes modulo an even number: modulo `Q` in the halting case,
and modulo `2` otherwise. Call that modulus `Q_n`. If `x = 2^n j` with `j ∈ J_n`, then
`x + 2^n Q_n Z = 2^n (j + Q_n Z) ⊆ 2^n J_n ⊆ B`.

**(3).** Given `1^s`, the machine does the following.
- It halves in unary to get `n = v_2(s)` and the odd part `j = s/2^n`. This takes `O(s)` steps,
  because the halvings shrink geometrically.
- It writes out the transition table of `M_n`. Since `n <= log_2 s`, this takes `O(s)` steps.
- It simulates `M_n` on the empty input for at most `j` steps, with the tape on two stacks. Each
  simulated step costs `O(n)` table lookups, so the simulation costs `O(j·n) = O(s·n/2^n)`, which
  is `O(s)` uniformly in `n`.
- If `M_n` has not halted after `j` steps, the machine accepts. This is correct:
  - if `N_n = ∞`, then `J_n` contains every odd number;
  - if `N_n = N >= j`, then `|j| <= N <= M`, so `j ∈ J_n`.
- If `M_n` halted at step `N < j`, the machine computes `j mod 8(N+1)` in unary in `O(j)` steps
  and compares the residue with the window `[-M, M]`.

The same test decides the negative half, because `B = -B`.

**(4).** Suppose an algorithm `Φ` outputs, for every `x ∈ B`, some `P >= 1` with `x + PZ ⊆ B`.
- The number `2^n` lies in `B` for every `n`: `1 ∈ J_n` in both cases.
- Let `P = Φ(2^n)` and `P' = lcm(P, 2^(n+1))`. Every element of `2^n + P'Z` has 2-adic valuation
  exactly `n`, so `2^n + P'Z ⊆ 2^n J_n`. That is, `1 + pZ ⊆ J_n` with `p = P'/2^n`.
- Suppose `M_n` halts in `N` steps and `p <= 2N`. Some element `1 + kp` with `k >= 1` lies in
  `(M, M + p] ⊆ (2N+1, 4N+1]`. Its residue modulo `Q = 8N+8` lies in `(M, Q - M) = (2N+1, 6N+7)`,
  outside the window, so it is not in `J_n`. This is a contradiction, so `p >= 2N + 1 > N`.
- So `M_n` halts if and only if it halts within `p` steps. Since `p` is computable from `n` via
  `Φ`, the halting problem on the empty input would be decidable, which it is not.

A periodic set is effectively closed: for `x ∉ A`, output the period. So `A` is not periodic. `∎`

## Lesson for general BH

- **What the non-effectivity costs.** It costs nothing in time. The set is closed but not
  effectively closed, yet its membership test runs in linear time in the value of the input.
- **Where the uncomputable part lives.** It sits only in the sizes of the periods, never in the
  cost of reading the set.
- **Consequence for hosts.** Hiding finite quotients at a non-recursive depth, as
  `effective-residual-finiteness-separator-for-boone-higman` requires of a universal host, needs no
  hard word problem in the host: a clocked machine in a fixed finitely presented group can do it
  (`nv-machines-realize-linear-time-lamp-centralizers`).
