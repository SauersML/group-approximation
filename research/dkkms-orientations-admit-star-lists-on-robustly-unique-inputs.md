---
rg: 2
id: dkkms-orientations-admit-star-lists-on-robustly-unique-inputs
kind: claim
title: (P2^RU) On robustly unique regular Gap3Lin YES inputs (every near-optimal assignment rho-close to one coset of dimension <= l + 1), every DKKMS orientation of lift value >= 1/2 + gamma has a lift labelling explained by a star list of at most L arbitrary outer labellings -- the selector-free star-list prerequisite restricted to a class where the flip orientation provably has no kernel map to act on
distinct_from:
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is (P2) on the exact-kernel classes P_r, refuted by the J'-instances; this restricts (P2) to RU-YES, which excludes J'-instances and every input carrying a generic approximate kernel of rank above r0.
  exact-kernel-rank-does-not-exclude-flip-violators: that states (P2^rob) on P^delta_r; this is (P2) on the subclass RU-YES of P^delta_r and is implied by (P2^rob).
  robust-uniqueness-bounds-robust-kernel-rank: that shows Theorem O and Theorem O' have no input on RU-YES; this is the star-list statement that must then hold there.
  star-list-structure-is-circular-on-decodable-yes-inputs: that refutes star lists on classes containing J-instances through the flip orientation; this asks for star lists on inputs where no flip exists.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is H1; this is one of the two prerequisites of the robust-uniqueness route to its constant-bias kill.
---

**OPEN.**

## Statement

Use the parameters and the notation of
`good-dkkms-orientations-admit-short-star-lists-on-hard-inputs` ((P2), the
Corollary DK^C budget for `L`) and the class RU-YES of
`gap3lin-hard-with-robustly-unique-yes-solutions`.

**Claim (P2^RU).** For all but finitely many `x` in RU-YES, every orientation
`o` of `G(x)` with `val(U_o) >= 1/2 + gamma` has a lift labelling `W` with
`val(U_o, W) >= 1/2 + gamma` and a list `Lambda` of at most `L` arbitrary
outer labellings with `D^C_L(proj W, Lambda) <= gamma - gamma'`.

That is, `F_inf(SL^C, RU-YES)` in the notation of
`selector-witness-hypotheses-collapse-to-selector-free-form`.

## Why it is open

* **Not refuted by the known mechanism.** Every known violator comes from the
  flip orientation `o*` of Theorems O and O'. It needs a kernel map (exact or
  `delta`-approximate) of rank `n = l + s >= l + 2` with `beta_bad` below the
  genericity threshold. By Lemma RU of
  `robust-uniqueness-bounds-robust-kernel-rank`, every `delta`-approximate
  kernel map of rank `> r0` on RU-YES has `beta_bad >= 1 - 12 k rho > beta0`.
  With `r0 <= l + 1`, no such map exists.
* **Implied by (P2^rob)**, since RU-YES ⊆ `P^delta_(r0)`.
* **Candidate attack.** Use the near-uniqueness of the outer solution. On
  RU-YES, every good lift labelling's projection should decode (by DKKMS
  soundness and Corollary DK^C) to outer labellings near `x* + C`. There are at
  most `2^(r0)` such cosets, so a list of size `2^(r0) <= 2^(l+1)` is available
  as a reference list. What is missing is the step from "the decoded labelling
  is near `x* + C`" to the star-wise charge `D^C_L <= gamma - gamma'`. This is
  the same 51 percent list-decoding gap as in the (SF_P) node, but now with a
  canonical candidate list.

## Falsifiers

* A violator on robustly unique inputs, meaning an orientation of lift value
  `>= 1/2 + gamma` not explained by any short star list. It would have to use
  a mechanism other than a linear family of branches, for example non-linear
  branch choices tied to the at most `2^(r0)` near-solution cosets.
* A proof that robust uniqueness at scale `1/k` is incompatible with the
  DKKMS soundness regime. That would make RU-YES empty for the relevant
  parameters and the statement vacuous, while (P1^RU) would be false.

## Attempts

* **2026-09-20, swarm-0917-w20-w20-ugc-pull (finite-models / transplanter).**
  Stated as the corrected (P2) prerequisite on the robust-uniqueness class.
  Checked that the flip mechanism is excluded (Lemma RU). No proof attempted.
