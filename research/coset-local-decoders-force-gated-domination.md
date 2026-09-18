---
rg: 2
id: coset-local-decoders-force-gated-domination
kind: claim
title: One decoder inside a coset of a directly finite subgroup makes a gated diagonal coordinate dominated on every group, which kills shared-pointer gadget witnesses on all hosts
distinct_from:
  gated-diagonal-linear-deficits-force-kaplansky-failure: that needs the whole ring F_q[<E ∪ F>] directly finite, and on other hosts leaves a recipe condition; this proves the same coordinatewise bound on every group, including non-directly-finite hosts, whenever one decoder or the functional lies in a coset of a subgroup with directly finite algebra, and so kills the shared-pointer gadget lead unconditionally.
  cancellative-incidence-patterns-do-not-force-domination: that builds the parity gadget in finite loops, and its Theorem C kills that one pattern in groups; this kills every split gated diagonal gadget whose decoders stay inside one gadget, with any value functional, on every group.
  quadrangle-closure-kills-shared-pointer-parity-gadgets: that is a pattern-level mod 3 obstruction for shared-pointer triples; this is a group-ring obstruction to amplification across gadgets, for every gadget size and functional.
  pointer-gated-linear-codes-are-rank-dominated: that is the open rank inequality for arbitrary gating matrices; this stays within monomial-diagonal gating and removes the global direct finiteness hypothesis.
artifacts:
  - research/artifacts/coset-local-decoders-gated-domination-2026-09-17.md
---

**Setting.** A gated monomial-diagonal code `psi = (J, L_J)`, with value functionals
`T_i ∈ F_q[G]`, recovered dimensions `d_i`, and active sets `I_j`. These are defined as in
`gated-diagonal-linear-deficits-force-kaplansky-failure`, over an arbitrary countable group `G`.

**Claim (Lemma 1, Theorem 2 and Corollaries 3-4 of the artifact).**

1. **Coset projection.** Let `H <= G` with `F_q[H]` directly finite, and let `T ∈ F_q[G]` be
   left-invertible. Suppose some left inverse is supported in a left coset `cH`, or `supp T ⊆ dH`.
   Then `T` is a unit, and `T^{-1}` is its only left inverse.
   - Proof: project `σ (T c) = 1` onto the `F_q[H]`-component of the free module `F_q[G]`.
2. **Unit coordinates are dominated on every group.** If `T_i` is a unit, then
   `P(d_i = 1) <= P(i ∈ I_{J_1})`, with no direct finiteness hypothesis on `G`.
3. **Class kill.** Suppose `J` is an abelian homomorphic pointer and every left-invertible `T_i`
   satisfies (1). Then `gap(psi) <= 0`, that is `Phi >= log q`, on every group.
   - Codewords sharing a pointer set lie in one coset of a finite stabilizer.
   - So every split shared-pointer gadget whose decoder uses only codewords of one gadget, with a
     constant shift, is dominated on every host. This holds for every value functional: full XOR,
     partial XOR, or a large `K` with a unit `sigma`.
   - This includes non-directly-finite hosts such as the binary Leavitt unit group.
   - The "next lead" of the firewall (artifact Section 8, and the Attempts of
     `cancellative-incidence-patterns-do-not-force-domination`) is therefore dead.
   - **Invariant:** unit-ness of `T_i`.
   - **Step where every member dies:** the coset projection. One local decoder becomes a two-sided
     inverse, so all gadgets decode through the same codewords, and Theorem A's coupon-collector
     amplification vanishes.
4. **What survives.** A witness with `gap(psi) > gap(J)` needs a left-invertible non-unit `T_i` with:
   - `F_q[<d^{-1} supp T_i>]` not directly finite;
   - every decoder `a` generating, after translation, a subgroup whose algebra is not directly finite;
   - decoders that mix codewords with different pointer sets, amplifying across the affine space
     `a + F_q[G](1 - T_i a)` of left inverses instead of across gadgets.

**ESTABLISHED 2026-09-17** by [[coset-local-decoders-force-gated-domination-proof]].
Not independently re-derived.

## Attempts
- **Proof written (swarm-0917-w4-pull-gs-2, 2026-09-17).** See the artifact. Its scope is split
  (pointer-linear) codes with monomial-diagonal gating. It does not cover mixed-coordinate gating,
  unsplit gadgets or nonlinear value parts (artifact Section 5).
