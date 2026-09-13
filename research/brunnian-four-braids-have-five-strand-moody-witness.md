---
rg: 2
id: brunnian-four-braids-have-five-strand-moody-witness
kind: claim
title: "Every nontrivial Brunnian 4-braid has, up to conjugacy and powers, a five-strand push map changing its Moody polynomial"
distinct_from:
  moody-polynomial-change-certifies-burau-nonkernel: that claim is the general criterion turning a change of Moody polynomial into non-membership in the Burau kernel; this claim is the existence of such a change for Brunnian 4-braids
---

For every `1 ≠ Φ ∈ Brun_4` there are `k ≥ 1`, a conjugate `Φ_0` of `Φ^k` in `B_4`, and a push map
`Γ ∈ K_5 = π_1(D_4, p_5) ⊂ B_5` with `𝕄_{f(Φ_0)·Γ} ≠ 𝕄_Γ`. Here `f : B_4 → B_5` is the inclusion
adding `p_5`, and `𝕄` is as in `moody-polynomial-change-certifies-burau-nonkernel` with `n = 5`.

This combines Lemma 6.3, Proposition 6.4 and Corollary 6.5 of arXiv:2607.05283v1
(Bharathram–Birman–Brendle), stated for `k = 1`. Allowing powers weakens the statement. Both routes
into this claim (`brunnian-four-braids-avoid-burau-kernel-via-moody` uses it, and
`five-strand-moody-witness-via-parity-correction` proves it) still work.

## Attempts

- 2026-09-13 (lane z3-05-burau-theory): the preprint's mechanism is:
  - conjugate `Φ` into a proper product with `ι(α, (β_*^3)Φ) > 0`;
  - build `Γ` so that `f(Φ)·Γ` and `Γ` both satisfy the parity condition and their intersection
    numbers with `α` differ;
  - no cancellation (Lemma 4.2) then turns "the counts differ" into "the Moody polynomials
    differ". The logic is checked in artifact §2.7.
- 2026-09-13 (check owner z3-05-burau-search, artifacts `zp-burau-n4-verification-2026-09-13-part1.md`
  and `-part2.md`, landed 5c5c59481a): **GAP** in the core.
  - **G1 (decisive).** The last step of Proposition 6.4, in both cases, replaces `γ_2` by
    `γ' ∪ γ'' ∪ γ_2`, with `γ''` "any nontrivial loop". It then asserts, without proof, that
    `ι(α, (β_*^3)Γ')` strictly increases and that `Γ'` still satisfies parity. The new `γ_2'`
    meets `α` at `r`, and a loop around `p_1` alone creates a `{p_1}`-disk. For a kernel element,
    parity plus unequal counts is exactly the contradiction, so this step carries the whole
    theorem.
  - **G2.** Parity of `Γ` in the first stage rests on two unproved claims: "without loss of
    generality each α–γ_1 disk is one of the five", and "pushed disks are also among the five".
    The staged pushes along non-closed paths are not mapping classes.
  - **G3.** The routing of `γ_2` is asserted, not argued.
  - **G4.** "`f(Φ)·Γ` is a proper product" is never checked, and Proposition 5.1 is stated for
    `K_n` while `f(Φ) ∉ K_5`.
  - **G5.** Theorem 6.6's step from free reduction in the basis `y_1, y_2, y_3` to Condition 2 is
    not proved.
  - **G6.** "Pseudo-Anosov ⇒ `ι(α, (β_*^3)Φ) > 0`" has no proof. REPAIRED up to powers by
    `brunnian-four-braid-powers-cross-the-base-arc` (established), which is why this claim allows
    `Φ^k`.
  - Lemmas 6.2–6.3 are supported by figures only.
- Correction to my §2.7 reading, per the check owner: minimal position is not needed. The winding
  identity only needs the arc piece and the α piece between consecutive crossings to form a
  simple closed curve. So parity for any transverse representative gives
  `Σ |coefficients of 𝕄| = #crossings of that representative`, and representatives with unequal
  crossing counts give different `𝕄`. This bypasses G4's use of Proposition 5.1, but not the
  parity verification in G1–G2.
- The owner's open claim `brunnian-four-braids-admit-parity-correcting-push` packages what remains
  (parity for both arcs plus unequal counts).
- Status: OPEN. No citation route may be written while G1 stands.
