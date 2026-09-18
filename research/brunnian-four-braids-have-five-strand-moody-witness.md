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
- 2026-09-17 (c-burau4, compute-scout; artifacts
  `experiments/moody-witness-equivalence-2026-09-17/spanning.py` and `cyclotomic_jets.py`, with logs).
  **Reframing: this hole is the flagship in disguise.**
  - *Equivalence.* New claim `moody-witness-exists-iff-outside-burau-kernel`, with route
    `-proof` requiring only established nodes. For every `Φ ∈ B_4`, a witness (with `k = 1`) exists
    iff `ρ_4(Φ) ≠ I`.
    - The converse direction uses exact rank certificates. Over `Q(t)`, in every convention
      variant, the `K_5`-orbit of the α-form column and the `B_4`-orbit of the loop-class row
      each span `Q(t)^5` together with the fixed vectors of `f(B_4)`, and so do the two mixed
      orbits.
    - So a braid whose conjugates change no `𝕄_Γ` has `J(f(Φ)) = I`.
    - The new route `five-strand-moody-witness-from-brunnian-burau-avoidance` gives
      target ⟸ `brunnian-four-braids-avoid-burau-kernel`, and the via-moody route gives ⟹.
    - Consequences: the target is equivalent to Brunnian Burau avoidance, hence to 4-strand Burau
      faithfulness. The via-moody decomposition is circular, not a reduction. Allowing powers and
      conjugates (G6) buys nothing, since `k = 1` is equivalent.
  - *Obstruction.* New claim `brunnian-burau-kernel-mod-cyclotomic-products-nontrivial`. For
    every fixed product `F` of `Φ_d` with `d ≠ 3`, to any multiplicity, there is a nontrivial
    Brunnian `X_F` with `𝕄_{f(Φ_0)Γ} ≡ 𝕄_Γ mod F` for all conjugates `Φ_0` of powers of `X_F` and
    all `Γ ∈ B_5`.
    - Construction: iterated commutators with `Δ_3^{2d}`, using
      `ρ_4(Δ_3^{2k}) = I + (t^{3k}−1)P` with `P² = P`. Nontriviality comes from cyclic
      centralizers in the free group `K_4`.
    - Every certificate that detects the witness through the residue of `𝕄` modulo a fixed `F`
      dies on `X_F`: parity (`t = −1`), finite jets at roots of unity, and finite cyclic covers of
      order prime to 3.
    - Survivors: moduli that depend on `Φ`, exact computation, and `Φ_3`.
  - Status stays OPEN (its only live routes need `brunnian-four-braids-avoid-burau-kernel`, or G1).
