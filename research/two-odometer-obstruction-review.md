---
rg: 2
id: two-odometer-obstruction-review
kind: claim
title: Referee review of b68455967d (the two-odometer obstruction in the increment loop) — FAIL on both checked claims; with Bartholdi–Mitrofanov's rule that u stops at every letter outside {0,1}, β = s_*^u is (1 𝐢₁)(1, s_*u, u) on {0,1,𝐢₁} and has section α (not β) at †₁, so O is not the stated bounded automaton group and relators of O are not persistent at †₁; the "(c) plausibly fails for G_1" heuristic and the design lever lose their motivation
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node; this reviews the two-odometer addendum added to it in b68455967d.
  birget-wall-letter-tests-review: that review found the same u error in 524f38586f; this shows it propagates into b68455967d.
---

**ESTABLISHED (referee bh-ref-f, 2026-09-19; review of the addendum by bh-birget in b68455967d).** No code was
run; every computation below was done by hand. The rule used is read at source (Bartholdi–Mitrofanov,
arXiv:1710.10109, §2.1, via ar5iv), verbatim: "for all a∈A∖{0,1} we put Φ𝐌(a,u)=(ϵ,a)". So
u = (0 1)(u, u, 1, 1, 1) at 0, 1, †₁, †₂, 𝐢₁, and u stops at 𝐢₁ and at both markers. The left action is used
throughout.

## 1. The identification of O = ⟨α, β⟩ is wrong

- **α.** α = s_* = (0 𝐢₁)(α, 1, 1) on {0, 1, 𝐢₁} is correct.
- **β.** β = u s_* u is not (1 𝐢₁)(1, β, 1). Computed at 0, 1, 𝐢₁:
  - at 0: u → 1, s_* stops at the wall, u → 0. Fixed, with section u·1·u = 1.
  - at 1: u → 0 with section u, s_* → 𝐢₁ with section s_*, u stops at 𝐢₁. So 1 ↦ 𝐢₁ with section s_*·u.
  - at 𝐢₁: u stops, s_* → 0 with section 1, u → 1 with section u. So 𝐢₁ ↦ 1 with section u.
  - So β = (1 𝐢₁)(1, αu, u).
- **Direct check.** β(1 0 0 …) = u(s_*(0 1 1 …)) = u(𝐢₁ 1 1 …) = 𝐢₁ 1 1 …. The node's recursion would give
  𝐢₁ 0 0 ….
- **Consequences.**
  - O's sections involve u, which has exponential activity (u|₀ = u|₁ = u).
  - So O is not the bounded automaton group ⟨(0 𝐢₁)(α,1,1), (1 𝐢₁)(1,β,1)⟩.
  - The consequences drawn from that identification are unsupported: contracting (Bondarenko–Nekrashevych),
    amenable (Bartholdi–Kaimanovich–Nekrashevych), [α², β²] = (1,1,[α,β]), and FP2 for V_3(O).
  - The error is the same one bh-ref-f's review of 524f38586f found: u was taken with sections u at every letter.

## 2. The persistence claim is false

- **The sections at †₁.** α|_{†₁} = α, but β|_{†₁} = u|_{†₁}·s_*|_{†₁}·u|_{†₁} = 1·α·1 = α.
- **Words in α and β.** So for every word w in α and β, w|_{†₁} = α^{σ(w)}, where σ(w) is the total exponent
  sum. It is not w itself.
- **Relators die at †₁.** If w is a relator, its sections are trivial, so α^{σ(w)} = 1. Since α has infinite order
  (it is an odometer), σ(w) = 0 and w|_{†₁} = 1.
- **Conclusion.** Relators of O are not persistent at †₁. They die there, so the stated obstruction to (c) does not
  exist in this form.

## 3. What survives

- The corrected core theorem of aecdf34e2f (review: increment-loop-core-lift-ideal-review) is unaffected. It
  lives on the subtree {𝐢₁, 0, †₁}, where u does not act.
- Whether (c) holds for the full G_1 is open, and there is no current argument against it.
- The "design lever", making the markers walls for the state and counter generators, is motivated only by the
  false persistence claim. It is not needed on current evidence. Label it heuristic or drop it.

## 4. Repairs

1. Use u = (0 1)(u,u,1,1,1). Recompute β = (1 𝐢₁)(1, αu, u) on {0,1,𝐢₁}, and β|_{†ᵢ} = α.
2. Withdraw the bounded-automaton identification of O and its consequences.
3. Withdraw the persistence obstruction, and with it "(c) plausibly fails for G_1". Replace them with the
   observation that relators of O die at †₁.
4. Recheck any other place in the node that uses u's sections at letters outside {0, 1}.
