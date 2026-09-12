---
rg: 2
id: anti-central-triangular-certificates-flatten-to-minors
kind: claim
title: Over the ternary anti-central summand, every triangular identity certificate flattens to a minor certificate
distinct_from:
  ternary-anti-central-states-force-nontrivial-rank-models: that asks that a state force a matricial rank model of the unit group; this is step (U1) alone, from a state to an abstract Sylvester rank function, in certificate form.
  rank-condition-rings-carry-sylvester-rank-functions: that is the same upgrade for every unital ring; this is only the ternary anti-central summand, where group structure may be used.
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x` and `S_- = eps_- F_3[G]`. If `I_(q+1) <=_T I_q` over `S_-` for some `q`,
through minors and triangular moves as in `sylvester-rank-functions-iff-no-triangular-certificate`,
then `I_(q'+1) <~ I_(q')` over `S_-` for some `q'`, through minors alone.

**Equivalent forms.**
- If `S_-` has the rank condition, it carries a Sylvester matrix rank function with `rk(eps_-) = 1`.
- If every Sylvester rank function on `F_3[G]` kills `eps_-`, the ternary swap corner is full, by
  `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`.

**Why it matters.** The abstract "No" branch of the characteristic-three rank gate (every rank function
on `F_3[G]` kills `eps_-`) is a finite triangular certificate over `S_-`. The corner equation, and with it
a Gottschalk counterexample, is a finite minor certificate. So this claim, together with abstract "No",
refutes Gottschalk. w3-gate-char3 Section 7 (PASS) says the abstract form of "No" is what the plan needs.
Both certificates live over `eps_- F_3[H]` for a finitely generated `H` containing `z`.

## Attempts

- 2026-09-12 `w4-upg-kill` (artifact Section 5).
  - **What flattens without group input:** split chains and idempotent triangular steps.
  - **What doesn't:** non-idempotent triangular moves at carried minors that mix the blocks.
  - **Not examined:** whether the halving homomorphism `M_2(S_-) -> S_-`, which shrinks minor
    certificates to size one (census Theorem E), also controls triangular ones.
  - **Relation to the "Yes" side:** a unital map from `S_-` to a regular ring with the rank condition would
    give a rank function, which is the "Yes" side of the gate and kills the corner. So the regular-ring
    calibration cannot prove this claim unless the corner is not full.
