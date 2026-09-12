---
rg: 2
id: exterior-tensor-powers-are-asymptotically-free
kind: claim
title: Exterior tensor powers of a faithful module over a finite linear group are free up to a geometrically vanishing proportion
distinct_from:
  level-unit-hnn-extensions-have-anti-central-rank-models: that uses the twisted regular module, which is exactly free on finite subgroups; this proves that the Fock modules Λ(W)^(⊗m) become free in proportion, which the Fock-locality idea needed.
artifacts:
  - research/artifacts/fock-local-rank-models-2026-09-12.md
---

**ESTABLISHED** (proof: Section 1 of the linked artifact, route
`exterior-tensor-powers-asymptotically-free-proof`).

**Statement.** Let `Γ ≤ GL(W)` be a finite group, `W` of dimension `w` over a finite field `F_q` of any
characteristic.
1. **Free seed.** `F_qΓ` is a direct summand of `Λ(W)^(⊗r)` for some `r <= w^3(q−1)`.
2. **Asymptotic freeness.** With `η = |Γ| 2^(−wr)`, for every `m`,
   `Λ(W)^(⊗m) ≅ F_qΓ^c ⊕ N` with `dim N <= (1−η)^⌊m/r⌋ · dim Λ(W)^(⊗m)`.
3. **Rank-close actions.** Two actions of `Γ` on one space of dimension `D` whose non-free parts have
   dimension `<= δD` are conjugate up to normalized rank error `δ`.

**Consequence.** The Fock tower `a -> Λ(a)` on `Λ(U_j)`, with `U_j = F_q^(2^j)`, is an injective rank
model of the level unit group `L = ∪ GL_(2^j)(F_q)`. It is asymptotically free on every finite subgroup,
so it carries the Haar law on the signed diagonal up to vanishing error. This settles the gap recorded
in Section 3 of `research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md` in every
characteristic.

**Proof idea.**
- **Free seed.** A basis tuple has a free orbit. Polynomial functions of bounded degree map onto
  functions on that orbit, which is `F_qΓ`. `F_qΓ` is projective, so it splits off a tensor power.
- **Expansion.** Expanding `(F_qΓ ⊕ R)^(⊗s)`, every term with an `F_qΓ` factor is free.
- No Brauer characters and no Sylow reduction are used.
