---
rg: 2
id: window-zero-twists-are-fixed-point-free
kind: claim
title: The twist of a genuine window-zero shell action has no nontrivial fixed point, and its periodic points act eventually periodically, so twists with a fixed or periodic generator force virtual abelianness
distinct_from:
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that proves in item 5 that a finite-order automorphism twist makes the input virtually abelian; this proves the pointwise statement behind it, for every endomorphism twist and both signs, so that a single fixed element is already excluded.
  cyclic-input-window-zero-needs-an-automorphism-twist: that excludes the twists a ↦ a^k of Z by counting along the shift ray; this is a general necessary condition on any twist, obtained from the centralizer of the shift in NearSym(N).
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that constrains FW inputs; this holds for every input and is used as a design test for constructions.
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**ESTABLISHED** by `window-zero-twists-are-fixed-point-free-proof` (lane proof, elementary, not independently reviewed, no priority claimed).

## Setting

`P` is a group and `rho: P -> Sym(N)` a genuine action in which every `g != 1` moves infinitely many points. `s: n ↦ n+1`. For `eps` in `{1, −1}`, window zero with twist `psi ∈ End(P)` means

    s^-eps rho_g s^eps = rho_(psi(g))   in NearSym(N), for every g.

This is the gate of `shell-ascending-gate-is-a-finite-window-inclusion` with `N = 0`, in the genuine-action form of `genuine-action-shell-envelopes-generalize-the-regular-shell`.

## Statement

1. **Centralizer of the shift.** In `NearSym(N)` the centralizer of `s^k`, for `k >= 1`, is the group of eventually `k`-periodic near permutations, those with `f(n+k) = f(n) + k` for large `n`. The centralizer of `s` is `<s>`.
2. **No fixed points.** If `psi(g) = g`, then `g = 1`.
3. **Periodic points.** If `psi^k(g) = g` for some `k >= 1`, then `rho_g` is eventually `k`-periodic. The `psi`-periodic elements with period dividing `k` form a subgroup `Fix(psi^k)`, which is virtually abelian.
4. **Consequences.**
   - If `psi` has finite order, all of `P` is `psi`-periodic, hence virtually abelian. This recovers item 5 of `eventually-periodic-genuine-shell-actions-give-fp-envelopes`.
   - Suppose a window-zero witness is sought for an input `P = <S>` whose twist fixes one generator, or permutes the generators up to finite order. Then that generator acts trivially, respectively eventually periodically.
   - An example is the Baumslag-type twist of the lamplighter: `a ↦ a·t a t^-1` and `t ↦ t`, which is injective with image of index 2. It is excluded, because `t` is fixed.

## Scope

- This is a necessary condition on twists. No window-zero witness is constructed here.
- The endomorphism is not assumed injective or surjective. The only input is the relation above and infinite supports.

## Lesson for general BH

The shell route's germ gate at window zero asks the input to be self-similar at infinity: shifting the ray by one step must conjugate the input into itself.
- The centralizer of the shift in `NearSym(N)` is only `<s>`. So every twist must move every nontrivial element.
- An element fixed at infinity, or periodic under the twist, is invisible to the shell: it is finitary, or eventually periodic.
- A universal shell proof therefore cannot rely on any part of the input being inert under the self-similarity. With the FW results, this points the general route toward windows `N >= 1`, where several shifted copies of the input interact.
