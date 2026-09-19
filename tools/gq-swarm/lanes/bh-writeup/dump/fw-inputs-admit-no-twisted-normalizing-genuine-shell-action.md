---
rg: 2
id: fw-inputs-admit-no-twisted-normalizing-genuine-shell-action
kind: claim
title: An infinite group with property FW has no faithful action on N that a power of the shift normalizes up to an automorphism, so FW inputs never pass the window-zero shell gate with an automorphism twist
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes window zero for regular enumerations of one-ended inputs; this excludes it for every genuine action with infinite supports, when the input has property FW and the twist is an automorphism.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that shows genuine actions can pass window zero for the one-ended Z^2 via a rotation twist, and leaves twists of infinite order open; this closes the automorphism case for FW inputs, whatever the order of the twist.
  normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups: that forbids Kazhdan germs normalizing the V-dilation; this forbids the V-dilation normalizing the Kazhdan germs up to an automorphism.
---

**ESTABLISHED** by `fw-twisted-normalizing-shell-action-proof` (lane proof, elementary; not
independently reviewed; no novelty claimed).

**Statement.** Let `P` be an infinite group with property FW (every commensurated subset
of every `P`-set is transfixed). For instance `P` has property (T). Let
`ρ : P -> Sym(N)` be an action in which every `g ≠ 1` moves infinitely many points, let
`s(n) = n + 1`, let `m ≠ 0`, and let `φ` be an automorphism of `P`. Then it is **not**
true that, for every `g in P`,

    s^-m ρ_g s^m = ρ_(φ(g))   near infinity (at all but finitely many n).

**Shell reading.** In the genuine-action shell envelope `E_ρ` of
`genuine-action-shell-envelopes-generalize-the-regular-shell`, this is the ascending gate
of `shell-germ-fp-is-an-ascending-hnn-gate` with window `N = 0` and base `ρ(P)`, twisted by
an automorphism. So for FW inputs that window is closed in both directions. This covers
every infinite simple Kazhdan input, and hence every input that matters for
`boone-higman-conjecture` by `boone-higman-iff-simple-kazhdan-decidable-inputs`. Main's
`Z^2` example passes it only because `Z^2` is not FW. A genuine-action shell for an FW
input needs a window `N >= 1` or a twist by a non-surjective endomorphism.

**Scope.** Twists by non-surjective injective endomorphisms are not covered: the orbit
partitions of `ρ` and `ρ∘φ` then differ. Near actions that are not genuine actions are not
covered either.
