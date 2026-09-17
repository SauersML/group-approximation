---
rg: 2
id: quadrangle-closure-kills-shared-pointer-parity-gadgets
kind: claim
title: In a cancellative incidence pattern with quadrangle closure, three codewords with a coherent cyclic shift have window symmetric difference of size divisible by three
distinct_from:
  cancellative-incidence-patterns-do-not-force-domination: that builds the shared-pointer parity gadget in finite loops and kills it in groups by a group-ring identity; this kills it at the finite quadrangle closure of the pattern itself, with the invariant |Delta| mod 3.
  rokhlin-window-transport-is-dominated: that is domination over group patterns, equivalent to Rokhlin maximality; this names the one axiom beyond cancellation that the known loop firewall violates, and which Bernoulli witnesses must satisfy.
artifacts:
  - research/artifacts/cancellative-firewall-reverification-2026-09-17.md
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.py
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.json
---

**Setting.** A pattern is a full rectangle `w : F x E -> sites`, written `(f, e) -> f e`, with:
- **(L)** rows injective;
- **(R)** columns injective;
- **(Q) quadrangle closure:** if `c e = c' e'`, `c r = c' r'` and `d e = d' e'`, then `d r = d' r'`.

Every pattern realized in a group satisfies all three. For (Q): `c'^-1 c = e' e^-1 = r' r^-1 = d'^-1 d`.

**Theorem.** Let a pattern satisfy (L), (R) and (Q). Let `W_1, W_2, W_3` be distinct codewords with a coherent cyclic
shift, meaning positions `u, u'` with

    W_1 u = W_2 u',  W_2 u = W_3 u',  W_3 u = W_1 u'.

Then `|W_1 E Δ W_2 E Δ W_3 E| ≡ 0 (mod 3)`.

**Corollary.** Let a pattern satisfy (L), (R) and (Q). Suppose three distinct codewords read one common set of three
sites at a set `P` of three positions. Then `|W_1 E_val Δ W_2 E_val Δ W_3 E_val| ≡ 0 (mod 3)` for `E_val = E ∖ P`, so
it is never a single site.

**Consequences.**
- **(Q) is the step where the gadget dies.** The shared-pointer parity gadget of
  `cancellative-incidence-patterns-do-not-force-domination` (Theorem A) needs `Δ_val = {o}`. So it fails (Q) inside
  its own finite pattern. Its Theorem C, that no group realizes it, follows without the group ring.
- **Proof side.** A proof of `rokhlin-window-transport-is-dominated` must use (Q). Cancellation, identity, both
  divisions, finiteness and a closed finite index set all hold in the loop firewall, where `Phi -> 0`.
- **Counterexample side.** Every attempt to build a Bernoulli Rokhlin deficit from shared-pointer triple parity
  gadgets dies at (Q), with invariant `|Δ_val| mod 3`. This happens before any question of embeddability or
  soficity.
- **Sharpness.** Exhaustive enumeration of 3-row cancellative patterns with `|E| <= 4` shows that coherent shifts
  without (Q) reach `|Δ| = 2` and `|Δ| = 4`. With (Q), only `0` occurs at `|E| = 2`, only `3` at `|E| = 3`, and only `0` and `6` at `|E| = 4`.

**What survives.** A coherent shift of order `r >= 5` whose XOR subset sums to a unit of `F_2[Z/r]`, as for `Z/5` with
`{1, s, s^2}`. It is open whether (L), (R) and (Q) force domination. A proof that they do would give INF for every
group.

**ESTABLISHED** by [[quadrangle-closure-kills-shared-pointer-parity-gadgets-proof]].
