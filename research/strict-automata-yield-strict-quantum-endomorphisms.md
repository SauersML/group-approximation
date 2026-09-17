---
rg: 2
id: strict-automata-yield-strict-quantum-endomorphisms
kind: claim
title: A group carrying an injective non-surjective cellular automaton carries a non-surjective quantum automaton
distinct_from:
  injective-ca-pullbacks-extend-to-matrix-observables: that asks the encoder pullback f -> f o tau to extend multiplicatively, which by split-ca-quantization-has-sharp-defect happens only when tau is onto, so it is equivalent to the goal; this asks only that some strict quantum automaton exist on the same group, with no required relation to tau, and in its natural form extends the decoder pullback instead.
  gottschalk-surjunctivity-conjecture: that is classical surjunctivity; this is the contrapositive transfer from classical to quantum strictness, which together with quantum-surjunctivity-conjecture gives the goal.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is about the encoder of a strict pair; this in its decoder-extension form forces the decoder to preserve the uniform product measure, a different measure statement about the surjective, non-injective partner.
---

**OPEN.** Let `G` be a group. Suppose some finite full shift over `G` carries an injective non-surjective cellular
automaton. Then, for some `d >= 2`, some shift-equivariant, finite-propagation, unital *-endomorphism of
`(x)_G M_d` is not onto.

This is the transfer ("diagonal extension") prerequisite of `gottschalk-via-quantum-surjunctivity`.

## Attempts

- **Sectors where it holds (established).**
  - *Sofic groups.* Both sides are vacuous, by `sofic-groups-are-surjunctive` and
    `sofic-groups-are-quantum-surjunctive`.
  - *Groups with a one-sided inverse over some `F_p[G]`.* Both sides hold. The classical side is
    `stable-finiteness-failure-refutes-surjunctivity`, and the quantum side is
    `clifford-quantum-surjunctivity-iff-stable-finiteness`, with `M = diag(A, B^*)`.
  - So the transfer is open only on non-sofic groups all of whose group algebras `F_p[G]` are stably finite. That
    is the territory of `non-surjunctive-group-with-stably-finite-group-algebras`.
- **Encoder form is dead.** One cannot extend `tau^*` for the strict encoder `tau` itself: by
  `split-ca-quantization-has-sharp-defect`, a unital *-homomorphism extending `f -> f o tau` exists only when `tau`
  is onto. The transfer must use the decoder, or build `Phi` from nothing.
- **Decoder-extension form: two necessary conditions (proved here).** Let `sigma` be a decoder with
  `sigma o tau = id`, and suppose a quantum automaton `Phi` on `(x)_G M_d`, with `d = |A|`, restricts to `sigma^*` on
  the diagonal `C(A^G)`.
  1. `Phi` is automatically strict. If `Phi` were onto, it would be an automorphism, so `Phi(C(A^G))` would be a
     maximal abelian subalgebra. But `Phi(C(A^G)) = sigma^* C(A^G)` is strictly contained in the abelian algebra
     `C(A^G)`, because `sigma` is not injective.
  2. `sigma` preserves the uniform product measure `mu`. The unique trace gives `tau o Phi = tau`, and on the
     diagonal this reads `mu(sigma^-1 E) = mu(E)` for every cylinder `E`.
     - By `window-balance-is-a-fiber-upper-bound`, this means every window pattern has the average number of
       preimage patterns.
     - It is strictly stronger than the single-site balance of
       `every-injective-ca-has-uniform-single-site-output-law`. Playbook lane (a) calls extension "exactly" single-site
       balance; that description is too weak.
  - So the decoder form splits into two questions that can each fail: **(D1)** some decoder of a strict pair
    preserves `mu`; **(D2)** a measure-preserving decoder pullback extends from the diagonal to a *-endomorphism
    commuting with the shift.
  - (D1) can fail for some decoders, because the local rule of `sigma` may be changed freely on windows that never
    occur in the image of `tau`. It is open whether some decoder always satisfies it.
- **Linearizable route (not recorded as a route, because it is dominated).** A strict pair over a `p`-power
  alphabet with `F_p[G]` not stably finite transfers through the Clifford sector. So the transfer for `p`-power
  alphabets would follow from the contrapositive of `stable-finiteness-forces-prime-power-surjunctivity`.
  - But that premise plus Kaplansky already gives the goal at those alphabets. The quantum route is worth having
    only if the transfer is proved without the classical Kaplansky reduction.
- **Quantum alphabets ascend by multiples.** `Phi (x) id_(M_m)` is strict on `M_(dm)` whenever `Phi` is strict on
  `M_d`. So the `d` in the statement can be taken to be any multiple of a strict size.
