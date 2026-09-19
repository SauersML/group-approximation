---
rg: 2
id: strict-pairs-admit-locally-balanced-decoders
kind: claim
title: A group carrying a strict automaton pair carries one whose decoder is locally balanced
distinct_from:
  strict-pairs-admit-post-surjective-decoders: that asks for a post-surjective decoder; this asks for a locally balanced one, which is post-surjective with lifts inside a fixed thickening and in addition balances the lift counts exactly within every context, so this implies that one and is implied by the absorption hub.
  strict-automata-yield-topological-bernoulli-absorptions: that asks for an absorption, which needs a decoder with commuting one-site translation lifts; this asks only for the local counting invariant of such a decoder, the necessary half, with the commutation left to locally-balanced-decoders-admit-translation-lifts.
  strict-automata-yield-strict-quantum-endomorphisms: that asks for some strict quantum automaton, and in decoder-extension form needs a decoder whose pullback extends; every such decoder is locally balanced, so the decoder-extension form of that hole implies this one.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is a measure statement about encoders; this is a pointwise counting statement about decoders, which implies measure preservation of the decoder only.
---

**OPEN.**

**Statement.** Let `G` be a group that carries an injective, non-surjective cellular automaton over some finite
alphabet. Then `G` carries a strict pair `(tau, sigma)`, over some possibly different finite alphabet, whose
decoder `sigma` is locally balanced for some lift set `S`, in the sense of `extension-decoders-are-locally-balanced`.

**Unpacked.** Let `W` be the memory of `sigma`. For every finite `F`, and every configuration outside `FS`, the
output on `F` must be uniformly distributed over the fillings of `FS`, conditionally on the output on the collar
`B_F = (F ∪ FSW^-1) \ F`. Equivalently, the fibres over any two outputs that agree on `B_F` have the same size.

**Place in the graph.**
- **Implied by the absorption hub.** `strict-automata-yield-topological-bernoulli-absorptions` implies this, by
  (A) of `extension-decoders-are-locally-balanced` and (a) of the monomial theorem.
- **Implied by the decoder form of the quantum transfer.** Any decoder of a strict pair whose pullback extends to
  a quantum automaton is balanced, by (B) of the lemma.
- **Implies the post-surjective-decoder hole.** Route `post-surjective-decoders-via-local-balance`, by (D1) of the
  lemma.
- **Half of the hub.** With `locally-balanced-decoders-admit-translation-lifts`, this gives the hub. Route
  `absorptions-via-locally-balanced-decoders`.
- **Chain of implications.** `absorption ⇒ monomial decoder extension ⇒ decoder extension ⇒ this claim ⇒
  post-surjective decoder ⇒ dual failure`.
  - The implication `decoder extension ⇒ this claim` is new here.
  - So this is the weakest decoder-level statement that any absorption or decoder-extension proof must establish
    on the way.
- **Sofic calibration.** On sofic groups a balanced automaton is reversible, so no decoder of a strict pair is
  balanced. This agrees with surjunctivity of sofic groups.

## Attempts

- **2026-09-19, swarm-0917-w16-w16-gs-last1 [local-designs]: rebalancing a given decoder off the image. OPEN.**
  - *Plan.* Start from any decoder `sigma_0` of `tau`. The local rule is free on windows that never occur in
    `Y = tau(A^G)`. Choose it there so that the fibre counts become balanced.
  - *What the known lifting gives.* By `decoders-lift-changes-away-from-infinite-defect-chains`, every decoder
    lifts a finite output change by overwriting the finite defect components that touch it.
    - This proves `Fib_c(v') ≠ ∅` whenever `Fib_c(v) ≠ ∅`, away from infinite defect chains. That is
      post-surjectivity there, but not balance.
    - The overwrite map `Fib_c(v) -> Fib_c(v')` erases the defect content, so it is many-to-one. It gives no bound
      in the reverse direction.
  - *What balance needs instead.* Balance asks for injective lifts inside `FS`, one for each translate of the output
    on `F`. Equivalently, `q^|F|` must divide the number of fillings `p ∈ A^(FS)` that produce any given collar
    output, in every context. So the decoder must re-encode the defect content injectively while its output on `F`
    changes.
    - At a context meeting an infinite defect chain, the only inputs that can change are the `q^|FS|` fillings.
      They must split into `q^|F|` equal classes whose collar output is fixed.
    - This is the same Hilbert-hotel accounting that sank the free-track attempt on
      `strict-pairs-admit-post-surjective-decoders` (w12), now in exact form.
  - *Where it dies.* The rule off the language of `Y` is chosen window by window. Balance is a condition on every
    context at once, including contexts that contain unboundedly many defect windows. No window-by-window choice is
    known to meet the divisibility condition on all of them. The step that fails is the same as for
    post-surjective decoders, at infinite defect chains, but the demand is stronger: exact counts, not just
    nonempty fibres.
  - *Falsifiable consequence.* A non-surjunctive group on which some strict pair has a post-surjective decoder, but
    no strict pair (over any alphabet) has a balanced one, would refute this claim without refuting the
    post-surjective-decoder hole. It would also refute the absorption hub.
