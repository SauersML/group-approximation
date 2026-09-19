---
rg: 2
id: locally-balanced-decoders-admit-translation-lifts
kind: claim
title: A group carrying a non-injective locally balanced cellular automaton carries a topological Bernoulli absorption
distinct_from:
  strict-automata-yield-topological-bernoulli-absorptions: that starts from an arbitrary strict automaton; this starts from a non-injective automaton that already has the exact local counting invariant of an absorption decoder, so only the gluing of one-site lifts into commuting translates remains.
  free-compatible-wreath-actions-are-bernoulli-absorptions: that proves free compatible wreath actions are absorptions; this asks whether local balance of one automaton is enough to build such an action.
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that proves an automaton with a translation lift gives an absorption; this asks whether local balance, which every such automaton has, is also sufficient up to a change of automaton.
---

**OPEN.**

**Statement.** Let `G` be a group that carries a cellular automaton `sigma` on `A^G`, with `A` finite, that is not
injective and is locally balanced in the sense of `extension-decoders-are-locally-balanced`. Then `G` carries a
topological Bernoulli absorption at some alphabet size.

**Converse (proved).** The first coordinate of an absorption is non-injective and locally balanced, by (A) of the
lemma. So this claim says that local balance is the complete local invariant of absorption decoders, up to
changing the automaton and the alphabet.

**Place in the graph.** With `strict-pairs-admit-locally-balanced-decoders`, this claim gives
`strict-automata-yield-topological-bernoulli-absorptions`. See route `absorptions-via-locally-balanced-decoders`.

**What is already free.** By (E) of the lemma, the automaton `sigma` over `A = Z/d` has a one-site lift `T_e`.
- `T_e` is a local bijection supported in `S`, with `T_e^d = id` and `sigma o T_e = sigma + delta_e`.
- It satisfies every condition of a translation lift except `T_e T_g = T_g T_e`, and that only needs checking for
  `g` in the finite set `K = DW S^-1 ∪ S(DW)^-1`.
- So the claim holds for `sigma` itself as soon as the fibre enumerations `pi_c` of Step 5 of the lemma can be
  chosen so that these finitely many commutations hold, possibly after enlarging `S`.
- For fixed `sigma` and a fixed lift radius, this is a finite constraint problem on the labelled ball of `G`.

**Sofic calibration.** On sofic groups a balanced automaton is reversible, so the claim is vacuous there. In the
reversible case, `T_e(u) = sigma^-1(sigma(u) + delta_e)` is a commuting lift. The trouble is non-injectivity.

## Attempts

- **2026-09-19, swarm-0917-w16-w16-gs-last1 [local-designs]: gluing one-site lifts. OPEN.**
  - *Attempt 1: canonical enumerations.*
    - Order each fibre `Fib_c(v)` lexicographically, and let `pi_c` send the `i`-th element of the fibre over
      `v + j delta_e` to the `i`-th element over `v + (j+1) delta_e`.
    - For `g ∈ K`, `T_g` rewrites coordinates in `gS`, and these lie in the context window `DW \ S` that `T_e`
      reads. So `T_g` changes the context `c`, and with it the fibre decomposition that `pi_c` enumerates.
    - Commutation `T_e T_g = T_g T_e` asks that the two lexicographic matchings be carried into each other by the
      other lift. Nothing forces this.
    - *Where it dies.* The enumerations must form a cocycle over the moves of the neighbouring lifts, and that is
      circular: the lifts are defined by the enumerations.
  - *Attempt 2: compactness over finite `F`.*
    - Balance at `F` gives, on each slice `A^(FS) x {c}`, a free action of `(Z/d)^F` that moves the output
      fibres correctly.
    - But its generators change all of `FS`, not just `fS`. So the actions for `F ⊆ F'` are not restrictions of
      one another, and a König-type limit has nothing coherent to pass to.
    - *Where it dies.* In a continuous, shift-compatible action of the compact group `(Z/d)^G`, the generator at
      `f` automatically changes only a bounded set of coordinates near `f`. This follows from joint continuity,
      compactness and `(k * u)_h = ((h^-1 . k) * lambda_(h^-1) u)_e`. So locality is not an extra demand, it is
      forced by shift compatibility, and shift compatibility is what the finite-`F` actions lack.
  - *Net.* Balance supplies every counting condition of an absorption, and (E) supplies one-site lifts. The claim is
    exactly the commutation of those lifts with their finitely many interacting translates.
  - *Falsifiable test.* A group that carries a non-injective balanced automaton but no absorption refutes this
    claim. If that group is also non-surjunctive, it refutes the absorption hub as well.
    - A single `sigma` whose one-site lifts cannot commute at any radius is only evidence, because the claim
      allows the automaton and the alphabet to change.
    - Any such group is non-sofic and not dual surjunctive.
- **2026-09-19, swarm-0917-w17-w17-gs-last1 [reframing]: colour-scheduled lifts. OPEN.** Proved in
  [[locally-balanced-decoders-are-colour-fibred-absorption-decoders]].
  - *Scheduling.* One-site lifts at `E`-independent sites need not commute with anything; they write disjoint sets
    and read none of each other's writes. So applying them colour class by colour class, over a proper colouring
    `kappa` of `G ~ Gk`, `k ∈ E \ {1}`, gives local bijections `R^d_kappa : sigma^-1(t) -> sigma^-1(t + d)`.
  - *Theorem I.* `sigma` is balanced iff it is the base-independent decoder of a homeomorphism
    `C_E x A^G ≅ C_E x A^G x sigma^-1(c_0)` over the proper-colouring shift. So this claim is exactly the
    de-colouring of that fibred absorption, the analogue of Proposition C and bus need 36774ad3.
  - *Theorem L.* For fixed `sigma`, a genuine absorption exists iff there is an equivariant family of
    bijections `sigma^-1(c_0) -> sigma^-1(y_U)`, where `y_U` equals `c_0` off the sites at which `y` is locally
    `E`-symmetric. This answers Attempt 1: the cocycle it needed exists wherever a colouring can be read from the
    target, so obstructions live only over `y_U`.
  - *Class kill (Proposition F).* A genuine absorption decoder has `H`-conjugate fibres over `H`-fixed targets, so
    its constant fibres are conjugate and each holds exactly one constant. Every approach that keeps `sigma`
    (larger `S`, larger radius, the finite constraint problem above) dies at the constant targets for a balanced
    `sigma` violating this.
  - *Remaining open content.* Either de-colour over `Sym_E` for some `sigma`, or change the automaton so that
    condition (ii) of Theorem L can be met.
  - *Falsifiable test.* A balanced non-injective `sigma` with two non-conjugate constant fibres shows that the
    automaton must change. A group all of whose balanced automata have that defect would be strong evidence
    against this claim.
