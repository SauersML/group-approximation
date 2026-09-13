---
rg: 2
id: simple-nonsofic-width-over-bounded-composition-factor-groups
kind: claim
title: A finitely presented simple nonsofic group has bounded relator width over all finite groups whose composition factors have bounded order
distinct_from:
  simple-nonsofic-relator-width-over-iterated-wreath-products: that bounds the width over full towers of bounded degree, with every base conjugator available; this asks for every subgroup of such a tower, with only the subgroup's own conjugators.
  relator-width-over-nilpotent-by-locally-finite-groups: that covers groups with bounded Fitting quotient; this class contains solvable groups with bounded primes and unbounded Fitting quotients.
  fg-simple-weakly-sofic-groups-are-sofic: that is the rigidity claim over all finite targets; this is the largest non-simple family on which the deep wreath methods were designed.
---

**ESTABLISHED** by `bounded-factor-width-from-almost-simple-quotient-bound` (2026-09-13, lane
`ex2-weak-sofic-bounded-factors`, **unreviewed**). The route uses `relator-width-bounded-by-almost-simple-quotients`,
which rests on the Nikolov--Segal import `nikolov-segal-generation-by-conjugates` and hence on
the classification of finite simple groups. Let `G = <X | R>` be an infinite finitely presented simple group that is
not sofic. For every `m` there is `K(G, m)` such that `w_Q(a) <= K(G, m)` for every finite group `Q` whose
composition factors all have order `<= m`, and every `a in Q^X`. Conjugators are taken in `Q`, and one may assume
`Q = <a>`. The proof uses neither simplicity beyond the absence of finite quotients, nor nonsoficity.

**Payoff (realized).** Weak models of `G` need targets with composition factors of unbounded order, which are
alternating groups or groups of Lie type. More sharply, the width over any target `Q` is bounded by a function
of the width over `Q/Q_0`, a subdirect product of almost simple groups
(`relator-width-bounded-by-almost-simple-quotients`, items (a) and (b)). So scarce-conjugator sections do not
create room: only large almost simple quotients do.

## Attempts

- **Settled (2026-09-13, lane `ex2-weak-sofic-bounded-factors`).** Two ingredients:
  - *Width is generation by relator conjugates.* In `Q = <a>`, if `n` conjugates of relator values generate `Q`,
    Nikolov--Segal Theorem 1.2 writes `Q'` as a bounded product of the sets `[Q, y]`. Each `[x, y]` is two
    relator conjugates, and `Q/Q'` is matched by exponent sums.
  - *Generation modulo `Q_0` is promoted to generation.* Nikolov--Segal Theorem 1.1 does this. Generation modulo
    `Q_0` comes from the finitely many marked quotients `Q/Q_0` when the almost simple quotients are bounded.
  - An elementary, classification-free partial result landed first:
    `relator-width-survives-abelian-and-central-extensions` covers abelian-by-nilpotent groups, including
    coprime `A ⋊ B`, through a duality spanning lemma for `[A, Q]`.
- **The class is the subgroup closure of towers.** By the Kaloujnine--Krasner embedding, a finite group
  with composition factors of order `<= m` embeds in an iterated wreath product of those factors in their
  regular actions, degree `<= m`. So the class is exactly the subgroups of towers of degree `<= m`. Full
  towers are settled (`simple-nonsofic-relator-width-over-iterated-wreath-products`), for every group
  without finite quotients.
- **Settled subclasses (before the general proof).**
  - *Nilpotent groups* (`perfect-group-relator-width-over-nilpotent-groups`).
  - *Nilpotent-by-(locally finite variety)* (`relator-width-over-nilpotent-by-locally-finite-groups`).
  - *Bounded derived length, trivially.* `G` is perfect, so each generator equals a fixed product of
    relator conjugates times an element of `F^(l)`.
- **Where the tower method dies.** The tower proofs use two things a subgroup lacks:
  - *Base conjugators.* The proofs use `(k at i; 1)` for arbitrary `k` in the subtree group. In `<a>` only
    elements of the subgroup are available, so dipoles and nested commutators can no longer be placed.
  - *Recursion.* On coordinates fixed by the root tuple, the recursion needs independent conjugators
    coordinate by coordinate.

  In an abelian layer `A` under an unbounded top `B`, the corrections from a template's own conjugators
  need not span `I_B A`. The fix is to use commutators with generating relator conjugates, which do span
  `[A, Q]` by duality.
- **A placement device worth trying.** Commutators `[(h; 1), P]` with `P` a *product* of relator
  conjugates realize every configuration whose twisted products along the cycles of `top(P)` are trivial.
  Tops with few cycles, which exist in `PSL_2(q)` on the projective line or in `Alt(n)`, therefore
  replace many dipole rounds by a bounded number of letters. This may still help for large almost simple
  tops, the room that remains.
- **No lower-bound mechanism was found, and none can exist here.** The class-size bound
  `w_Q(a) >= log|a_x^Q| / max_r log|r(a)^Q|` gives nothing when some relator acts at the top of a tower. The
  theorem shows that no invariant can separate on this class.
