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

**OPEN.** Let `G = <X | R>` be an infinite finitely presented simple group that is not sofic. For every
`m` there is `K(G, m)` such that `w_Q(a) <= K(G, m)` for every finite group `Q` whose composition factors
all have order `<= m`, and every `a in Q^X`. Conjugators are taken in `Q`, and one may assume `Q = <a>`.

**Payoff.**
- **True.** Weak models of `G` need targets with composition factors of unbounded order, which are
  alternating groups or groups of Lie type. Together with
  `simple-group-width-over-all-finite-simple-groups`, the remaining room would be groups in which large
  simple factors occur as scarce-conjugator sections.
- **False.** `G` is weakly sofic through finite groups with bounded composition factors, for example
  solvable groups with bounded primes. That separates weak soficity from soficity with a finitely
  presented simple group and refutes `fg-simple-weakly-sofic-groups-are-sofic`.

## Attempts

- **The class is the subgroup closure of towers.** By the Kaloujnine--Krasner embedding, a finite group
  with composition factors of order `<= m` embeds in an iterated wreath product of those factors in their
  regular actions, degree `<= m`. So the class is exactly the subgroups of towers of degree `<= m`. Full
  towers are settled (`simple-nonsofic-relator-width-over-iterated-wreath-products`), for every group
  without finite quotients.
- **Settled subclasses.**
  - *Nilpotent groups* (`perfect-group-relator-width-over-nilpotent-groups`).
  - *Nilpotent-by-(locally finite variety)* (`relator-width-over-nilpotent-by-locally-finite-groups`).
  - *Bounded derived length, trivially.* `G` is perfect, so each generator equals a fixed product of
    relator conjugates times an element of `F^(l)`.

  So unbounded derived length and unbounded Fitting quotient are both needed.
- **Where the tower method dies.** The tower proofs use two things a subgroup lacks:
  - *Base conjugators.* The proofs use `(k at i; 1)` for arbitrary `k` in the subtree group. In `<a>` only
    elements of the subgroup are available, so dipoles and nested commutators can no longer be placed.
  - *Recursion.* On coordinates fixed by the root tuple, the recursion needs independent conjugators
    coordinate by coordinate.

  In an abelian layer `A` under an unbounded top `B`, the available corrections are sums of translates
  `beta (1 - r-bar) A` by the template's own conjugators, and they need not span the augmentation
  submodule `I_B A`.
- **A placement device worth trying.** Commutators `[(h; 1), P]` with `P` a *product* of relator
  conjugates realize every configuration whose twisted products along the cycles of `top(P)` are trivial.
  Tops with few cycles, which exist in `PSL_2(q)` on the projective line or in `Alt(n)`, therefore
  replace many dipole rounds by a bounded number of letters. This suggests extending
  the full-tower theorem to unbounded simple vertex groups of bounded rank, where short-cycle relator
  tops otherwise defeat bounded placement. It does not address the scarcity of conjugators in
  subgroups.
- **No lower-bound mechanism is known.** The class-size bound
  `w_Q(a) >= log|a_x^Q| / max_r log|r(a)^Q|` gives nothing when some relator acts at the top of a tower, since
  its class is then a fixed power of `|Q|`. A refutation needs an invariant of products of few conjugates
  that is not a function of class size or support, in groups with scarce conjugators.
