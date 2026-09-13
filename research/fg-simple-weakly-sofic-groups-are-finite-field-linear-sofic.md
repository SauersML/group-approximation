---
rg: 2
id: fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic
kind: claim
title: Every finitely generated simple weakly sofic group is linear sofic over finite fields
distinct_from:
  fp-simple-weak-soficity-is-finite-field-linear-soficity: that proves this for finitely presented simple groups, where the PSL dichotomy uses a finite presentation; this asks it for finitely generated simple groups, the class on which the rigidity claim and its Kazhdan envelope route are stated.
  fg-simple-weakly-sofic-groups-are-sofic: that is the rigidity claim, which implies this one; with this claim, the rigidity claim becomes the statement that finitely generated simple groups linear sofic over finite fields are sofic.
---

**OPEN.** Let `G` be a finitely generated simple group that is weakly sofic. Then `G` embeds in a rank-metric
ultraproduct of groups `GL_(n_i)(F_(q_i))` (definition on `simple-group-psl-width-is-finite-field-linear-soficity`).

**Payoff.**
- **True.** `fg-simple-weakly-sofic-groups-are-sofic` becomes: *every finitely generated simple group that is linear sofic
  over finite fields is sofic*. The Kazhdan envelope route `non-weakly-sofic-group-from-simple-weak-sofic-rigidity` then
  needs only that statement, for the simple Kazhdan envelope of the Kun--Thom wreath.
- **False.** There is a finitely generated simple weakly sofic group that is not linear sofic over finite fields. It is
  nonsofic, so it refutes the rigidity claim. It also answers `non-linear-sofic-group` with a weakly sofic witness.
  By the finitely presented theorem, it cannot be finitely presented.

## Attempts

- **Finitely presented case: settled** (`fp-simple-weak-soficity-is-finite-field-linear-soficity`, unreviewed).
- **Reduction to `PSL_n(q)`: available for finitely generated groups.** By Theorem 4 of
  `nst-simple-weakly-sofic-groups-are-psl-approximable`, `G` is approximable by groups `H_i = PSL_(n_i)(q_i)` with invariant
  lengths `l_i`. Lemma 1 there lets one take `diam(H_i, l_i) = 1`.
- **Null lengths have null ranks.** Take `g in H_i` with `l_i(g) >= 1/2`. Liebeck--Shalev covering
  (`liebeck-shalev-normal-subset-covering`) writes `g` as a product of `k <= c log|H_i| / log|h^(H_i)|` conjugates of
  `h^(+-1)`. So the conjugacy length `l^c(h) = log|h^H| / log|H|` satisfies `l^c(h) <= 2c l_i(h)`. Nikolov--Schneider--Thom
  (page 4) record that `l^c` and the projective rank length `l^pr` are Lipschitz equivalent on non-abelian finite
  simple groups. So the identity induces a homomorphism from the `l`-ultraproduct onto the projective-rank
  ultraproduct `prod_U (PSL_(n_i)(q_i), l^pr)`. This step has not been written as a proof node.
- **Dichotomy for simple `G`.** The composite `G -> prod_U (PSL_(n_i)(q_i), l^pr)` is injective or trivial.
  - *Injective.* `G` is projectively linear sofic over finite fields. Passing to linear soficity should use the
    adjoint action `X -> g X g^-1` on `M_n`, whose rank is comparable to `n` times the rank distance of `g` to the scalars.
    This is the projective item of `simple-group-support-and-semisimple-rank-models-collapse` for finitely presented
    groups. It is not written for finitely generated ones.
  - *Trivial: the near-scalar horn, where the claim is open.* Every `g in G` then has `l^pr(phi_i(g)) -> 0`, while
    `l_i(phi_i(g)) >= delta_g`. Invariant lengths separating near-scalar elements do exist, for example the capped number
    of transvections needed to write an element. For bounded `n_i` this horn is empty: a noncentral element of
    `PSL_n(q)` has class size at least `|H|^(c(n))`, so `l^c -> 0` forces `phi_i(g) = 1`. So the open case has `n_i -> ∞`
    and tuples within rank `o(n_i)` of the scalars.
- **Why the finitely presented proof does not transfer.** In the near-scalar case,
  `simple-group-psl-width-is-finite-field-linear-soficity-proof` matches the big kernel block with the nilpotent
  template, using finitely many relators and a fixed perfectness identity. A finitely generated simple group has
  such identities too. But the width formulation behind the Glebsky--Rivera reflection needs one finite relator set
  that normally generates the kernel.
