---
rg: 2
id: set-indexed-repetition-escapes-the-base-sdp-bound
kind: claim
title: Set-indexed (unordered) repetition escapes Steurer's base-SDP lower bound -- a tagged odd cycle has set value O(m/n) while n times its SDP deficit tends to 0 -- but the black-box odd-cycle sqrt-scale kill still transfers to it
distinct_from:
  steurer-parallel-repeated-unique-games-rounding: that bound (S1) holds for ordered repetition G^l; this shows no bound of that shape holds for set-indexed repetition.
  parallel-repetition-cannot-substitute-rounds-for-alphabet: that kill is for ordered repetition via (S1); this is the separate set-indexed class, on which (S1) fails and the kill must be re-derived.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kill is for ordered repetition with a universal bound; this transfers it to set-indexed repetition via disjoint copies, and shows the survivor mechanism (tag anonymity).
  raz-odd-cycle-repetition-lower-bound: that is the ordered repeated value of C_m; this proves an upper bound O(m/n) on the set-indexed value of a tagged blow-up of C_m.
---

**ESTABLISHED.** Proved in the route below. It uses only
`raz-odd-cycle-repetition-lower-bound` (by citation) and the elementary
Chernoff bound.

**Set-indexed repetition.** Let `G` be a unique game with question
distribution `(u, v, pi)` on vertex sets `U, V` and alphabet `[k]`. The
`n`-fold *set-indexed repetition* `G^{{n}}` is defined as follows.

* Sample `n` iid edges `(u_j, v_j, pi_j)` and condition on the event `Good`
  that the `u_j` are distinct and the `v_j` are distinct.
* Alice receives the set `A = {u_1, ..., u_n}` and Bob receives the set
  `B = {v_1, ..., v_n}`. Neither learns the matching `j`.
* They answer `alpha : A -> [k]` and `beta : B -> [k]`, that is, labels in
  `[k]^n` in a fixed order of the set. They win iff
  `beta(v_j) = pi_j(alpha(u_j))` for every `j`.

`G^{{n}}` is a unique game with alphabet `k^n`. It is a multigraph, because
one pair `(A, B)` can carry several hidden matchings.

**Statement.**

**(A) The base-SDP lower bound fails.** For odd `m >= 3` and `M >= 1`, let
`G_{m,M}` be the *tagged odd cycle*. Alice's question is `(x, a)` and Bob's is
`(y, b)`, where:

* `(x, y)` is distributed as in `C_m`;
* the tags `a, b` are uniform in `[M]` and independent;
* the bits must be equal iff `y = x`.

The game satisfies the following.

1. `val(G_{m,M}) = 1 - 1/(2m)` and `sdp(G_{m,M}) >= 1 - pi^2/(8 m^2)`.
2. The ordered repetition has value tending to 1 at this scale. By (S1),
   `opt(G_{m,M}^n) >= 1 - C_1 sqrt(n ln 2) pi/(sqrt 8 m)`. By Raz,
   `opt(G_{m,M}^n) >= 1 - B sqrt(n)/m`.
3. If `M >= n^2`, the set-indexed repetition satisfies

   ```text
   val(G_{m,M}^{{n}})  <=  2 [ 2m/n + 2m e^{-n/(8m)} + 6 (3/4)^{n/(2m)} ].
   ```

Take `n = m^{3/2}`. Then `n (1 - sdp) <= pi^2/(8 sqrt m) -> 0` and the ordered
value tends to 1, while the set-indexed value is `O(m^{-1/2}) -> 0`. So no
bound of the form

```text
opt(G^{{n}}) >= 1 - Psi(n (1 - sdp(G)), k),  with  Psi(t, 2) -> 0 as t -> 0,
```

holds, even at `k = 2`. Steurer's (S1), and every kill built on it, does not
extend to set-indexed repetition.

**(B) The black-box kill transfers.** A *universal set bound*
`F_set(gamma, n)` bounds `val(G^{{n}})` over all unique games with
`val(G) <= 1 - gamma`. Every universal set bound satisfies
`F_set(gamma, n) >= 1 - 4 B gamma sqrt(n)` for `0 < gamma <= 1/8`. Hence the
conclusion of `black-box-repetition-needs-sqrt-scale-soundness-gap`, Part 2,
holds verbatim for set-indexed amplifiers:

```text
gamma  >=  min( 1/8 ,  (1 - delta') sqrt(eta) / (4 B sqrt(2 eps')) ).
```

Here completeness is certified by product strategies. On `G^{{n}}` the
certificate is `(1-eta)^n - Pr[not Good] >= 1 - eps'`. It is valid, because a
product strategy restricted to the sets wins with probability at least
`(1-eta)^n - Pr[not Good]` given `Good`. It implies `(1-eta)^n >= 1 - eps'`,
which is all that Part 2 uses.

**Invariant and death step.**

* **(A) kills the transfer.** The class is "rounds versus alphabet via the
  base SDP" (`parallel-repetition-cannot-substitute-rounds-for-alphabet`). It
  does not cover set-indexed repetition. The dying step is the lifting of an
  ordered strategy: players who cannot agree on the coordinate order cannot
  run a coordinate-wise rounding. The quantity that separates the two
  repetitions is *tag anonymity*. Bob's `n_z` tags at position `z` are
  exchangeable given Alice's view, so each mixed required multiset `R_z` costs
  a factor `1/C(n_z, r_z) <= 1/n_z`. The odd cycle forces a mixed `R_z` except
  with probability `6 (3/4)^g`.
* **(B) kills black-box set-indexed amplification.** The invariant is again
  the ratio `gamma/sqrt(eta)`. Every member dies at the universal-bound
  soundness step, on the disjoint union of `M -> infinity` copies of `C_m`.
  There the copy index is a public coordinate order, so anonymity is lost and
  Raz's ordered strategy runs.

**Consequence for `sqrt-scale-unique-games-hardness`.** Neither the (S1)
obstruction nor the universal-bound obstruction blocks the following route.
The route is not closed; it is a sharpened decomposition.

* **Survivor (anonymity-certified set repetition).** Take a set-indexed
  amplifier whose soundness proof uses anonymity of the hard instances. For
  example, the instances could be the tagged blow-ups of the source gap, where
  the blow-up is applied by the reduction itself.
  - Completeness: tagging preserves a `(1-eta)` product strategy. The product
    certificate then gives `n <= 2 eps'/eta`, so rounds are still paid
    linearly in `1/eta`.
  - Soundness: it must beat `1 - 4 B gamma sqrt(n)` only on the tagged
    instances, not universally.
  - Its first independently failable prerequisite is a tagged-set soundness
    bound `val(G) <= 1 - gamma => val(G_{tag,M}^{{n}}) <= delta'` at
    `n ~ eps'/eta` and `gamma = o(sqrt eta)`. Part (A) proves the analogue of
    this bound for odd cycles at `gamma = 1/(2m)` and `n >> m`.
* **Not a survivor.** Set-indexed repetition with a universal soundness bound
  is dead, by (B).

The checks are in
`experiments/ugc-set-indexed-2026-09-17/output.txt`:

* the SDP vectors, to `1e-16`;
* Lemma W by Monte Carlo;
* `E[Phi]` for natural strategies against the bound in (A).

DERIVATION set-indexed-repetition-escapes-the-base-sdp-bound-proof
