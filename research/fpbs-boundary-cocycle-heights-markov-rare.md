---
rg: 2
id: fpbs-boundary-cocycle-heights-markov-rare
kind: claim
title: On every countable group every quasi-invariant boundary cocycle has Markov-rare heights, so its Radon-Nikodym growth is at most log gr and no fibre-uniform height function or fibre-uniform concatenation exists
distinct_from:
  fpbs-boundary-tilted-susceptibility-kernel: that proves the framework and the rigidity remark (a zeta-independent cocycle is trivial); this is the quantitative form valid on every group, namely that a vertex can be at height s only on a set of fibres of measure at most e^(-s), which also caps h_nu by log gr and kills fibre-uniform transfers
  fpbs-boundary-half-tilt-above-pc-universal: that is the open kernel [BT]; this proves no percolation statement and instead kills one class of attempts on [BT] on every group, amenable or not
artifacts:
  - experiments/boundary-cocycle-markov-2026-09-17/check_cocycle_markov.py
  - experiments/boundary-cocycle-markov-2026-09-17/check_cocycle_markov.out
---

**ESTABLISHED.** Proof in `fpbs-boundary-cocycle-heights-markov-rare-proof`.

**Setting.** `Gamma` is countable, `(Z,nu)` is a quasi-invariant Borel
`Gamma`-space, and `nu_y = y_* nu`. Put `Delta_zeta(o,y) = (d nu_y/d nu)(zeta)`.
Both `h_nu(zeta) = limsup_n (1/n) log max_(y in B_n) Delta_zeta(o,y)` and
`gr = lim |B_n|^(1/n)` are taken in a Cayley graph `Cay(Gamma,S)`. The notation
is that of `fpbs-boundary-tilted-susceptibility-kernel`.

**Claim.**

1. **Markov tail.** `nu(Delta_zeta(o,y) >= M) <= 1/M` for every `y` and every
   `M > 0`.
2. **Universal growth cap.** `h_nu <= log gr` holds `nu`-a.e. This is sharp: the
   visual measure on `T_d` has `h_nu = log(d-1) = log gr`. So the rate that
   [BT] certifies through item 3 of the tilt claim is at most `(log gr)/2`. That
   is the rate item (C) of `fpbs-lq-two-point-infinite-cluster-reduction` gives
   at `q = 2`.
3. **Fibre-uniform heights are bounded.** Let `H : Gamma -> R` and `delta > 0`
   satisfy `nu(Delta_zeta(o,y) >= e^(H(y))) >= delta` for every `y`. Then
   `H <= log(1/delta)` everywhere.
   - In particular, the upper `delta`-quantile height is at most `log(1/delta)`.
   - Let `D(y)` be the essential supremum of `Delta(o,y)`, and suppose
     `Delta(o,y) >= D(y)/C` holds on a set of measure `>= delta` for every `y`.
     Then `D <= C/delta`, and `h_nu = 0` a.e.
4. **High points are spread.** Let `zeta -> y(zeta)` be a Borel selection with
   `Delta_zeta(o,y(zeta)) >= e^s` on `E`. Then it takes at least
   `nu(E) e^s` distinct values.
5. **Fibre-uniform concatenation decays.** Let `y_1,...,y_k` be in `Gamma` and
   put `w_j = y_1...y_j`. Suppose `Delta_eta(o,y_j) >= e^(s_j)` on `E_j`. Then
   the set of `zeta` whose shifted fibres `w_(j-1)^(-1) zeta` all lie in their
   `E_j` has measure at most `exp(-(s_1+...+s_k))`.

**Class killed (all groups, all `nu`).** Consider a transfer of Hutchcroft's
nonunimodular layer argument (arXiv:1711.02590v3, Section 5.2) to a boundary
cocycle. This class covers every such transfer that replaces the fibre-dependent
height `log Delta_zeta(o,.)` by a `zeta`-independent height valid on a
`delta`-fraction of fibres, or that concatenates layer steps with a fibre
fraction bounded below independently of the number of steps.

- *Invariant.* The Radon–Nikodym mass `int Delta_zeta(o,y) d nu = 1`.
- *Failing step.* "Choose a vertex at height `n` for a fixed fraction of fibres",
  followed by "concatenate `k` such steps". By items 3 and 5 the first is void
  for `n > log(1/delta)`, and the second has fraction at most `e^(-kn)`.
- *Consequence.* The upward half of the deterministic layer structure is empty.
  The duality `lambda <-> 1-lambda`, which swaps the up and down layers, then
  has nothing to act on.
- *Scope.* The obstruction is not an amenable phenomenon. It holds verbatim on
  `T_d`, where [BT] is true. So nonamenability cannot rescue a fibre-uniform
  transfer.

**What survives.** Arguments that use `zeta`-dependent layer *sets*
`L_n(zeta) = {x : Delta_zeta(o,x) >= e^n}` are not touched. By item 4, such a
set spreads over at least `delta e^n` vertices on a `delta`-fraction of
fibres. The cocycle gives `x L_m(x^(-1) zeta) ⊆ L_(n+m)(zeta)` for
`x in L_n(zeta)`. Orbit-uniform bounds on `P(o <-> L_n(eta))` for these sets are
therefore still available.
