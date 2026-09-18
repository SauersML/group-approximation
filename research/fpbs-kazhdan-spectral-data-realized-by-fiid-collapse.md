---
rg: 2
id: fpbs-kazhdan-spectral-data-realized-by-fiid-collapse
kind: claim
title: Under uniqueness the two-point state is a theta-squared atom plus a reduced state, so property (T) is invisible to it, and on Kazhdan lattices in the universal cover of Sp_2n(R) an FIID collapse family realizes the whole spectral profile
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that family is not FIID on Kazhdan groups (Theorem B needs a Z-quotient) and says nothing about two-point states; here the family is FIID on Kazhdan lattices and realizes the spectral profile
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that family is deletion tolerant and FKG but not FIID, so its two-point states need not be reduced plus an atom; this one is FIID
  fpbs-fiid-partition-spectral-jump-model: that model reproduces walk-sampling data with graph-disconnected classes; this is a genuine monotone bond percolation equal to Bernoulli through p_c
  fpbs-uniqueness-spectral-atom-decomposition: that gives the moment formula a_n = theta^2 + integral t^n dnu; this identifies the full state on C*(Gamma) as atom plus reduced, for every FIID percolation with at most one infinite cluster
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-kazhdan-spectral-data-realized-by-fiid-collapse-proof`.

Let `Gamma` be nonamenable and `G = Cay(Gamma,S)`. For a percolation `omega`
let `phi(x) = P(o <-> x)` and let `s` be the state on `C*(Gamma)` it defines.

**Theorem I (atom plus reduced).** Let `omega` be a factor of iid with a.s. at
most one infinite cluster, and put `theta = P(o ∈ I)`. Then

`s = theta^2 epsilon + sigma`,

where `sigma` factors through `C*_r(Gamma)`. The proof gives each finite cluster
a random sign and writes `phi = theta^2 + <kappa(x)Z,Z>` with `Z` a mean-zero
FIID field; the Bernoulli Koopman representation is contained in a multiple of
`lambda`. Consequences:

* the Kazhdan projection gives `s(p_0) = theta^2`;
* no part of the state lies in a Fell neighbourhood of `1` other than the atom;
* the non-trivial part satisfies the Kesten gap, which is at least as strong as
  any Kazhdan constant;
* `a_n = theta^2 + integral_[0,rho] u^n dnu`.

Under collapse `p_c = p_u`, every Bernoulli `xi_p` satisfies the hypothesis.
So for every `p`, **property (T) enters the two-point state only through
`theta(p)^2`**, and that is continuous at `p_c` (sw-029).

**Theorem II (realization).** For `Gamma~_n = p^-1(Sp_2n(Z))`, `n >= 2`, which
has property (T), and for every `S`, there is a monotone family `(omega_t)` that
is jointly a factor of iid and has the following properties:

* `omega_t = xi_t` for `t <= p_c`;
* it is ergodic, mixing and insertion tolerant;
* for every `t > p_c` it has exactly one infinite cluster, with `theta(t) -> 0`;
* `phi_t -> phi_(p_c)` pointwise as `t ↓ p_c`.

It is Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines` run on
the FIID spines of `fpbs-central-z2-groups-have-fiid-sparse-spines`. By
Theorem I its states have exactly the collapse profile. At `p_c` the state is
the critical Bernoulli state, which obeys Hutchcroft's bound and is reduced by
Cowling–Haagerup–Howe.

**Corollary (obstruction).** On every Cayley graph of `Gamma~_n` no argument
can derive a contradiction from `p_u = p_c` if it uses only the following
inputs:

* Bernoulli facts at `p <= p_c`;
* soft supercritical properties (monotone coupling, FIID, mixing, insertion
  tolerance, uniqueness, continuity of `theta`);
* the spectral data of `tau_t`: Kazhdan projection, Fell support, Kazhdan and
  Kesten gaps, walk-sampling measures, reducedness, weak-* continuity.

Some `S` gives a true window (`fpbs-simple-generating-set-with-gap-exists`), and
on that graph the window and the FIID collapse satisfy the same constraints.

**Exact failing steps.**

* (F1) Mass near `1` but not on it does not exist under collapse. The
  non-atomic part is reduced, and the Kesten gap already isolates it for every
  nonamenable group.
* (F2) Hutchcroft's bound agrees with collapse. It forces `s_(p_c)` to be
  reduced, which is the `theta = 0` case of the profile.
* (F3) The pivotal-spike theorem needs Russo's identity and product structure
  above `p_c`, which the family lacks. A proof must use quantitative
  independent-increment input (Russo, BK, submultiplicativity), not the
  representation theory of `tau_t`.

**Calibration.**

* On `T_d` the state `p^|x|` is reduced for `p ∈ (1/q, q^-1/2]`, inside the
  window. So "non-reduced part beyond the atom implies a window" holds only in
  one direction, and it cannot certify a window from data at `p <= p_c`.
* The FIID spines give fixed price one for `Gamma~_n`, which is already known
  from Gaboriau (centre), so nothing contradicts Lyons.
