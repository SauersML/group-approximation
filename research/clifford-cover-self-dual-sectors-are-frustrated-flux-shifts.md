---
rg: 2
id: clifford-cover-self-dual-sectors-are-frustrated-flux-shifts
kind: claim
title: On a central Z/2-extension, self-dual automata act on the eps-odd sector as W-automata on a frustrated flux shift, bijective whenever a character detects eps
distinct_from:
  clifford-cover-group-algebra-splits-into-wreath-and-skew-ring: that splits the ternary group algebra into the wreath and the anti-central skew ring, which governs linear automata; this is the nonlinear binary sector of self-dual rules, written as a gauge-field subshift over W.
  copying-rules-lift-to-clifford-covers-only-as-shifts: that shows site-level lifts land in eps-fixed configurations, where injective automata are bijective; this describes the eps-odd sector where the twist can still act.
  strict-automata-memory-keeps-finite-normal-kernel-residual: that forces eps into the finite residual of the memory group of a strict automaton; this adds, for self-dual rules, that eps must be a product of squares and commutators of the memory group.
artifacts:
  - research/artifacts/clifford-copying-rule-lift-2026-09-12.md
---

**ESTABLISHED** by `self-dual-sector-frustrated-flux-shift-proof` (artifact Section 2; verification requested from
`w3-vf-nonlinear`).

**Setting.** `E` a group with central involution `eps`, `W = E/<eps>`, binary alphabet, and a rule `mu` that is
self-dual: `mu(a + 1) = mu(a) + 1`. The sector is `Tw = { x : x(eps e) = x(e) + 1 }`.

**Theorem.**
1. `tau(Tw) <= Tw`, and for injective `tau`, `tau(F_2^E) cap Tw = tau(Tw)`.
2. `x -> Theta_x(w, m) = x(e) + x(e m)` identifies `Tw` modulo the global flip, `W`-equivariantly, with the subshift
   `Z_omega` of `Z/2`-gauge fields on the Cayley graph of `W` whose holonomy on each relator `r` is `omega(r)`, where
   `r = eps^(omega(r))` in `E`.
3. `tau` induces a `W`-automaton on `Z_omega`, injective when `tau` is, and `tau(Tw) = Tw` iff it is onto.
4. `Z_omega` is a torsor under the full shift `F_2^W/flip` of flat fields.
5. If a homomorphism `theta : <M> -> Z/2` has `theta(eps) = 1` and `<M>/<eps>` is surjunctive, every injective
   self-dual automaton maps `Tw` onto `Tw`.
6. On a Clifford cover `E_S`, `omega = b_S(o, g o)` on the plaquette `[c_o, g c_o g^(-1)]`, `q` on `c_o^2`, and `0` on
   the relators of `G` and on `[Gamma, c_o]`. On the complete graph every plaquette at distinct sites carries flux `1`,
   and `eps` is a commutator, so no character detects it.

**Payoff.** In the split extension `W x Z/2` the sector is the full shift modulo flip and injective self-dual
automata are bijective on it. On the complete-graph Kun--Thom cover the Clifford twist enters this sector only as the
frustration `omega = 1` on lamp plaquettes. A self-dual strict automaton on `E_S` whose image misses a configuration
of the sector exists iff some self-dual automaton is injective on `F_2^(E_S)` while its induced map misses part of
`Z_omega`. Design filter: for such an automaton the memory group must contain `eps` as a product of squares and
commutators.

Open: whether `Z_omega` and the flat shift are conjugate as `W`-subshifts, compatibly with induced automata.
