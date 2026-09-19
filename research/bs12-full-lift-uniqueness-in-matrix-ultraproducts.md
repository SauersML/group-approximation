---
rg: 2
id: bs12-full-lift-uniqueness-in-matrix-ultraproducts
kind: claim
title: Two unital lifts to the norm matrix ultraproduct of one faithful-trace embedding of C*(BS(1,2)) into R^omega are unitarily equivalent
distinct_from:
  bs12-matrix-lift-pairs-have-zero-kl-class: that proves the K-theoretic class of such a pair vanishes; this asks for the unitary equivalence itself, which also needs absorption and de-amplification.
  bs1n-rq-padded-opnorm-stability: Willett's R_q-stability is stable uniqueness after padding by an uncontrolled representation; this is uniqueness with no padding and no amplification.
---

**OPEN.**

**Statement (P2_full).**  Let `theta : A = C*(BS(1,2)) -> R^omega` be a
unital *-homomorphism with `tau_omega . theta` faithful on `A`.  Such a
`theta` is injective, since `R^omega` is a II_1 factor and its trace is
faithful.  Let `phi, psi : A -> Q_omega` be unital lifts of `theta`.  Then
there is a unitary `u` in `Q_omega` with `u phi(g) u* = psi(g)` for the two
generators `g`.  Notation is as in `bs12-matrix-lift-pairs-have-zero-kl-class`.

**Equivalent form.**  P2_full holds if and only if both of the following
hold.
- Q3_full (`bs12-faithful-trace-opnorm-correction`).
- GU_full: two sequences of genuine representations in `U(N)` with the same
  faithful limit trace are asymptotically unitarily conjugate in operator
  norm.

*Proof of the equivalence.*  Q3_full and GU_full follow from P2_full by
applying P2_full to (near-rep, HS-close genuine rep) and to (genuine,
genuine).  Conversely, by Q3_full both lifts are, along `omega`, close to
genuine representations, and those have the same faithful trace, so GU_full
conjugates them.

**The faithfulness hypothesis cannot be dropped.**  Take the two genuine
representations `1_{N-1} + chi`, with `chi` a nontrivial character of
`G^ab = Z`, and `1_N`.  They are HS-close.  They are norm-far: any unitary
conjugate of one is at distance at least `|chi(t) - 1|` from the other at
`t`, by comparing spectra.  Their common limit trace is the trivial character,
which is not faithful.

**Architecture and where each step stands.**  The steps follow the
classification-of-lifts proof of Carrion--Gabe--Schafhauser--Tikuisis--White
(arXiv:2307.06480, Thm 1.2), transplanted to `B_omega = Q_omega`.
- (a) `J_omega` is separably stable.  Plausible (projections of trace `0` are
  abundant), but not written.
- (b) Full lifts are absorbing in `M(J_E)`.  This is a Voiculescu/Elliott--
  Kucerovsky type statement.  A partial result: at a faithful trace,
  `phi(A)` meets the compacts of the ultrapower space trivially, because
  projections of positive trace have rank tending to infinity.
- (c) The KL class vanishes.  **ESTABLISHED** in
  `bs12-matrix-lift-pairs-have-zero-kl-class`.
- (d) De-amplification: `phi + phi ~ psi + psi` implies `phi ~ psi`.  This
  is the crux.  CGSTW remove the 2-fold amplification using separable
  Z-stability of `B_omega` (their Def 4.13 and Prop 4.14, via a unital
  embedding of Z into `B_omega cap B'`).  For `B = prod M_N` this route is
  closed, because the relative commutant of `prod M_N` in `Q_omega` is `C`
  (Stampfli: `||ad x|| = 2 dist(x, C)` in each `M_N`).  Whether separable
  Z-stability holds for the relevant separable subalgebras (for example the
  approximate commutant of the clock representation `pi_0`, whose exact
  commutant is abelian) is unknown.

**Consequence if true.**  Via `bs12-faithful-trace-opnorm-correction-via-uniqueness`,
we get Q3_full.  In particular the wave-14 census distance satisfies
`d(s,N) -> 0` for every fixed `s`.  So a positive census liminf would refute
P2_full, and hence (d).

## Attempts

- 2026-09-19 (swarm-0917-w15-w15-ptm-follow): isolated (a)-(d), proved (c).
  CGSTW does not apply verbatim.  Theorem 1.2 needs `B` Z-stable, and the
  Z-stable KK-uniqueness step is exactly what removes amplification.  No
  published matrix-ultraproduct result gives same-dimension uniqueness.
  Dadarlat's Thm 1.5 and Willett's R_q-stability both pad by a genuine
  representation.
