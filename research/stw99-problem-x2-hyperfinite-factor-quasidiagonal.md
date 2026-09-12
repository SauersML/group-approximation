---
rg: 2
id: stw99-problem-x2-hyperfinite-factor-quasidiagonal
kind: claim
title: The hyperfinite II1 factor is quasidiagonal (STW Problem X(2))
root: true
refuted_by: [hyperfinite-factor-not-quasidiagonal]
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: that quantifies over all amenable traces on all C*-algebras; this is the single instance of the trace of R, which STW expect to be the heart of the non-exact case.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
  - research/artifacts/stw99-x2-2026-literature-and-route-audit-2026-08-31.md
---

**Problem X(2) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  Is the hyperfinite II₁ factor `R` quasidiagonal
(as a C\*-algebra)?

**Literature status (reverified 2026-08-31):** open.  Popa devoted a
W\*-News post to exactly this question on 2026-05-28
(`popa-projection-formulations-of-x2` imports its equivalent
formulations: operator-norm Folner projections on `L²(R)`, and the
local-AFD criterion), quoting Brown--Ozawa's "this seems unlikely, but
a proof would be nice"; an Oberwolfach problem session poses it as
Problem 16 together with the strictly weaker MF variant, now carried
as `hyperfinite-factor-mf`.  The positive route's exact missing lemma
is `norm-folner-projections-for-hyperfinite-factor`: Connes' Folner
condition gives the Hilbert--Schmidt version unconditionally, and the
norm upgrade admits no dimension-free conversion (checked rank-`n`
projection pair in that node's Attempts).

The post-Popa theorem of Alekseev--Thom (arXiv:2606.07369,
2026-06-05) does not change this status.  It proves Ulam stability of
`R` for defects and conclusions measured in normalized trace norm,
after amplification; it neither asserts quasidiagonality nor upgrades
Hilbert--Schmidt leakage of finite-rank projections to operator-norm
leakage.  The distinction is audited in
`research/artifacts/stw99-x2-2026-literature-and-route-audit-2026-08-31.md`.

**Packet normal form (2026-08-31):** the packet quantifier in the
local-AFD formulation collapses — X(2) is equivalent to local AFD for
all THREE-operator packets `{u, w, x}` (two unitaries and a
contraction), by the clock-shift encoding of
`x2-reduces-to-three-operator-packets`.  Commuting packets are solved
(`x2-local-afd-holds-on-abelian-packets`), rate-controlled packets are
solved (`x2-local-afd-holds-at-rate-controlled-packets`), and any
refuting packet must carry full-support non-normal mass with no
2-norm approximation rate
(`shadow-avoidance-fails-at-column-isometries` closes the
commutant-reduction escape).  Ultraproduct ambience cannot help:
`matrix-tracial-ultraproduct-trace-not-quasidiagonal`,
`hyperfinite-ultrapower-trace-not-quasidiagonal`.

The rate-controlled cell has been sharpened:
`stw99-x2-local-afd-at-partial-trace-rate` replaces entrywise cuts by
one operator-valued partial-trace cut and proves local AFD whenever
`dist_2(Y,M_d)=O(d^{-1})`.  Together with the column-isometry obstruction
at scale `d^{-1/2}`, this narrows the relative-commutant exponent gap to
`[1/2,1]`; it still supplies no rate for an arbitrary hyperfinite packet.

Since `R` has a unique trace and that trace is faithful, this is equivalent to
asking whether `τ_R` is a quasidiagonal trace (Brown's Proposition 4.1.3
argument: a faithful quasidiagonal trace makes the algebra quasidiagonal by
Voiculescu's characterization).  `τ_R` is amenable, by Connes' Følner
condition for `R` (Brown, Theorem 3.1.7(3)), so a positive answer to
Problem X(1) gives a positive answer here (`stw99-x1-implies-x2`).

STW: "It seems likely to us that for not necessarily exact C*-algebras, the
heart of the matter is whether the trace on the hyperfinite II₁ factor is
quasidiagonal."  Not to be confused with `stw99-problem-xciv-hyperfinite-factor-separably-z-stable`.

The norm-nonseparability of `R` is not itself part of the obstruction.
`stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses` proves that
`R` is quasidiagonal exactly when every finitely generated weakly dense
unital C-star subalgebra is quasidiagonal.  If the answer is negative, one
may choose such a witness to contain a fixed weakly dense CAR algebra.  Its
restricted trace is faithful and amenable, has GNS closure `R`, but is not
quasidiagonal; the witness cannot be both exact and UCT.  The CAR core records
the available Hilbert--Schmidt approximation, while a finite added set
records the unresolved operator-norm obstruction.

There is also an exact finite-stage normal form for the missing
operator-norm models.  By
`stw10-qd-traces-admit-exact-finite-dimensional-core-models`, after fixing a
weakly dense CAR tower `D_n subset R`, X(2) is equivalent to the existence,
for every finite packet and every `n`, of a quasidiagonal trace model having
`D_n` in its multiplicative domain.  Such a model is a genuine unital
representation on `D_n` and recovers `tau_R|D_n` exactly.  Thus the CAR stage
may be frozen without loss: the open hinge is precisely operator-norm
multiplicativity for the finitely many elements outside that exact core.
This is a finite-set/net statement for the nonseparable factor, not a claim
that one sequence models all of `R`.

The exact core can further be divided out of every model.
`stw10-matrix-core-models-are-corner-amplifications` proves that, for
`D_n isomorphic to M_d` and `p_n=e_11`, the canonical identification

```text
R isomorphic to M_d(p_n R p_n)
```

carries every core-exact u.c.p. model, up to a target unitary, to precisely
`id_(M_d) tensor chi` for a u.c.p. corner map
`chi:p_n R p_n -> M_m`.  Its multiplication defect is the explicit matrix
of sums of corner defects, and the normalized trace is
`tr_d tensor (d tau_R|p_n R p_n)`.  Thus X(2) has an exact Morita normal
form: all approximation data live in one `e_11` corner, the ambient model
size is forced to be `dm`, and the CAR matrix action carries no residual
choice or error.

**Group reduction (2026-08-30).**  If `R` is quasidiagonal then every
countable subgroup of `U(R)` is an MF group
(`hyperfinite-factor-qd-forces-unitary-subgroups-mf`).  So a single non-MF
group with a faithful hyperfinite character refutes this problem
(`hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`).  Kazhdan
non-MF groups cannot be that witness, since a finitely generated Kazhdan
subgroup of `U(R)` is residually finite
(`kazhdan-groups-in-hyperfinite-unitary-group-are-rf`).  The former literal
group candidate is now excluded as well:
`literal-group-mark-invisible-to-hyperfinite-representations` shows that its
central mark dies in every finite injective representation.

This route is NOT invalidated by `x2-witnesses-are-never-group-shaped`.
That theorem excludes canonical `delta_e` group traces and amenable-action
crossed-product traces.  The live route asks for a noncanonical faithful
hyperfinite character, whose off-identity values may be nonzero.  The
Kazhdan and marked-packet no-go theorems exclude candidate classes only;
no general theorem here rules out a non-MF subgroup of `U(R)`.

The representation-free Clifford exclusion now has its sharp finite-block
form.  `signed-clifford-cycle-trace-formula` computes the implementing trace
for every signed permutation of `2m` Clifford generators.  A single cycle
whose sign-product equals `(-1)^(cycle length)` makes that trace zero.
Consequently `marked-clifford-compressor-hyperfinite-invisibility` excludes
any marked candidate whose abelian compressor family contains such a cycle,
provided the existing nonamenable Haar-null dual-action hypotheses hold.
This strictly extends the former fixed-point-free-involution test to even
cycles with fixed points and to negatively signed odd cycles; it remains an
exclusion theorem for proposed group witnesses, not a resolution of X(2).

The finite-dimensional mechanism itself is now independent of Clifford
relations.  `finite-packet-compressor-hyperfinite-invisibility` allows an
arbitrary finite subgroup and an arbitrary semisimple negative
central-character block.  A normalizer's moved irreducible summands are
automatically off-diagonal and traceless; only its fixed summands need
traceless inner implementers.  Matrix-corner trace factorization then
replaces the Clifford calculation; compressor conjugacy and the nonamenable
Haar-dual action finish the same obstruction.  Thus any marked candidate
built from such a finite representation packet is also excluded.  This
enlarges the no-go class but does not provide the non-MF subgroup of `U(R)`
needed to decide X(2).  The argument works separately in every nontrivial
spectral sector of an arbitrary finite-order central mark, so it also
excludes odd-prime marked variants when the corresponding finite packets
satisfy the same fixed-block trace test.

**Downstream (2026-08-30 rewiring):** a positive X(2) restricts
through injective GNS closures, so it implies that EVERY trace on
every separable nuclear C\*-algebra is quasidiagonal — in particular
Problem IX(1) (`stw99-x2-implies-ix1`) and the simple case of
Blackadar--Kirchberg (`stw99-vii-restricted-to-simple-algebras` via
`stw99-ix1-implies-vii-simple`).  With X(1) refuted by the
literal-group counterexample (non-nuclear, non-injective GNS — it
cannot enter these routes), X(2) is now the live ancestor of the
whole nuclear quasidiagonality cluster.
