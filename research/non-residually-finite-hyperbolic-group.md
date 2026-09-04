---
rg: 2
id: non-residually-finite-hyperbolic-group
kind: claim
title: A word-hyperbolic group that is not residually finite
root: true
distinct_from:
  oyakawa-graph-wreath-rf-iff-acting-group-rf: that is an established equivalence inside one construction, saying that a residual finiteness failure there is always inherited from the acting group; this is the open existence question that construction was hoped to settle, and the equivalence is precisely why it does not
  persistent-degree-two-class-on-hyperbolic-group: that is the cohomological input to one of the four live routes, a statement about classes and finite-index subgroups of a group already known to be residually finite; this is the counterexample target itself, which three other routes reach without any cohomology
  exact-stably-finite-non-mf-reduced-group-algebra: that is a proved C-star statement about the quotient witness W — exact, stably finite, not MF; this is an open group-theoretic existence question about hyperbolic groups and their finite quotients, and no operator algebra appears in it
  nonsofic-hyperbolic-group: that claim demands a hyperbolic group that is not sofic, which is strictly stronger — non-soficity implies failure of residual finiteness, but this claim is also satisfied by a group that is sofic and not residually finite, which is exactly the shape of this repository's own literal group E
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
---

Produce a word-hyperbolic group that is not residually finite, or prove that
none exists.

This is the long-standing question usually attributed to Gromov.  It remains
open as of 2026-08-24: Cui--Wan, arXiv:2604.04007 (5 April 2026), say in their
§1.2 that residual finiteness of every hyperbolic group is still an open
conjecture.  None of the constructions recorded below changes that status.

## Why it sits in this program

Two of this program's objects sit directly above and below it.

Above: `nonsofic-hyperbolic-group`.  A non-sofic group is never residually
finite, so a non-sofic hyperbolic group settles this claim as a corollary
(`non-rf-hyperbolic-from-nonsofic-hyperbolic`).  That is the *only* logical
traffic between the two, and it runs one way.  The graph carries the weaker
demand separately because three of the four live attacks below reach it
without saying anything about soficity, and because the converse fails —
this repository's own literal group `E` is sofic and not residually finite
(`literal-group-sofic`, `literal-mark-quotient-finite-residual`), so a
non-residually-finite hyperbolic group need not be a second non-soficity
mechanism.

Below: nothing.  A resolution in the *positive* direction — every hyperbolic
group is residually finite — would not close any hole in this graph either;
it would remove `nonsofic-hyperbolic-group` as a Q3.4 candidate, since
residually finite groups are sofic.

## Attempts

Five live routes, none of which this graph can yet walk:

- `non-rf-hyperbolic-via-periodic-higman` — the explicit singular-on-`H_1`
  endomorphism `x_i |-> [x_i,x_(i-1)]` has a hyperbolic mapping torus, and its
  sufficiently deep torsion fillings retain the base mark.  Every finite
  image of a filling has a perfect base image governed by one finite-order
  automorphism.  The route is reduced exactly to
  `periodic-higman-large-prime-period-gap`: one prime above the filling
  threshold must be absent from the resulting Higman period spectrum.  That
  finite-group statement is open here. The 2026-09-04 result
  `periodic-higman-spectrum-is-cofinite` proves that every integer above
  `B_*=4000*40^12` belongs to the spectrum, and gives finite quotients
  detecting all four base generators at those periods. Only the finite
  interval `[m_0,B_*]` can still supply a missing prime for this route.

- `non-rf-hyperbolic-from-nonsofic-hyperbolic` — inherit it from a non-sofic
  hyperbolic group.  Blocked exactly where `nonsofic-hyperbolic-group` is
  blocked, i.e. on the Chapman--Peled estimate.
- `non-rf-hyperbolic-via-relative-dehn-filling` — build the counterexample
  *relatively* hyperbolic with residually finite peripherals and fill.  The
  filling step is proved; the input claim
  `non-rf-relatively-hyperbolic-with-rf-peripherals` is open and, by that very
  reduction, is not easier than this one.
- `non-rf-hyperbolic-via-persistent-central-extension` — a finite central
  extension of a residually finite hyperbolic group whose class survives
  restriction to every finite-index subgroup.  The criterion is classical and
  established here (`finite-central-extension-rf-iff-virtually-splits`); the
  cohomological input `persistent-degree-two-class-on-hyperbolic-group` is
  open, and the nearest arithmetic sources push the other way.
- `non-rf-hyperbolic-via-rips-kernel` — a hyperbolic Rips extension of a
  non-residually-finite quotient whose kernel has no finite quotients.
  Belegradek--Osin supply everything except the kernel condition, and that
  condition is `rips-kernel-without-finite-quotients`, which is open and
  adjacent to circularity.

Four older attacks are recorded dead, each with its own route and its own
obstruction: transplanting this program's finite-residual compression witness
into a hyperbolic ambient group
(`non-rf-hyperbolic-via-compression-transplant`), its free-lamp repair
(`non-rf-hyperbolic-via-free-lamp-compression`), Oyakawa's hyperbolic
graph-wreath products (`non-rf-hyperbolic-via-oyakawa-graph-wreath`), and
routing a known non-residually-finite group through Hull's small-cancellation
theorem (`non-rf-hyperbolic-via-hull-routing`).

The strongest natural shortcut inside the new periodic-Higman route is also
dead.  `periodic-higman-spectrum-contains-three` gives an exact
`PSL_2(11)` certificate with period three, refuting
`periodic-higman-spectrum-has-no-odd-primes` and invalidating
`non-rf-hyperbolic-via-odd-period-exclusion`.  Borisov--Sapir's residual
finiteness theorem for the *unfilled* injective free-group mapping torus is a
second consistency check: the torsion filling is indispensable, not a
cosmetic step.

Conservatively modeled as OPEN.  The periodic-Higman construction is a real
reduction to a sharply isolated finite-group lemma, not a solution; claiming
otherwise would erase the only unproved implication in the construction.
