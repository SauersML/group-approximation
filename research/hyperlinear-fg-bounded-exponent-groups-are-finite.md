---
rg: 2
id: hyperlinear-fg-bounded-exponent-groups-are-finite
kind: claim
title: Every finitely generated hyperlinear group of finite exponent is finite
distinct_from:
  infinite-fg-bounded-exponent-groups-are-non-mf: that is the operator-norm MF form of the same finiteness principle, reduced to the corona restricted Burnside statement; this is the normalized Hilbert--Schmidt form, and neither implies the other on its face.
  hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness: that is the established equivalence with a statement about limit traces of approximate exponent-N models; this is the finiteness statement itself.
---

**OPEN.** Let `G` be a finitely generated group of finite exponent. If `G` is
hyperlinear, then `G` is finite.

This is a Hilbert--Schmidt "Burnside problem". A proof would give a
non-hyperlinear group. The large odd exponent free Burnside groups are
infinite (`free-burnside-large-odd-exponent-is-nonamenable`), so they would be
non-hyperlinear, a negative answer to Weiss's Open question 9.4 in Pestov's
guide. Route: `non-hyperlinear-group-via-hyperlinear-burnside-finiteness`.

By `hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness`, this
statement for `m`-generated groups of exponent dividing `N` is equivalent to
the following. Every limit trace of approximate exponent-N unitary models
factors through a finite quotient of `F_m`.

## Attempts

1. **Hilbert--Schmidt stability of exponent laws** (approach A5 of
   `research/artifacts/ideas-2026-09-13/nh/nh-small-cancellation.md`,
   2026-09-13).
   - Its trace-level conclusion is statement 2 of the equivalence node, so
     the route is this claim, not something weaker.
   - Rounding a single generator is free: move its eigenvalues to `N`-th roots
     of unity. Rounding does not pass to products, though, and at the trace
     level there is nothing left for stability to add.
2. **Kill test: an infinite f.g. hyperlinear group of finite exponent.** None
   found. The search below is not exhaustive.
   - Pestov, arXiv:0804.3968v8, §9, Open question 9.4 (text checked): "Is
     the free Burnside group of a finite exponent n sofic?" It is recorded
     there as open. A web search found no later answer.
   - Residually finite candidates die. A f.g. residually finite group of
     finite exponent embeds in a product of finite quotients of `R(m,N)`,
     hence is a quotient of `R(m,N)` and finite (`restricted-burnside-finiteness`).
   - Bounded-dimension approximations force finiteness, not just LEF:
     `bounded-dimension-microstates-bounded-exponent-group-is-finite` passes to
     a faithful representation in `U(d)` and applies Schur's theorem. So a
     counterexample needs microstate dimensions tending to infinity. (The
     earlier inference from `bounded-dimension-microstates-force-lef` alone was
     incomplete, since LEF does not force finiteness.) An infinite
     bounded-exponent LEF group would still be a counterexample, through
     unbounded dimensions. The MF analogue of that firewall is
     `bounded-exponent-lef-group-defeats-burnside-mf-program`.
   - Amenable groups are hyperlinear, so this claim forbids infinite f.g.
     amenable groups of finite exponent. A search summary called that
     existence question open; the source was not pinned against text.
3. **Calibration through stability.** By
   `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, a flexibly
   HS-stable hyperlinear f.g. group of finite exponent is residually finite,
   hence finite. So flexible HS-stability of the bounded-exponent groups would
   prove this claim. Conversely, one infinite hyperlinear bounded-exponent
   group refutes every such stability principle for that group.
4. **Counterexample hunt and small exponents** (lane solve-nh-bounded-exponent,
   2026-09-13). Not solved; no counterexample.
   - **Verbal products give nothing.** Brude--Sasyk (arXiv:1909.07800v5,
     Theorem 1.5 and Corollary 1.6, read from the PDF, p. 3) preserve soficity
     and hyperlinearity under k-Burnside products only for `k = 2, 3, 4, 6`.
     Those are exactly the exponents where free Burnside groups are finite, so
     their constructions stay finite on finitely generated finite-exponent
     inputs. For larger `k` the `k`-Burnside product of two cyclic groups of
     order `k` is `B(2,k)` itself, since the verbal subgroup lies in `[A,B]`
     (their Corollary 2.9); soficity there is Pestov's Question 9.4 again.
   - **Small exponents are trivial.** For `N` dividing `2`, `3`, `4` or `6`,
     every f.g. group of exponent dividing `N` is finite (Burnside, Sanov,
     M. Hall; statement pinned from the "Burnside problem" survey page), so
     the claim holds there vacuously. It is open exactly where `B(m,N)` is not
     known to be finite, including `N = 5`; `B(m,N)` is infinite for odd
     `N > 665` (Adian) and large even `N` (Ivanov, Lysenok).
   - **Stability adds no leverage.** For infinite `B(m,N)`, flexible
     HS-stability plus hyperlinearity would already force residual finiteness,
     hence finiteness, so stability for these groups is at least as strong as
     their non-hyperlinearity. No mechanism for it was found. Rounding
     almost-order-`N` unitaries one at a time does not control products.
   - **Literature scan.** arXiv full-text searches for bounded exponent with
     amenable, Burnside with sofic, and finite exponent with LEF (2026-09-13)
     returned no construction of an infinite f.g. amenable, sofic, LEF or
     hyperlinear group of bounded exponent, and no finiteness theorem. The
     session's web search budget was exhausted, so MathOverflow, zbMATH and
     MathSciNet were not checked. Not exhaustive.
