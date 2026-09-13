---
rg: 2
id: invariant-measure-gives-rank-function-any-field
kind: claim
title: Open - over an arbitrary field, does an invariant probability measure on the unit space give a faithful Sylvester matrix rank function on the Steinberg algebra
distinct_from:
  invariant-measure-gives-rank-function-in-char-zero: that is the settled characteristic-zero case, proved through the groupoid von Neumann algebra; this is the statement over an arbitrary field, where no analytic tool is available.
  measure-side-stable-finiteness-contains-char-p-kaplansky: that is the firewall showing the weaker stable-finiteness form already contains Kaplansky in characteristic p; this is the stronger rank-function form that the algebraic Tarski chain needs to reverse.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**OPEN.** Let `𝒢` be a minimal, effective, Hausdorff, ample, second countable groupoid with compact
unit space `X` carrying a `𝒢`-invariant Borel probability measure `μ`, and let `k` be any countable
field. Does `A_k(𝒢)` carry a faithful Sylvester matrix rank function with `rk(1_U) = μ(U)`?

A positive answer would reverse `algebraic-tarski-for-steinberg-algebras` and make all four conditions
of that chain equivalent over every field, so that the paradox/measure branch of a groupoid would
decide the approximation type of `EL_n(A_k(𝒢))` uniformly in `k`.

## Attempts

- **Characteristic zero: settled.** `invariant-measure-gives-rank-function-in-char-zero` proves it for
  every countable `k ⊆ ℂ` through the trace `τ(f) = ∫_X f dμ` and the Murray–von Neumann dimension of
  the groupoid von Neumann algebra. The argument dies in characteristic `p`: there is no positivity,
  no GNS space and no von Neumann algebra.
- **Cantor `Z`-systems: settled for every field.** `cantor-z-crossed-product-embeds-in-continuous-factor`
  (Ara–Claramunt) builds the rank function from a generalized Bratteli diagram and a rank completion,
  with `rk(χ_U) = μ(U)`. The mechanism is the Kakutani–Rokhlin tower structure of a Cantor minimal
  `Z`-system, not an analytic one, so it is the right template. It is not stated for general `𝒢`.
- **The Pestov groupoid: settled by hand.** The return-word tower embedding
  `LC(X,F_q) ⋊ Z ↪ ∏_ω M_N(F_q)` gives the stronger exact local embedding, hence a rank function.
- **Where a general proof should come from.** Almost finite groupoids (Kerr, Matui) carry
  Kakutani–Rokhlin towers over arbitrary index groups and are the natural common generalization of the
  two settled cases; lane `un-measure` owns that target. An invariant measure alone is not expected to
  suffice, since it gives no towers.
- **Firewall: the weaker form is already Kaplansky-hard.**
  `measure-side-stable-finiteness-contains-char-p-kaplansky` shows that even proving *invariant
  measure ⟹ stably finite* for all free minimal Cantor actions over `k` proves Kaplansky's stable
  finiteness conjecture over `k`. Since a faithful rank function implies stable finiteness, this claim
  is at least that hard in characteristic `p`, and no cheap proof should be expected.
- **Why it matters anyway.** By `invariant-measure-gives-rank-function-in-char-zero`, property (T)
  through Ershov–Jaikin-Zapirain requires a finitely generated ring, hence a finite field. So the
  Kazhdan simple groups this program produces live exactly in the characteristic where this claim is
  open, and every measure-branch example has to be witnessed individually.
