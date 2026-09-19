---
rg: 2
id: dadarlat-matricial-stability-obstruction
kind: claim
title: Dadarlat's matricial-stability obstruction — exact hypotheses, norm, and cohomology
distinct_from:
  exel-loring-relative-quasirep-invariant: that records the two-homology quasi-representation invariant from the companion paper; this pins the stability-obstruction theorem's hypotheses, its stability notion, and its cohomological conclusion
  matrix-corona-k1-vanishes: that is a K-theory computation for the norm matrix corona; this is a cohomological obstruction to matricial stability of a group
---

Read from the PDF of arXiv:2007.12655v2 (Dadarlat, *Obstructions to matricial
stability of discrete groups and almost flat K-theory*) on 2026-08-14, on
demand for `cairn-torsionfree`'s mutual-exclusivity paragraph.  Three
questions, three answers.

## 1. The stability notion is point-norm, exactly as hoped

> "A group `G` is called `(U(k_n), ||.||)_n`-stable [34] or **matricially
> stable** [38] if for any asymptotic homomorphism
> `{phi_n : G -> U(k_n)}_(n in N)` (not necessarily a separating one) there is
> a sequence of homomorphisms `{pi_n : G -> U(k_n)}_(n in N)` such that
> `lim_(n->infinity) ||phi_n(s) - pi_n(s)|| = 0` for all `s in G`."

Operator norm on `U(k_n)`, and the limit is required **for each `s`
separately** — pointwise on the group, not uniformly over it, and not in any
Schatten norm.  So it is point-norm in the intended sense.

**Weakly matricially stable** is the padded variant: for any sequence of ucp
maps `phi_n : G -> M_(k_n)` satisfying his condition (1), there are
homomorphisms `pi_n^(0), pi_n^(1)` with
`lim ||phi_n(s) ⊕ pi_n^(0)(s) - pi_n^(1)(s)|| = 0` for all `s in G`.
Matricial stability implies weak matricial stability; MF implies weak
quasidiagonality.

## 2. The cohomological conclusion is rational cohomology, all nonzero even degrees

> **Theorem 1.1.** Let `G` be a countable discrete MF-group that admits a
> `gamma`-element (e.g. `G` is uniformly embeddable in a Hilbert space).  If
> `H^(2k)(G, Q) != 0` for some `k >= 1`, then `G` is not matricially stable.

> **Theorem 1.2.** Let `G` be a countable discrete weakly quasidiagonal group
> that admits a `gamma`-element.  If `G` is weakly matricially stable, then
> `G` is MAP and `H^(2k)(G, Q) = 0` for all `k >= 1`.

Group **cohomology** with **rational** coefficients, in **all** nonzero even
degrees — not homology, not integral, and it is the cohomology of the whole
group, not of an almost-flat part.  The MAP conclusion comes along with it.

## 3. Which classes — Kazhdan groups are neither blanket-in nor blanket-out

Two hypotheses carry the theorems: **weak quasidiagonality** (implied by MF)
and existence of a **`gamma`-element** (satisfied by uniformly embeddable
groups, so in practice rarely the binding one).  The binding constraint is
weak quasidiagonality, and for Kazhdan groups it is governed by:

> **Proposition 3.19 (Ozawa-Thom).** If an infinite property (T) group `G` is
> weakly quasidiagonal, then `G` has an infinite residually finite quotient.

**Contrapositive, and this is the operative fact:** an infinite property-(T)
group with *no* infinite residually finite quotient is **not** weakly
quasidiagonal, hence falls outside Theorem 1.2 entirely.  That is exactly the
minimally-almost-periodic regime this program's compression bases live in.

But the exclusion is not blanket, because of:

> **Corollary 1.3.** If `G` is a countable **linear** group such that
> `H^(2k)(G, Q) != 0` for some `k >= 1`, then `G` is not weakly matricially
> stable.

Linear groups are uniformly embeddable and quasidiagonal enough for the
machinery, so **linear Kazhdan groups are covered** — and the bases used here
(`SL_3(Z)`, `Z^3 ⋊ SL_3(Z)`) are linear.  So the right statement is: the
theorem applies to a Kazhdan base iff that base is weakly quasidiagonal, which
for linear bases it is, and which for an infinite (T) group with no infinite
residually finite quotient it provably is not.
