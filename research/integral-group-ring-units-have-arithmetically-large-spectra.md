---
rg: 2
id: integral-group-ring-units-have-arithmetically-large-spectra
kind: claim
title: Over a group with a domain complex group algebra, a nontrivial unit u of Z[G] makes every integer Laurent polynomial of uu* have spectrum of capacity at least one
distinct_from:
  integral-spectra-of-small-capacity-are-finite: that says an integral self-adjoint matrix whose spectrum has capacity below one has finite spectrum, over every group; this applies it to integer Laurent polynomials in uu* for a unit u, and uses a domain hypothesis to turn finite spectrum into triviality of u.
  integral-operator-norm-below-two-is-quantized: that quantizes norms below two of self-adjoint integral elements; this shows a nontrivial unit and its inverse both have operator norm above two.
  promislow-integral-units-have-monomial-definite-line-shadows: that uses sum-of-squares norms on three quotients of Z[P]; this is an archimedean spectral condition in the reduced group C*-algebra, valid over every group with a domain complex group algebra.
  integral-unit-conjecture-torsion-free: that is the open conjecture that units of Z[G] are trivial for torsion-free G; this is a necessary spectral condition on any counterexample and proves no triviality.
artifacts:
  - research/artifacts/hl-promislow-positivity-2026-09-14.md
---

**ESTABLISHED** by `integral-group-ring-units-arithmetically-large-spectra-proof`.
Unreviewed. No novelty is claimed.

**Setting.** `G` is a group such that `C[G]` has no zero divisors. For
`u = sum u_g g` put `u* = sum u_g g^-1`. Norms and spectra are taken in
`C*_r(G)`.

Let `u in Z[G]` be a unit other than `+-g`. Put `v = u^-1`, `w = u u*` and
`sigma = sigma(w)`.

1. **The positive unit.** `w` is a self-adjoint positive invertible element of
   `Z[G]`, with `w^-1 = v* v in Z[G]`. Its spectrum satisfies
   `min sigma = a = ||v||^-2` and `max sigma = b = ||u||^2`.
2. **Capacity.** For every nonconstant `f in Z[x, x^-1]`, the compact set
   `f(sigma) ⊂ R` has logarithmic capacity at least `1`.
3. **Norms** (`f = x` and `f = x^-1`). `b - a >= 4` and `1/a - 1/b >= 4`.
   Hence `||u|| > 2` and `||u^-1|| > 2`.
4. **Symmetric bound** (`f = x + x^-1`). `max(a + 1/a, b + 1/b) >= 6`, so
   `max(||u||, ||u^-1||) >= 1 + sqrt 2`.

**Contrapositive form.** If some nonconstant integer Laurent polynomial maps
`sigma(u u*)` into a set of capacity below one, then `u = +-g`.

**Application to the Promislow group `P`.** `P` is torsion-free and elementary
amenable (it is virtually `Z^3`; `rational-units-rescale-to-integral-units`
records that the Kropholler--Linnell--Moody hypothesis holds for `P`). By
`elementary-amenable-torsion-free-strong-atiyah`, `C[P]` is a domain. So items
1--4 hold for every unit of `Z[P]` other than `+-g`, including every Case A unit
of `promislow-shadow-kernel-intersection-is-line-vanishing`.

**The domain hypothesis is necessary.** In `Z[C_5]` put `s = x + x^-1` and
`t = x^2 + x^-2`. Then `s t = s + t`, so `(s - 1)(t - 1) = 1` and `u = s - 1` is
a unit other than `+-g`. Its spectrum is finite, so every `f(sigma(u u*))` has
capacity `0`. Item 2 fails there, and `C[C_5]` has zero divisors.

**What this does not do.** It proves no triviality. A Case A unit of `Z[P]`
would need `sigma(u u*)` to be arithmetically large in the sense of item 2.
Nothing on main shows that this spectrum is small for Case A units. The
artifact records why the Fuglede--Kadison determinant, AM--GM and integer moment
inputs add nothing beyond item 2.

DERIVATION
[[integral-group-ring-units-arithmetically-large-spectra-proof]]
