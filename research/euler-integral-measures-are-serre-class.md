---
rg: 2
id: euler-integral-measures-are-serre-class
kind: claim
title: A measure whose integral polynomial images all have integer moment Euler products obeys every Serre inequality
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that derives the Serre inequalities from approximation by integer matrices; this asks whether exact arithmetic integrality of the moment zeta series suffices, with no approximation
  serre-class-measures-are-integral-spectral-limits: that is the converse realization question for Serre-class measures; this is a sufficient arithmetic criterion for membership in the class
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes the finitely atomic members of the Serre class; this concerns measures with continuous parts, which is where the question is open
---

**OPEN.** Let `mu` be a finite positive Borel measure on a compact real interval.
Suppose that for every `Q in Z[x]` the moments `m_j(Q) = integral Q^j d mu` are
integers and

```text
exp( sum_(j>=1) m_j(Q) z^j / j )  in  Z[[z]].
```

Then `integral_(Q != 0) log |Q| d mu >= 0` for every nonzero `Q in Z[x]`.

**Why it matters.** Over a torsion-free group every self-adjoint integral
matrix `T` has all these properties: each `Q(T)` is integral, so
`torsion-free-integral-zeta-is-an-integer-euler-product` applies to it. With
`determinant-conjecture-iff-serre-class-spectra`, this claim would prove Lück's
determinant conjecture for every torsion-free group, nonsofic ones included.
The statement mentions no group. See
`master-host-determinant-via-euler-integrality`.

## Attempts

- **Support of length below `4`.** Holds, and `mu` is integer-atomic. The proof
  of `torsion-free-small-spread-integer-atomic-proof` uses only the
  integrality of the series for `mu` itself (`Q = x`) and the bounded support,
  so it applies verbatim.
- **Finitely atomic `mu`.** Expected to hold. Sketch, not written as a proof
  node: the Frobenius congruences `m_(pj) == m_j (mod p)`, together with
  Chebotarev density applied to `lambda^p == Frob(lambda) (mod p)`, force
  Galois-equal masses. Then `atomic-serre-measures-are-equal-weight-real-orbits`
  applies. Over groups this case is already
  `finite-spectrum-integral-elements-obey-determinant`.
- **Examples.**
  - The Fibonacci measure of `integer-moment-measure-with-negative-log-determinant`
    fails integrality at `p = 2`.
  - `(1/2) arcsine[-2,2] + (1/2) delta_0` has integer moments, but its series is
    the square root of the Catalan series, which is not integral.
  - Spectra over `Z^d` and over free groups satisfy both the hypothesis and the
    conclusion.
- **Capacity at least `1`.** Open. Pólya's theorem is silent here; integral
  series can be transcendental, such as the Catalan series of `g + g^(-1)`.
  What is needed is an arithmetic bound on the logarithmic potential of `mu` at
  algebraic integers, derived from integrality of `F(w) = exp(-integral log(w-x) d mu)`
  at infinity. Arithmetic capacity theory (Fekete--Szegő, Cantor,
  Chambert-Loir--Noûs arXiv:2305.17210) is the natural toolbox. No such bound
  is known here.
- **Weak limits.** Do not help: the Serre class is weakly closed, but exact
  congruences do not survive weak limits.
