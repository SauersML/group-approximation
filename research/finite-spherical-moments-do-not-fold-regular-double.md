---
rg: 2
id: finite-spherical-moments-do-not-fold-regular-double
kind: claim
title: Finite spherical moment decompositions cannot fold the regular arithmetic double
distinct_from:
  sl3-regular-double-bass-serre-rigidity-firewall: that exhibits the exact nonfolded block swap in the group factor and rules out tracial/property-T arguments; this proves the sharper finite-moment atomic quadrature fence on its spherical character decomposition.
  no-spherical-leak-in-matrix-ultraproducts: that asks to exclude a spherical leak which already extends to a regular matrix-ultraproduct representation; this shows that the spherical moments alone never provide that exclusion.
  single-hecke-average-isometry-for-lambda-central-unitaries: that asks for one matrix-origin norm equality; this explains precisely why the same equality is false at the abstract Hecke-moment level and why matrix-origin extension is load-bearing.
---

Put

```text
A=SL_3(Z[1/2]),       C=SL_3(Z),
G=SL_3(Q_2),          K=SL_3(Z_2).
```

Density and the identity `C=A intersect K` identify `A/C` with `G/K`.
The spherical Hecke algebra

```text
H=C_c(K\G/K)
```

is commutative.  On the quasi-regular cyclic module
`ell^2(A/C)=ell^2(G/K)`, let `mu_Pl` denote the joint spectral measure of
`H` at `delta_C`.  This is exactly the spherical part of the canonical
double block swap: by `sl3-double-tensor-leak-is-quasiregular`, its
coefficient is `1_C`.

Fix any selfadjoint `T_1,...,T_r in H`, any finite family of real
polynomials `f_1,...,f_q`, and `epsilon>0`.  There are points
`xi_1,...,xi_s` in the joint spectrum, with `s<=q+1`, and rational weights
`a_l/N` summing to one such that

```text
| integral f_j d mu_Pl
  - (1/N) sum_l a_l f_j(xi_l) | < epsilon             (FSM1)
```

for every `j`.

Indeed the moment vector

```text
(integral f_1 d mu_Pl,...,integral f_q d mu_Pl)
```

lies in the closed convex hull of the compact joint-spectrum image
`xi |-> (f_1(xi),...,f_q(xi))`.  Caratheodory gives a convex combination
of at most `q+1` points (after removing an affine redundancy if necessary),
and rational approximation of its weights gives `(FSM1)`.  Repeating
`xi_l` with multiplicity `a_l` realizes the right side as normalized traces
of commuting diagonal `N by N` matrices.

Consequently every fixed finite spherical-character test of the regular
block swap has finite-dimensional atomic models.  This includes any finite
list of Hecke trace moments and the squared norm of the explicit lazy Hecke
average.  At the wired pair `(3,2)`, the quasi-regular enemy value

```text
||S(k)||_2^2=43/168
```

can therefore be approximated arbitrarily closely by such finite atomic
spherical models; abstract moment positivity or character decomposition
cannot force the folded value `1`.

Property (T) does not alter this conclusion.  It isolates the trivial
spherical character and gives a uniform contraction away from it, but the
regular Plancherel state lives on the nontrivial spherical spectrum.  Finite
atomic quadrature approximates that state without moving its mass to the
trivial point.

This does not construct a canonical microstate of `A*_C A`.  The diagonal
Hecke atoms need not extend to unitaries satisfying the presentation of
`A`.  In fact exact finite-dimensional extension is precisely what
co-density forbids: a `C`-fixed vector in an exact finite-dimensional
`A`-representation is already `A`-fixed, so only the folded spherical point
can occur.  The unresolved matrix-only content is therefore the
**joint-extension gap**:

> exclude nontrivial finite spherical quadratures once the Hecke operators
> are required to arise from one approximately multiplicative,
> canonical-character matrix assignment of the full arithmetic double.

Thus a regular-specific block-swap/character decomposition does not prove
`sl3-regular-arithmetic-double-fold-mark-collapse`.  Any successful proof
must use presentation-level joint extension, not finitely many spherical
moments or their property-(T) spectral gap alone.
