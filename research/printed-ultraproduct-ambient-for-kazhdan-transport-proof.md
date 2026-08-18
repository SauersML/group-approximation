---
rg: 2
id: printed-ultraproduct-ambient-for-kazhdan-transport-proof
kind: route
title: The Hilbert ultraproduct carries the norm-ultraproduct action faithfully
target: printed-ultraproduct-ambient-for-kazhdan-transport
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/UltraproductAdjointAmbient.lean
  - GroupApproximation/Sofic/UltraproductModelConstructionAssembly.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
  - GroupApproximation/Sofic/KOmegaHilbert.lean
  - GroupApproximation/Sofic/OmegaOperatorUltraproduct.lean
  - GroupApproximation/Sofic/HilbertUltraproductSeparating.lean
  - GroupApproximation/Sofic/OmegaWeightedAmbient.lean
---

# Direct construction of KT.02--KT.04

Fix a free ultrafilter `omega` and Hilbert spaces
`K_n=L^2(M_(d_n)(C),tr_(d_n))`.  Everything the printed proof asks for is a
standard Banach/Hilbert ultraproduct construction; no operator-algebraic
existence theorem is needed.

## 1. The Hilbert-space ultraproduct

Let

```text
ell_infty(K_n) = { xi=(xi_n) : sup_n ||xi_n|| < infinity }
N_omega        = { xi : lim_omega ||xi_n|| = 0 }.
```

`N_omega` is a closed linear subspace.  Put

```text
K_omega = ell_infty(K_n) / N_omega,
< [xi_n], [eta_n] > = lim_omega <xi_n,eta_n>.
```

The scalar ultralimit exists because the inner-product sequence is bounded.
Cauchy--Schwarz shows the formula is independent of representatives and
positive definite modulo `N_omega`; in particular

```text
||[xi_n]|| = lim_omega ||xi_n||,
[xi_n]=[eta_n]  <=>  lim_omega ||xi_n-eta_n||=0.                 (KT.02)
```

Completeness is automatic: `ell_infty(K_n)` is a Banach space and
`N_omega` is closed, hence the quotient is Banach.  The displayed inner
product induces its quotient norm (equivalently the parallelogram law passes
to the quotient), so the Banach quotient is a Hilbert space.

## 2. Coordinate operators descend

For a uniformly bounded family `T=(T_n)` with `T_n in B(K_n)`, define

```text
rho(T)[xi_n] = [T_n xi_n].
```

If `[xi_n]=0`, then

```text
||T_n xi_n|| <= (sup_n ||T_n||) ||xi_n|| ->_omega 0,
```

so the action is well-defined.  It is plainly linear, multiplicative,
*-preserving and unital, and

```text
||rho(T)|| <= lim_omega ||T_n||.
```

If `||T_n|| ->_omega 0`, the induced operator is zero.  Hence `rho` factors
through the norm ultraproduct

```text
B_omega = prod_omega B(K_n).
```

This gives the multiplicative action required in KT.03/KT.04.

## 3. The action is faithful (indeed isometric)

Let `a=[T_n] in B_omega` and write
`c=lim_omega ||T_n||`, the quotient norm.  For each `n` choose a unit vector
`xi_n` with

```text
||T_n xi_n|| >= ||T_n|| - 1/n
```

(exact norm-attainment is available here because every `K_n` is finite
dimensional, but an approximate maximizer would suffice).  Then
`xi=[xi_n]` is a unit vector in `K_omega` and

```text
||rho(a) xi|| = lim_omega ||T_n xi_n|| = c.
```

Thus `||rho(a)||>=c`; together with the previous inequality,
`||rho(a)||=c`.  So `rho` is isometric and in particular faithful.

Consequently algebraic identities read from the Hilbert-space action descend
back to `B_omega`.  In particular, for projections `P,Q`, range inclusion
`Ran(P) subset Ran(Q)` is equivalent on a Hilbert space to `QP=P`; taking
adjoints also gives `PQ=P`.  Faithfulness turns those operator identities
into the identities in `B_omega` used by the printed absorption argument.
This is exactly the KT.04 read-back demanded by the claim.

## 4. Match to the matrix adjoint model

For the manuscript's coordinates, `Ad(U_n)` acts unitarily on `K_n` because
left and right multiplication by a unitary preserve normalized
Hilbert--Schmidt norm.  Hence the already-defined coordinate family
`Ad(U_n(g))` gives an element of `B_omega`, and its action under `rho` is
literally

```text
[x_n] |-> [U_n(g) x_n U_n(g)^*].
```

Operator-norm asymptotic multiplicativity of the `U_n` makes these classes a
genuine representation in the ultraproduct, exactly as in the repository's
KT.01/KT.05 calculations.

Therefore the ambient package whose existence was left open in the printed
route exists for every free ultrafilter.  This establishes
[[printed-ultraproduct-ambient-for-kazhdan-transport]].  It does not replace
the repository's finite-stage proof of Kazhdan transport; it repairs the
separate ultraproduct proof printed in the manuscript.

## Machine-checked form

The argument above is also formalized, section by section, so this route is not
carried by its prose alone.  All five modules named below are in the root
import closure, so they are covered by `lake build` and the kernel audit.

1. **Section 1, the Hilbert-space ultraproduct.**  `KOmegaHilbert.KOmega` is
   the quotient of uniformly mass-bounded matrix families by `omega`-null
   families, carrying the descended inner product
   (`kOmegaInnerProductSpace`).  Positive definiteness is proved, not assumed:
   `HilbertUltraproductSpace.uinner_self_eq_zero_iff` identifies the null space
   of the form with the quotient's denominator.  At the dimension weight,
   `UltraproductModelConstruction.weightNull_dimWeight_iff_tendsto` is the
   `KT.02` criterion itself — class equality is exactly normalized
   Hilbert--Schmidt convergence to zero along `omega`.
2. **Section 2, the norm ultraproduct and its action.**
   `OmegaOperatorUltraproduct.OmegaAdjointCorona Y omega` is the norm quotient
   along the ultrafilter, a complete complex C-star algebra, with
   `norm_omegaMk` identifying its quotient norm with the `omega`-limit of the
   coordinate operator norms; `omegaAct` is its multiplicative linear action on
   the vector ultraproduct.
3. **Section 3, faithfulness and the absorption dictionary.**  The separating
   lemma `HilbertUltraproductSeparating.actQ_eq_zero_iff_tendsto` says an
   operator family acts as zero exactly when its norms are `omega`-null, whence
   `OmegaOperatorUltraproduct.omegaAct_injective`.  For idempotents,
   `range_le_iff_mul_eq` is the range-inclusion/absorption equivalence
   `q * p = p`, and the same fact at adjoints gives the two-sided form the
   printed absorption argument uses.
4. **Section 4, the bundled ambient.**
   `UltraproductModelConstruction.nonempty_ultraproductAdjointModel` and its
   choice form `.ultraproductAdjointModel`
   (`Sofic/UltraproductModelConstructionAssembly.lean`) inhabit
   `UltraproductAdjointModel iota s d U omega` under exactly the transport
   hypotheses — property (T) of `Gamma`, `s iota(Gamma) s^-1 <= iota(Gamma)`,
   `0 < d n`, operator-norm asymptotic multiplicativity of `U` — and
   `OmegaWeightedAmbient.omegaWeightedAmbient` assembles the `omega`-corona
   route the current printed proof runs on.  `manuscriptKazhdanTransport`
   (`Sofic/ManuscriptKazhdanTransport.lean`) then states the manuscript's
   `thm:kazhdan-transport` with no ambient hypothesis and discharges it with
   the constructor, so the printed theorem is unconditional.

One honest gap in the correspondence, and it is inert: no `CompleteSpace`
instance is constructed for the synonym `KOmega`.  Completeness is not a field
of `UltraproductAdjointModel` and is not used anywhere in the printed transport
chain, so the prose argument's completeness paragraph is a convenience of the
hand construction rather than something the formalization owes.
