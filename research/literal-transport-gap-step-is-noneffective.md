---
rg: 2
id: literal-transport-gap-step-is-noneffective
kind: claim
title: The current literal transport path has a non-effective spectral-gap gate
distinct_from:
  effective-transport-modulus: This identifies the exact missing gate in the current proof; it does not assert that no effective modulus exists.
  uniform-finite-mf-obstruction: That compactness theorem proves existence of a finite threshold; this claim audits why it does not compute one.
artifacts:
  - GroupApproximation/Sofic/WeakMFVectorGNS.lean
  - GroupApproximation/Sofic/KazhdanCornerCompression.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralP13HodgeReplay.lean
---

**ESTABLISHED BY SOURCE AUDIT.** The current finite-stage transport path does
not expose a numerical function from the forty-one relator defects to the
spectral cutoff used in Kazhdan transport.

The non-effective declaration actually called by the path is
`WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues`.
Its conclusion is an unspecified `exists N`; its proof assumes failure,
reindexes a bad eigenvector sequence, passes to `Hyperreal` standard parts,
and applies the exact Kazhdan pair only after taking that limit. The module
docstring explicitly identifies this declaration as non-effective.

`KazhdanCornerCompression.hermitianAverage_eventually_top_spectral_residual`
calls that theorem directly. Everything printed after this call is
quantitative, but only after the unknown stage `N`; therefore unfolding
`KazhdanAsymptoticCommutant.transport` or
`ManuscriptKazhdanTransport.finiteStageKazhdanTransport` cannot produce a
relator threshold.

The P13 subproblem is now quantitative.
`p13-hodge-robust-rotation-gap` combines the exact rational Hodge
coefficients, every support-product replay, every Fox-prefix replay, and the
individual rotation-substitution costs. If the eight rotation relators have
defect `delta`, it proves

```text
(gamma - 6692*delta - 599314*delta^2) * rotation_energy
  <= squared_laplacian_norm + 196350*delta^2*squared_norm,
gamma = 28329113480286/10^16.
```

This gives an explicit low/high spectral split for
`delta < 3.7381134709e-7`. Thus Hodge coefficient aggregation is no longer
the first mathematical obstruction.

Transport, however, uses the full affine base. The base gets property (T) in
`LiteralBasePropertyTBridge.lean` by an exact rotation-fixed projection and
a circumcenter of the entire translation orbit. In an approximate tuple the
P13 estimate supplies only a low rotation-spectral cluster, not an exactly
rotation-fixed subspace. The two-conjugate translation normal form uses
rotation conjugators of unbounded word length, so generator-level error
telescoping is not uniform over the translation lattice.

The loss can be written exactly. Suppose a vector \(p\) satisfies
\(\max_i\|U_i p-p\|\le\alpha\) for the six elementary-root unitaries, and let
\(R\) be a word of length \(L\) in those unitaries and their inverses.
Telescoping gives \(\|Rp-p\|\le L\alpha\). For every unitary \(V\),

\[
 \left|\|RVR^*p-p\|-\|Vp-p\|\right|\le 2L\alpha.
\tag{NT1}
\]

Indeed, with \(q=R^*p\), the first norm is \(\|Vq-q\|\), while
\(\|q-p\|=\|Rp-p\|\le L\alpha\); two applications of the triangle inequality
give (NT1).

The literal two-conjugate normal form uses

\[
 r=e_{13}^{\,m}e_{23}^{\,n},\qquad s=e_{32}^{\,k}.
\]

Their elementary-root word lengths are
\(|m|+|n|\) and \(|k|\). Even if one grants the exact translation normal-form
identity for free, its direct robustification therefore yields only

\[
 \|\rho(t)p-p\|
 \le \|\rho(v_3)p-p\|+\|\rho(v_2)p-p\|
      +2\alpha(|m|+|n|+|k|),
\tag{NT2}
\]

before any approximate-relator replay error is added. The last term is
unbounded on the translation lattice for every \(\alpha>0\). Thus the exact
circumcenter proof cannot simply replace “rotation fixed” by “in the low
rotation spectral cluster”; a new finite relative-\((T)\) estimate or a
full-base certificate is logically required.


The smallest sufficient new input is therefore either

1. a finite rational sum-of-squares certificate for the literal affine base,
   together with free-word replay areas, or
2. an explicit finite-stage relative-property-(T) theorem for the affine
   relations that converts the P13 low cluster and the nine affine relator
   defects into a full-base spectral cutoff with a numerical residual.

After that gate, a separate finite ledger is still required for compressor
transport, central spectral-corner restriction, and the marked-word estimate.
Accordingly no explicit positive defect threshold for
`effective-transport-modulus` is yet justified.

No `invalidates` entry is attached: current main has no route targeting
`effective-transport-modulus`; this node records the obstruction without
inventing a dead route.
