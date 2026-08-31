---
rg: 2
id: central-projectors-overcount-regular-endpoint-payload
kind: claim
title: Central projectors overcount the residual width of regular endpoints
artifacts:
  - research/regular-plancherel-multiplicity-is-character-invisible.md
distinct_from:
  endpoint-expander-authenticates-bounded-residual-width: that authenticates a supplied irreducible endpoint factor; this proves why refining a reducible endpoint into irreducible factors can create a completely spurious unbounded residual width.
  raw-core-central-reynolds-authentication-is-circular: that concerns evaluating moving endpoint idempotents on a raw approximate core; this gives an exact zero-defect endpoint where all central idempotents exist but still do not identify the minimal tensor grouping.
  steinberg-endpoints-are-indecomposable-but-payload-width-one: that uses one irreducible Steinberg endpoint to separate raw irreducible size from payload width; this uses the full regular endpoint and quantifies the repeated-irrep ambiguity on asymptotically full rank.
---

For odd primes \(p\geq5\), put
\[
 G_p=\operatorname{PSL}_2(\mathbb F_p),\qquad
 \eta_p=\lambda_{G_p}\circ\operatorname{red}_p:
 A=\operatorname{PSL}_2(\mathbb Z[1/2])
 \longrightarrow U(\ell^2G_p).                          \tag{CPO1}
\]
The two modular-vertex restrictions of \(\eta_p\) form an exact compatible
endpoint. Hence, in the intrinsic sense of (ERW1),
\[
 w_0(\eta_p|_{V_+},\eta_p|_{V_-})=1.                    \tag{CPO2}
\]

On the other hand the central character projectors give the Plancherel
decomposition
\[
 \ell^2(G_p)
 \cong\bigoplus_{\rho\in\widehat G_p}
 V_\rho\otimes\mathbb C^{d_\rho},\qquad
 \lambda_{G_p}(g)
 \cong\bigoplus_\rho \rho(g)\otimes1_{d_\rho},           \tag{CPO3}
\]
where \(d_\rho=\dim\rho\). The projector \(z_\rho\) has normalized rank
\[
 \operatorname{tr}(z_\rho)=\frac{d_\rho^2}{|G_p|},       \tag{CPO4}
\]
but every endpoint-image moment and commutator is blind to the full
multiplicity algebra
\[
 z_\rho\eta_p(A)'z_\rho
 =1_{V_\rho}\otimes M_{d_\rho}.                          \tag{CPO5}
\]
In particular \(U(d_\rho)\) is an exact alignment ambiguity on this block,
of real dimension \(d_\rho^2\), and property \((T;FD)\) assigns zero energy
to all of it.

The smallest dimension \(m_p\) of a nontrivial complex irreducible
representation of \(G_p\) tends to infinity; indeed
\[
 m_p\geq\frac{p-1}{2}.                                   \tag{CPO6}
\]
Thus the carrier
\[
 1-z_{\mathrm{triv}}
\]
has trace \(1-|G_p|^{-1}\) and every irreducible central block inside it has
multiplicity at least \(m_p\). An authentication rule which first refines
the endpoint into irreducible character projectors and then regards their
multiplicity spaces as residual payload therefore reports width at least
\(m_p\) on asymptotically full physical rank, although the true residual
width is exactly one by (CPO2).

Consequently central idempotents, character moments, and the
property-\((T;FD)\) commutant expectation do not by themselves reconstruct
the minimal congruence endpoint factor when repeated irreducibles are
present. They locate isotypic carriers but cannot decide whether a
multiplicity algebra is intrinsic to one reducible endpoint or is an
external payload. A successful intrinsic test must also recover a global
grouping of the isotypic blocks, for example through a compatible complete
multiplication/coproduct structure, or minimize directly over reducible
endpoint representations.

This is an exact alignment countermodel to irreducible-projector
reconstruction, not a counterexample to congruence capture: (CPO1) is
already an endpoint. It supplies no nonhyperlinear group, and the root
remains open.

DERIVATION
regular-plancherel-multiplicity-is-character-invisible
