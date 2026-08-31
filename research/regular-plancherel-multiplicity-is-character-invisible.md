---
rg: 2
id: regular-plancherel-multiplicity-is-character-invisible
kind: route
title: Compare regular Plancherel multiplicity with intrinsic endpoint width
target: central-projectors-overcount-regular-endpoint-payload
requires:
  - endpoint-expander-authenticates-bounded-residual-width
  - steinberg-endpoints-are-indecomposable-but-payload-width-one
---

# The whole regular block is one endpoint factor

Because \(p\) is odd, reduction modulo \(p\) is defined on
\(\mathbb Z[1/2]\). Composing it with the left regular representation of
\(G_p\) gives the exact representation (CPO1) of \(A\). Its restrictions to
the two modular vertices agree on the Iwahori edge by functoriality; no
repair or choice of an edge intertwiner is involved. In the tensor hull take
the payload to be the one-dimensional trivial pair and take the endpoint
factor to be \(\eta_p\) itself. This proves (CPO2).

# Character projectors see atoms but not their endpoint grouping

Finite-group Fourier decomposition gives
\[
 \mathbb C[G_p]
 \cong\bigoplus_{\rho\in\widehat G_p}
 \operatorname{End}(V_\rho)
 \cong\bigoplus_\rho V_\rho\otimes V_\rho^*.             \tag{1}
\]
Left translation acts as \(\rho\otimes1_{V_\rho^*}\). Thus the multiplicity
of \(\rho\) is \(d_\rho\), proving (CPO3). The standard central idempotent
\[
 z_\rho=
 \frac{d_\rho}{|G_p|}
 \sum_{g\in G_p}\overline{\chi_\rho(g)}\,\lambda(g)       \tag{2}
\]
is the identity on the summand
\(V_\rho\otimes V_\rho^*\) and zero on every other summand. Its rank is
\(d_\rho^2\), which proves (CPO4).

Schur's lemma on each summand gives
\[
 \{\rho(G_p)\otimes1\}'
 =1\otimes\operatorname{End}(V_\rho^*).                  \tag{3}
\]
Since reduction of \(A\) is onto \(G_p\), (3) is exactly (CPO5). Conjugating
the multiplicity coordinate by any unitary in \(U(d_\rho)\) leaves every
endpoint matrix, every character value, and every central idempotent
unchanged. In the adjoint representation used by property \((T;FD)\), (3)
is the invariant subspace itself. The Kazhdan inequality controls the
orthogonal complement of (3) and is identically zero on (3); it cannot
select a basis, a tensor grouping, or a smaller algebra inside that fixed
space.

# The false residual width diverges on full rank

The ordinary complex character table of
\(\operatorname{PSL}_2(\mathbb F_p)\), equivalently the rank-one case of
the Landazuri--Seitz minimum-degree bound, gives
\[
 \dim\rho\geq(p-1)/2                                     \tag{4}
\]
for every nontrivial irreducible \(\rho\) when \(p\geq5\). The trivial
summand of the regular representation has rank one. Therefore all but
normalized rank \(1/|G_p|\) is a sum of central blocks whose multiplicity
spaces have dimensions at least \((p-1)/2\).

If one insists on feeding the irreducible factors in (CPO3) separately into
the expectation argument of
**endpoint-expander-authenticates-bounded-residual-width**, the factor
\(V_\rho^*\) is placed on the residual side and has dimension \(d_\rho\).
Equation (4) makes this apparent residual width diverge on asymptotically
all rank. But the unfissioned representation \(\eta_p\) was already one
legal reducible congruence endpoint with a one-dimensional payload. This
proves that the divergence is entirely an artifact of the central
refinement.

The countermodel is exact, so adding more accurate character moments or a
larger Kazhdan set does not reduce the ambiguity. What is absent from the
central data is the global decision to group all Plancherel atoms into the
single regular endpoint representation. Recovering that grouping requires
structure beyond isotypic projectors and their commutant gaps.
