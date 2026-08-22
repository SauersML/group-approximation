---
rg: 2
id: central-selector-spectrum-subgroup-proof
kind: route
title: Use the marked regular corner and tensor closure of central characters
target: central-selector-spectra-cannot-prune-a-nonlinear-predicate
requires: []
---

Since `J` is a nonidentity group element, the identity coefficients give
`tau_Gamma(q_-)=1/2`.  Fourier orthogonality in the finite subgroup `D` gives
`tau_Gamma(p_chi)=1/|D|`; the equation `chi(J)=-1` gives
`q_-p_chi=p_chi`.  These identities prove `(CSP3)` and require neither
normality of `D` nor residual finiteness of `Gamma`.

If `D` is central, Schur's lemma makes it scalar in every irreducible
finite-dimensional representation, but irreducibility is not needed for the
existence set `(CSP4)`.  If `pi,rho` have characters `chi,psi`, then
`pi tensor rho` has character `chi psi`; the conjugate dual of `pi` has
character `chi^(-1)`; and the trivial representation has character one.
Thus `Sigma_fd` is a subgroup.  The fiber of the homomorphism
`chi |-> chi(J)` over `-1` is empty or a coset of its kernel, proving
`(CSP5)`.  Finally, characters of a quotient `D/K` are exactly the
annihilator of `K`, which proves the selector-collapse statement.

