---
rg: 2
id: finite-phase-pauli-basis-dilation-is-a-twisted-group-factor-compiler
kind: claim
title: A finite-phase Pauli-basis dilation is a twisted group-factor compiler, not a free hyperfinite dilation
distinct_from:
  group-basis-actions-have-permutation-koopman-spectrum: that gives the necessary Koopman condition for a strict equivariant embedding into an untwisted group basis; this includes finite projective phases, proves the crossed-product compiler, and identifies the unrestricted existence statement with the nonhyperlinear-group problem.
  unrestricted-algebraic-envelope-equals-nonhyperlinearity: that treats compact abelian Haar bases by Pontryagin duality; this treats nonabelian Pauli/unitary-error bases and finite scalar cocycles.
  full-shared-pauli-rows-have-an-exact-finite-tracial-model: that identifies one canonical Pauli crossed product but does not turn it into a discrete group factor; this states exactly what extra invariant-basis dilation would be required and why it is not formal.
---

A **finite-phase Pauli-basis dilation** of a trace-preserving action
`alpha:G action M` consists of:

1. an equivariant trace-preserving embedding `Phi:M->L_omega(K)`, where
   `K` is countable, `L_omega(K)` is hyperfinite, and the cocycle `omega`
   takes values in one finite cyclic group `mu_m`;
2. an action `theta:G action K` and finite phases `c(g,k) in mu_m` such
   that the dilated action `beta` satisfies

   ~~~text
   beta_g(v_k)=c(g,k)v_(theta_g(k))                       (PBD1)
   ~~~

   on the canonical projective unitary basis; and
3. either strict equivariance, or a specified cocycle conjugacy/corner
   inclusion which embeds `M crossed_product_alpha G` trace preservingly in
   `L_omega(K) crossed_product_beta G`.

Then

~~~text
L_omega(K) crossed_product_beta G
  isomorphic to L_Omega(K semidirect_theta G),            (PBD2)
~~~

for an explicit `mu_m`-valued cocycle `Omega`.  A finite central extension

~~~text
1 -> mu_m -> Gamma_hat -> K semidirect G -> 1             (PBD3)
~~~

has a positive central-character corner isomorphic to the algebra in
(PBD2).  Consequently, if `M crossed_product G` is not Connes embeddable,
`Gamma_hat` is a countable nonhyperlinear group.

The unrestricted existence statement is exactly circular:

~~~text
some non-CE action admits a finite-phase Pauli-basis dilation
iff
a countable nonhyperlinear group exists.                  (PBD4)
~~~

For the reverse implication take the standard countable tensor-Pauli index
`K=direct_sum_N(F_2^2)` with its symplectic sign cocycle, so
`L_omega(K)=tensor_N M_2=R`, and let a nonhyperlinear group act trivially on
that projective basis.

A strict dilation also has a concrete obstruction.  Its Koopman
representation must be a subrepresentation of a countable finite-phase
monomial representation.  This is not automatic even for sofic actions.
Inside `R` choose irrational-rotation unitaries `U,V` with

~~~text
UV=exp(2 pi i theta)VU,             theta irrational,
~~~

and let `Z` act by `Ad U`.  The vector `V` has a non-torsion Koopman
eigenvalue.  A finite-phase monomial `Z`-representation has only
root-of-unity eigenvalues, so no strict Pauli-basis dilation exists.  The
actor is amenable and the crossed product is Connes embeddable; in the usual
pmp approximation setting amenable actions are sofic.  Thus sofic/CE
approximability does not imply strict basis dilation.

Unrestricted cocycle conjugacy erases this particular example because an
inner action is cocycle conjugate to the trivial action.  For amenable
actors, Ocneanu's classification supplies broad cocycle-conjugacy
standardization on the hyperfinite factor, but all resulting crossed
products are Connes embeddable.  No analogous universal algebraization
theorem is available for nonamenable actors.

The precise sofic equivalence occurs only after one additionally asks for
finite **charts** of the permuted basis: in the Pauli lamp setting,
basis charts recover the underlying set-action charts, while a sofic set
action constructs the Pauli charts.  Exact basis preservation alone does not
imply soficity either: the Pauli Bernoulli action attached to the pinned
Kun--Thom nonsofic set action permutes its countable Pauli-word basis exactly.
What is unavailable is a finite common chart.  Thus exact dilation and
soficity are not equivalent in either direction.

Therefore a basis-preserving dilation of a pinned non-CE action would indeed
solve the root problem, but proving it is already a source-specific
groupification theorem.  The global target remains **OPEN**.

DERIVATION
finite-phase-basis-crossed-product-and-circularity-proof
