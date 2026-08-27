---
rg: 2
id: free-actor-extension-fence-proof
kind: route
title: Apply soficity of every free-group action and normal-ideal decomposition
target: free-actor-extensions-cannot-host-nonce-relation
requires: []
artifacts:
  - research/artifacts/paunescu-free-action-crossed-product-audit-2026-08-21.md
---

Păunescu proves that every action of `Z` is sofic and that sofic actions are
closed under free products over the trivial amenable subgroup.  His Corollary
3.7 therefore says that **every** pmp action of `F_infinity`, and hence of every
countable free group, is sofic.  By the definition used there, its von Neumann
crossed product embeds trace-preservingly in a matrix ultraproduct, so it is
Connes embeddable.  This applies without freeness and is unchanged by adding
compact, Bernoulli, skew-product, or other pmp coordinates.

For the IRS realization, the orbit maps `g:X->X` give the normalizing
unitaries `v_g` in `L(R)`.  Covariance makes
`q_0(a u_g)=a v_g` a star homomorphism on the algebraic crossed product, and
the diagonal algebra together with these orbit normalizers weakly generates
`L(R)`.  If `q_0` extended normally to `P=L^infinity(X) rtimes F`, its kernel
would be `Pz` for a central projection `z`, and its image would be normally
isomorphic to the direct summand `P(1-z)`.  Connes embeddability passes to
central summands, so `L(R)` would be Connes embeddable.  But the Manzoor GNS
algebra embeds trace-preservingly in `L(R)` and is not Connes embeddable.
Contradiction.  Hence the quotient representation is singular.

Finally, any proposed trace-preserving inclusion of `L(R)` into the crossed
product of a diagonal/free/skew extension by `F` would put a non-CE finite
algebra inside a CE algebra, which is impossible because Connes embeddability
passes to von Neumann subalgebras.  This proves all assertions.

