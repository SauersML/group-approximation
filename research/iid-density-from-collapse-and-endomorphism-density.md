---
rg: 2
id: iid-density-from-collapse-and-endomorphism-density
kind: route
title: Finite-base total collapse and density of automorphisms among endomorphisms give dense generating i.i.d. partitions at zero supremum
target: iid-generators-dense-at-zero-rokhlin-supremum
requires:
  - bernoulli-shifts-above-rokhlin-supremum-are-isomorphic
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms
  - iid-density-iff-collapse-and-endomorphism-density
---

Let `G` be countably infinite with `h^Rok_sup(G) = 0`, and let `(K, κ)`, `(L, λ)` be finite bases with positive
entropy.

1. **Isomorphism.** `X_κ ≅ X_λ`. If `H(κ) = H(λ)`, this is `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`.
   Otherwise it is `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` with `s = 0`, applied to the smaller and
   the larger of the two entropies, both finite and positive.
2. **One shift.** DENSE(`X_λ`) is `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms`.
3. **Conclusion.** `X_κ ≅ X_λ` gives `Fac_G(X_κ, X_λ) ≠ ∅`. So item 4, (d) ⇒ (a), of
   `iid-density-iff-collapse-and-endomorphism-density` applies, and the generating partitions are dense in
   `Ind_λ(X_κ)`.

The converse also holds, by (a) ⇒ (d) of the same item: the target claim for `(κ, λ)` gives both prerequisites for
that pair.
