---
rg: 2
id: bernoulli-measures-not-finitely-determined-at-zero-supremum
kind: claim
title: On a group with zero Rokhlin supremum and a rigid free ergodic action, no nontrivial Bernoulli measure is finitely determined, so on maximally almost periodic groups a finitely determined Bernoulli measure certifies positive Rokhlin entropy
distinct_from:
  seward-bernoulli-measures-finitely-determined-under-rbs: that is Seward's theorem that Bernoulli measures are finitely determined when their Rokhlin entropy is the base entropy; this proves the opposite at zero supremum on groups with rigid free ergodic actions.
  rigid-actions-have-no-dbar-close-bernoulli-models: that is the unconditional d-bar lower bound for models of rigid actions; this combines it with weak* approximation at zero supremum to break finite determination.
---

**ESTABLISHED (unreviewed)** by [[bernoulli-measures-not-finitely-determined-at-zero-sup-proof]].

Let `G` be countably infinite with `h^Rok_sup(G) = 0`, and suppose `G` has a rigid free ergodic p.m.p. action,
as every infinite maximally almost periodic group does (`rigid-actions-have-no-dbar-close-bernoulli-models`).
Let `L` be finite and `λ` a probability vector on `L` that is not a point mass, with `c_λ = 1 − Σ_l λ(l)^2`.

**Theorem.** `λ^G` is not finitely determined in the sense of
`seward-bernoulli-measures-finitely-determined-under-rbs`. Every weak*-neighbourhood of `λ^G` contains an
ergodic, essentially free `ν ∈ M_G(L^G)` with `h_G(L^G, ν) = h_G(L^G, λ^G) = 0` and `d̄(ν, λ^G) ≥ c_λ/2`.

**Corollary (a d-bar certificate for POS).** Let `G` be an infinite maximally almost periodic group, for
instance a residually finite one. If some nontrivial finite-alphabet Bernoulli measure over `G` is finitely
determined, then `h^Rok_sup(G) > 0`, so some free ergodic action of `G` has positive Rokhlin entropy.

**Reading.**
- On such groups finite determination of `λ^G` is a dichotomy: it holds under RBS(`G`) by Seward's
  Corollary 1.6, and fails at supremum `0`. The Kun–Thom groups are residually finite, so there POS follows
  from finite determination of one Bernoulli measure. At supremum `0` the entropy condition in the definition
  is automatic, so finite determination there would say that `d̄` is weak*-continuous at `λ^G`.
- For `zero-rokhlin-supremum-forces-bernoulli-collapse`: an Ornstein-type proof that copies processes through
  finite determination cannot compare all essentially free measures of zero Rokhlin entropy. It must restrict
  to a class that excludes models of rigid actions, for example models of mixing actions or of Bernoulli
  shifts. The density question `iid-generators-dense-at-zero-rokhlin-supremum` is not affected.
- Under RBS the same argument gives: a rigid free ergodic action whose Rokhlin entropy equals `H(λ)` has no
  shift models in some weak*-neighbourhood of `λ^G`. Whether rigid free actions of positive Rokhlin entropy
  exist is not recorded here.
- Simple hosts (the binary Leavitt units, Thompson's `V`, the tester host) are not maximally almost periodic.
  The theorem applies to them only through a rigid free ergodic action, which is not recorded for them.
