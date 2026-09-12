---
rg: 2
id: formalizability-is-a-boolean-ideal-cokernel-class
kind: claim
title: Formalizability of a binary left-inverse pair is vanishing of a class in the cokernel of the encoder lift on the Boolean ideal
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asked whether every left-invertible binary pair is formalizable, and is refuted; this identifies formalizability, for a fixed encoder representative, with vanishing of one explicit linear-algebra class.
  binary-left-inverse-pairs-need-not-be-formalizable: that exhibits a pair with no formalizing representatives; this reformulates formalizability as a cokernel class, which for that pair is nonzero for every encoder representative.
  formal-polynomial-strict-pairs-need-unstable-linearization: that shows a formal pair is bijective under direct finiteness; this reduces the prior question of making a pair formal to a single linear equation over the Boolean ideal.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that shows the canonical multilinear Jacobian defect is not an invariant of the automata; this gives the representative-independent class that governs formalizability instead.
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be any group, `A = F_2^n`, `R = F_2[X_h : h in G x {1..n}]`, `I` the Boolean
ideal `(X_h^2 + X_h)`, and `B = R/I` the algebra of finite-memory functions
`A^G -> F_2`. A representative of a cellular rule is a `G`-equivariant finite-memory
`F_2`-algebra lift `hat tau^* : R -> R` of `tau^* : B -> B`, and every lift satisfies
`hat tau^*(I) subseteq I`.

Let `tau, sigma` be cellular automata on `A^G` with `sigma o tau = id`. Fix a lift
`hat tau^*` and any lift `hat sigma_0^*`, and write
`hat tau^* hat sigma_0^*(X_h) = X_h + eps_h` with `eps_h in I`.

**Claim.** The pair is *formalizable with this encoder representative* (there are lifts
with `hat tau^* hat sigma^* = id_R`, i.e. `sigma o tau = id` as a formal polynomial
identity) iff the linear equations `hat tau^*(delta_h) = eps_h` are solvable with
finite-memory equivariant `delta_h in I`. Equivalently the class `[eps]` vanishes in
`coker(hat tau^*|_I)`. The class depends only on the functions `tau, sigma` once
`hat tau^*` is fixed, and it is `0` for every sitewise pair.

`binary-left-inverse-pairs-are-formalizable` asked that every left-invertible binary pair
have some encoder representative with `[eps] = 0`. Its refutation
`binary-left-inverse-pairs-need-not-be-formalizable` is, in these terms, a bijective pair
over `Z` whose class is nonzero for every encoder representative.

## Attempts

- **Proved,** by `formalizability-is-a-boolean-ideal-cokernel-class-proof`: the correction
  is exact (an algebra map is fixed by its generator values, so correcting the decoder by
  `delta_h in I` adds exactly `hat tau^*(delta_h)`); decoder-side independence; sitewise
  vanishing, where `hat tau^*` is an automorphism of `R`.
- **Nonvanishing, decided elsewhere:** the marker involution of
  `binary-left-inverse-pairs-need-not-be-formalizable` has `[eps] != 0` for every encoder
  representative (gk-fz-bennett, cf99b38215).
- **Encoder dependence:** the leading part of the class can always be killed by choosing
  the encoder representative (Lemma C,
  `formalizability-conormal-obstruction-is-jacobian-cokernel`). With such a
  representative every graded layer vanishes, and the obstruction is exactly termination
  (`binary-left-inverse-pairs-are-boolean-adically-formalizable`).
- **Where it stops:** no invariant is known that measures non-termination directly.
