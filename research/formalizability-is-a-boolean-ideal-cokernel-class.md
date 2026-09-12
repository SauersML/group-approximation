---
rg: 2
id: formalizability-is-a-boolean-ideal-cokernel-class
kind: claim
title: Formalizability of a binary left-inverse pair is vanishing of a class in the cokernel of the encoder lift on the Boolean ideal
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asks whether every left-invertible binary pair is formalizable; this identifies formalizability, for a fixed encoder representative, with vanishing of one explicit linear-algebra class, and does not decide whether it vanishes.
  formal-polynomial-strict-pairs-need-unstable-linearization: that shows a formal pair is bijective under direct finiteness; this reduces the prior question of making a pair formal to a single linear equation over the Boolean ideal.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that shows the canonical multilinear Jacobian defect is not an invariant of the automata; this gives the representative-independent invariant that governs formalizability instead.
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
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
identity) if and only if the linear equations `hat tau^*(delta_h) = eps_h` are
solvable with `delta_h in I`. Equivalently the class `[eps]` vanishes in
`coker(hat tau^*|_I)`. The class depends only on the functions `tau, sigma` once
`hat tau^*` is fixed, and it is `0` for every sitewise pair. So
`binary-left-inverse-pairs-are-formalizable` holds iff for every left-invertible
binary pair some encoder representative has `[eps] = 0`.

## Attempts

- **Proved,** by `formalizability-boolean-ideal-cokernel-proof`: the exactness of the
  correction (an algebra map is fixed by its generator values, so correcting the
  decoder by `delta_h in I` adds exactly `hat tau^*(delta_h)`, with no higher terms);
  representative independence on the decoder side; and the sitewise vanishing, where
  `hat tau^*` is an automorphism of `R`.
- **Open:** whether the class vanishes in general. By this reduction a
  counterexample is a left-invertible pair whose class stays nonzero under every
  encoder representative. On a host with `M_n(F_2[G])` directly finite the constant
  slice of the leading part is a split epimorphism
  (`formalizability-conormal-obstruction-is-jacobian-cokernel`), so a witness must
  live in the higher `I`-adic layers.
- **Where it stops:** independence of the class from the encoder representative is
  not settled; a different encoder lift changes both `hat tau^*|_I` and `eps`.
