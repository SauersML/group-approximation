---
rg: 2
id: dihedral-marker-involution-is-formalizable
kind: claim
title: The marker involution along the translation of the infinite dihedral group admits formalizing representatives
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that is the one-track integer marker, refuted by affine rigidity; this is the same rule over the infinite dihedral group, which is two tracks over the integers with a reflection symmetry, where affine rigidity does not apply.
  marker-involution-is-formalizable-after-regrouping: that formalizes the integer marker equivariantly only under 4Z; this asks for full dihedral equivariance, where regrouping along the normal subgroup <g^4> already gives a formalization after regrouping.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

**OPEN.** Let `D = <g, s | s^2, sgs = g^(-1)>`. On `{0,1}^D` let `tau` flip cell `h` exactly when
`(x(hg^(-3)), x(hg^(-2)), x(hg^(-1)), x(hg), x(hg^2), x(hg^3)) = (0, 0, 1, 1, 0, 0)`. Then some
polynomial representative `tau~` of `tau` satisfies `tau~ o tau~ = id` formally.

**Reformulation.** In coordinates `a(k) = x(g^k)` and `b(k) = x(g^k s)`, one-track `D`-automata are
exactly the two-track `Z`-automata whose `b`-rule is the `a`-rule reflected, with the tracks swapped.
`tau` is `tau_Z x tau_Z`, where `tau_Z` is the integer marker. So the claim asks for a reflection-symmetric
formalization of `tau_Z x tau_Z` over `Z`.

## Attempts

- **Pushforward is void.** Every bi-orderable quotient of `D` is trivial: it kills `s`, hence `g`. So
  `formal-pairs-push-along-quotients-of-the-encoder-memory-group` gives no obstruction.
- **Affine rigidity does not apply.** It needs one track, and here a top variable can cancel between the
  `a`- and `b`-components.
- **Any formalization is two-sided.** `M_2(F_2[Z])` is directly finite, so by
  `formal-polynomial-strict-pairs-need-unstable-linearization` the encoder translates are algebraically
  independent.
- **Zero-divisor gates.** For a reflection `g^i s`, the shears of
  `zero-divisor-shears-are-formal-automorphisms` add equal bits to the pairs `(a(k), b(k+i))`. They read
  only functionals of the pair sums, which they preserve. `tau_Z x tau_Z` changes pair sums at marked
  cells. Whether words for several `i`, with units of `F_2[D]`, realize it is open.
- **Regrouping.** `<g^4>` is normal of finite index, and after regrouping the object is two copies of the
  regrouped integer marker, formalizable by `marker-involution-is-formalizable-after-regrouping`. The open
  content is full `D`-equivariance.
- **Scope.** A refutation through the finite dihedral quotients `D_n` refutes this claim, but not
  `thompson-v-marker-involution-is-formalizable`. A formalization here induces one over `V`
  (`dihedral-marker-formalization-induces-to-thompson-v`).
