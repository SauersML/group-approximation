---
rg: 2
id: kl-substituting-a-short-inner-word-preserves-injectivity
kind: claim
title: Substituting a nonsingular inner word of variable length at most five into an injective equation keeps it injective
distinct_from:
  kl-even-syllable-words-reduce-to-shorter-equations: that substitutes the pure power z = t^d, whose inner equation is a root adjunction; this substitutes any nonsingular inner word of variable length at most five, solved by the length-five theorems.
  kl-length-at-most-five-equations-are-solvable: that is the base theorem for short words; this is a closure property that uses it to build longer injective words out of two short ones.
---

Let `G` be any group, `v in G * <z>` with `deg_z(v) != 0`, and
`u in G * <t>` with `deg_t(u) != 0` and variable length `ell_t(u) <= 5`. Let
`w` be the image of `v` under the homomorphism
`sigma_u : G * <z> -> G * <t>` that fixes `G` and sends `z` to `u`.

If `G -> (G * <z>)/<<v>>` is injective, then `G -> (G * <t>)/<<w>>` is
injective.

Here `deg_t(w) = deg_z(v) deg_t(u) != 0`. Nothing is assumed about torsion, about
cyclic reduction of `u`, `v` or `w`, or about how much cancels in `sigma_u(v)`.

**Scope.** The bound `ell_t(u) <= 5` is used only to solve the inner equation
`u(t) = z` over an arbitrary group. The same argument works for any inner word
whose equations are solvable over every coefficient group, but only the
length-five version is claimed here.

**Use at length six.** `kl-length-six-residue-squares-and-fourth-powers-inject`
applies it with `v = z^2 c` and `v = z^4 c`. The pure-power case `u = t^d` is the
reduction lemma of `kl-even-syllable-words-reduce-to-shorter-equations`.

DERIVATION
kl-short-inner-word-substitution-proof
