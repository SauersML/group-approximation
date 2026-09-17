---
rg: 2
id: virtually-endomorphic-self-similar-actions-have-finite-image
kind: claim
title: A self-similar action whose sections agree virtually with endomorphisms of a finite-index normal subgroup has finite image
distinct_from:
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that asks for hard finitely presented self-similar groups; this is an obstruction to one natural way of building them, where the sections are restrictions of endomorphisms, such as generator substitutions or Frobenius-type scalings.
  eventually-periodic-twisted-affine-hosts-have-polynomial-wp: that bounds the word problem of a class of affine hosts; this bounds nothing about complexity and instead shows that a different class of candidate actions, where the section maps extend to endomorphisms, cannot be faithful on an infinite group.
  char-p-untwisted-self-similar-affine-groups-are-linear: that linearizes affine hosts over elementary abelian p-groups; this is group-theoretic, needs no affine structure, and kills the actions outright rather than bounding them.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's embedding of finitely presented self-similar groups in finitely presented simple groups; this constrains which self-similar structures can feed that embedding.
---

**ESTABLISHED** by `virtually-endomorphic-self-similar-actions-finite-image-proof`.
Elementary. No novelty in the literature is claimed, and it has not been
independently reviewed.

## Statement

Let `X` be a finite alphabet and `X*` the rooted tree of words. For `g in Aut(X*)`
and `x in X`, `g|_x` is the section: `g(xw) = g(x) g|_x(w)`.

**Theorem A (sections).** Let `G <= Aut(X*)` be finitely generated and
self-similar, so `g|_x in G` for all `g in G`, `x in X`. Suppose there are:

- a normal subgroup `G' <| G` of finite index;
- a subgroup `Q_0 <= G` of finite index;
- for each `x in X`, an endomorphism `Φ_x: G' -> G'`,

such that `g|_x = Φ_x(g)` for every `g in Q_0 ∩ G' ∩ Stab_G(x)`. Then `G` is finite.

**Corollary B (virtual endomorphisms).** Let `G` be a finitely generated group,
`Q <= G` a subgroup of index `d`, and `φ: Q -> G` a homomorphism. Suppose there are
a normal subgroup `G' <| G` of finite index, a subgroup `Q_0 <= Q` of finite index
in `G`, and `Φ in End(G')` with `φ(q) = Φ(q)` for all `q in Q_0 ∩ G'`. Then the
self-similar action of `G` on the `d`-regular tree associated with `(Q, φ)` has
finite image. Explicitly, its kernel contains the fully invariant subgroup
`R_n(G')`, the intersection of all normal subgroups of `G'` of index at most
`n = [G : core_G(Q_0) ∩ core_G(Q) ∩ G']`.

The action associated with `(Q, φ)` fixes a transversal `t_1, ..., t_d` of `Q` and
sets `g·(t_i w) = t_j (φ(t_j^{-1} g t_i)·w)` where `g t_i Q = t_j Q`. It is the
Nekrashevych--Sidki action, and every transitive self-similar action arises this
way.

## Exact failing step

Any self-similar design whose section maps agree, on some finite-index subgroup,
with an endomorphism of a finite-index normal subgroup fails at one step. The
fully invariant finite-index subgroup `R_n(G')` is mapped into itself by every
section and eventually stabilizes every vertex. So it lies in the kernel, and a
faithful action forces `G` to be finite.

## What it kills

- **Substitution hosts.** Designs where the section of a generator is obtained by
  substituting generators, `s ↦ w_s`, and the substitution respects all defining
  relations. The substitution is then an endomorphism, so the associated action
  has finite image. This includes "canonical rewriting-system dynamics" where the
  tree action is read off from an endomorphism of the group being rewritten.
- **Frobenius-type scalings of the Kharlampovich--Myasnikov--Sapir groups.** These
  are the `p`-scale-invariant machines `x_u ↦ x_(ψ(u))`, `a ↦ a^p`, `a' ↦ a'^p`,
  `A_i ↦ A_i` from arXiv:1204.6506. Whenever such a map is a homomorphism on a
  finite-index normal subgroup, the associated tree action has finite image.
- **Expanding integer-matrix affine designs.** On `Z^n x| F`, a section map
  `v ↦ Mv` with `M` an integer matrix is an endomorphism of a finite-index
  normal subgroup. So it gives finite image.

The seed idea for `boone-higman-conjecture` was a universal host built from
rewriting-system dynamics. Theorem A is where it dies, whenever that host is
meant to be a finitely presented self-similar group feeding
`fp-self-similar-groups-embed-in-fp-simple-groups`.

## What survives

Only "division" sections survive: section maps that are not restrictions of any
endomorphism of any finite-index normal subgroup. Examples are:

- the adding machine `φ(2m) = m` on `Z`;
- Brunner--Sidki affine actions `v ↦ A^(-1) v` on `A Z^n`, with `|det A| > 1`;
- Cartier-type digit contractions on Laurent-polynomial modules.

For the Kharlampovich--Myasnikov--Sapir groups, their scaling units are rigid:
`a^b - 1` must map to a unit of `F_p[a^(±1), (a-1)^(-1)]`. Heuristically this leaves
only Frobenius-type maps, which are killed here, and Cartier-type maps, which are
digit contractions and plausibly finite-state. That last step is not proved here.

## Calibration

- **Extendable, finite image.** On `G = Z`, take `Q = 2Z` and `φ(2m) = 2m`, the
  restriction of the identity. The associated action on the binary tree has image
  `Z/2`, as predicted.
- **Non-extendable, faithful.** For the adding machine, `φ(2m) = m`. Any
  endomorphism of `kZ` is `x ↦ cx` with `c in Z`, while agreement with `φ` on a
  finite-index subgroup needs `c = 1/2`. So Theorem A does not apply, consistent
  with the action being faithful and infinite.
