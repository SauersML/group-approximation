---
rg: 2
id: xl-groupoid-action-amenable-iff-semidirect-amenable
kind: claim
title: An action by groupoid automorphisms on an amenable groupoid algebra is amenable iff the semidirect groupoid is amenable
distinct_from:
  xl-commuting-minimal-action-gives-classifiable-witness: that is the special case G = G x Gamma acting on X x Gamma with Gamma commuting; here G may normalize the groupoid in any way (twisted Gamma x| G, partial class permutations), and the criterion is an equivalence, not only a sufficient condition.
  xl-invariant-af-relation-gives-amenable-af-witness: that needs every compact open R_n to be G-invariant; here G only has to act by automorphisms of the whole groupoid, which evades that node's boundary obstruction.
---

Let `G` be a countable group and let `H` be a second countable, locally
compact, Hausdorff étale groupoid with compact unit space `X`.  Let `G` act on
`H` by groupoid automorphisms `g : H -> H` (homeomorphisms respecting range,
source and multiplication), and let `alpha_g(f) = f o g^-1` on `C_c(H)`, which
extends to an action `alpha : G acts on A = C*_r(H)` preserving `C(X)`.
Let `H x| G` be the semidirect product groupoid (arrows `(eta, g)`,
`s(eta, g) = g^-1 s(eta)`, `r(eta, g) = r(eta)`,
`(eta, g)(zeta, k) = (eta g(zeta), gk)`).  Suppose `H` is amenable.  Then

```text
alpha is an amenable action   <=>   H x| G is (topologically) amenable.
```

`(<=)` Push a Reiter net of `H x| G` forward along the homomorphism
`c(eta, g) = g`.  This gives continuous `n : X -> Prob(G)`, finitely supported
in one finite set, that are uniformly almost `G`-equivariant **and** uniformly
almost invariant along each compact subset of `H`.  Then `xi(h) = n(.)(h)^{1/2}`
is a quasi-central approximation net for `alpha`, whence `alpha` is amenable
(Buss--Echterhoff--Willett).  `(=>)` `A x|_r G = C*_r(H x| G)` is nuclear, and a
second countable étale groupoid with nuclear reduced algebra is amenable
(Anantharaman-Delaroche--Renault; Brown--Ozawa Thm 5.6.18).

**Consequence for Problem XL.**  `G` satisfies XL as soon as

> **(GSA_G)** some amenable, minimal, effective étale groupoid `H` on a compact
> metrizable space, with `C*_r(H)` unital, simple, stably finite and
> classifiable, carries an action of `G` by groupoid automorphisms with
> `H x| G` amenable.

Conversely every XL witness for `G` that has a `G`-invariant Cartan subalgebra
with trivial twist, on which `G` acts through Weyl groupoid automorphisms,
arises this way (Renault's reconstruction).  So (GSA_G) is exactly XL
restricted to such Cartan-preserving witnesses.  `H x| G` amenable forces the
restriction `X x| G` amenable, i.e. `X` is an amenable `G`-space; in general it is a further
condition on how `G` normalizes `H`: for `H = X x| Gamma` with `Gamma` an amenable normal
subgroup of a split extension `Gamma x| G` acting on `X`, it says
`Gamma x| G` acts amenably on `X`.

**Scope of the known obstructions.**  The boundary kills of
`xl-commuting-minimal-action-forbids-proximal-factors` and
`xl-invariant-af-relation-gives-amenable-af-witness` use that `G` commutes with
`H` or preserves a compact open exhaustion of `H`: in those two settings the proximality argument shows that every `G`-map
`phi : X -> P(B)` into a strongly proximal flow is `H`-invariant, hence
constant by minimality.  For a general
automorphism action only the `H`-invariant `G`-maps are excluded (by minimality
of `H`), and a `G`-factor map `X -> B` onto a boundary is not excluded by that
argument.  The surviving class is automorphism actions that do not commute
with, nor preserve any compact open exhaustion of, `H`.
