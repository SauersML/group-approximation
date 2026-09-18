---
rg: 2
id: twisted-field-crossed-products-untwist-into-skew-rings
kind: claim
title: Every field crossed product embeds unitally in an untwisted faithful skew group ring over the cocycle's generic splitting field, so a rank-condition witness can always be taken untwisted, faithful and simple
distinct_from:
  twisted-group-algebra-failures-are-finite-field-cover-failures: that handles trivial action and removes the cocycle by specializing to a finite field and passing to a central extension of the group; this keeps the group and the action and removes the cocycle by enlarging the coefficient field, for any action.
  field-crossed-product-rank-condition-survival-cases: that proves the rank condition in three regimes, case (c) only for alpha = 1; this is a reduction of the twisted problem to the untwisted one, and extends case (c) to cocycles that are unitary almost everywhere as a corollary.
  bernoulli-field-rank-failure-gives-rokhlin-deficit: that turns a rank failure over a Bernoulli field with alpha = 1 into a Rokhlin deficit and lists nontrivial cocycles as its first gap; this converts that gap into its second gap, non-Bernoulli invariant fields.
  virtually-biorderable-crossed-products-rank-condition: that proves the rank condition for any cocycle over virtually biorderable groups; this proves no rank condition, it moves every cocycle into the coefficient field.
  central-extension-untwisting-over-boundaries: that is about groupoid twists of finite central extensions over boundary actions; this is about 2-cocycles with values in the unit group of a coefficient field.
---

**ESTABLISHED (unreviewed)** by [[twisted-field-crossed-products-untwist-into-skew-rings-proof]].

**Setting.**
- `K` is a field, `σ: G -> Aut(K)` is an action and `α: G x G -> K^x` is a normalized 2-cocycle, so
  `α(1,h) = α(h,1) = 1` and `α(g,k) α(gk,h) = σ_g(α(k,h)) α(g,kh)`.
- `K*_α G` has `K`-basis `u_g`, with `u_g a = σ_g(a) u_g` and `u_g u_h = α(g,h) u_(gh)`.

**Theorem (generic splitting field).** Put `L = K(t_h : h ∈ G \ {1})`, purely transcendental, with `t_1 := 1`,
and let `σ_g(t_h) = α(g,h) t_(gh) t_g^(-1)`.
1. This extends `σ` to an action of `G` on `L` by field automorphisms.
2. The action on `L` is faithful whenever `G ≠ 1`, even if `σ` on `K` is trivial.
3. `φ(a u_g) = a t_g v_g` is a unital injective ring homomorphism `K*_α G -> L ⋊ G`, where `L ⋊ G` is the
   untwisted skew group ring with basis `v_g`.
4. `L ⋊ G` is simple. So for it the rank condition, weak finiteness and stable finiteness are equivalent.
5. The `t`-monomials form the lattice `Z^(G \ 1)`. The map `e_h <-> [h] - [1]` identifies it `G`-equivariantly
   with the augmentation ideal `I_G ⊂ Z[G]`. So `L = K(I_G)_α` is the `α`-twisted monomial field of `I_G`, and
   `α = ∂t` becomes a coboundary there.
   - For `α = 1`, `L` is the degree-zero subfield `K(x_h / x_1)` of the Bernoulli extension `K(x_g : g ∈ G)`.

**Corollary A (the witness can be untwisted).**
- The rank condition and stable finiteness pass to unital subrings.
- Hence: if some `K*_α G` fails the rank condition (respectively stable finiteness), then so does `L ⋊ G`. That
  ring has trivial cocycle, a faithful action, is simple, and has the same group.
- So need `f489b4fe` on `some-field-crossed-product-fails-the-rank-condition` loses nothing by assuming `α = 1`
  and a faithful action.
- The witness class "Bernoulli field with a cocycle" falls into the class "untwisted orbit field with no finitely
  generated stable subfield". For `s` of infinite order, the monomials `σ_s^n(t_h)` involve infinitely many
  distinct variables, so no `σ_s`-stable subfield containing `t_h` has finite transcendence degree over `K`. That
  puts `L` outside the local form of `finitely-generated-field-crossed-products-have-rank-condition`.
- In `bernoulli-field-rank-failure-gives-rokhlin-deficit`, gap (i) (nontrivial cocycles) becomes an instance of
  gap (ii) (non-Bernoulli invariant fields). The field in question is `L = K_m(k)(I_G)_α`.

**Corollary B (unitary cocycles in characteristic 0).** Assume:
- `char K = 0`, with `G` and `K` countable;
- `μ` is a `G`-invariant probability measure on `Emb(K, C)`;
- `|ι(α(g,h))| = 1` for `μ`-a.e. `ι` and all `g, h`.

Then `μ ⊗ Haar(T^(G \ 1))` pushes forward to a `G`-invariant probability measure on `Emb(L, C)`. So
`K*_α G` has the rank condition, and survival case (c) extends from `α = 1` to such cocycles.

**Where it stops.**
- **Point models.** A point model for `L` over a Bernoulli base (for the deficit theorem or a sofic count) has to
  choose values of the `t_h`. This needs base points off the zero and pole loci of every `α(g,h)`.
  - These are infinitely many conditions that are not translates of each other, so iid finite-field base points
    violate some of them almost surely.
  - Equivalently, the evaluated cocycle `α_ω` has to be a finitary coboundary on the Bernoulli orbit relation.
  - On hyperfinite relations this is expected, because `H^2` of an increasing union of finite relations vanishes
    by `lim^1` of the vanishing `H^1`. That case is not proved here. For nonamenable `G` it is open, and this is
    the dying step for point models.
- **No escape into a larger Bernoulli field.** For torsion-free `G`, `α` never becomes a coboundary in a
  Bernoulli extension `M = K(x_(g,i))` with free permutation of the variables.
  - `M^x = K^x ⊕ Div` as `G`-modules. The divisor module `Div` of the UFD `K[x_(g,i)]` is a permutation module
    with free orbits, since a stabilizer permutes a finite nonempty variable set and so has torsion. A free orbit
    gives an equivariant section.
  - So `H^2(G, K^x) -> H^2(G, M^x)` is split injective.
  - So the twisted problem genuinely lives in the non-Bernoulli field `K(I_G)_α`: it does not reduce to a larger
    Bernoulli field.
