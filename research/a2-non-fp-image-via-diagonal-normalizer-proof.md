---
rg: 2
id: a2-non-fp-image-via-diagonal-normalizer-proof
kind: route
title: Normalize a twisted Brin-Thompson clopen action by a diagonal Thompson group and quotient out the actor
target: a2-action-with-non-finitely-presented-image
requires:
  - twisted-brin-thompson-finite-presentation-criterion
  - twisted-btb-clopen-action-is-type-a
  - normalizer-extension-of-type-a-actor-is-a2-cover
  - abstract-btb-simple-quotient-fp-gate
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

Brick notation is that of `twisted-btb-clopen-action-is-type-a`. The coordinate
set is `S = Ω_C`, the coordinate actor is `G = V` acting on `S`, and
`Γ = SV_G`. The diagonal elements use a second, independent copy of `V`,
written with letter `w`.

**(1) The actor.** With one coordinate and the trivial actor, the brick calculus
gives exactly Thompson's group: bricks are cones and branches are prefix
replacements. The trivial group acts faithfully on a point with type (A). So
`twisted-btb-clopen-action-is-type-a`, applied to that one-point action, shows
that `V` acts on `S = Ω_C` with type (A). The same conclusion is
`fp-full-binary-cantor-groups-have-type-a-actions` with `D = V`. `S` is
infinite. By `twisted-brin-thompson-finite-presentation-criterion`,
`Γ` is finitely presented. By `twisted-btb-clopen-action-is-type-a`, `Γ` acts on
`Ω` with type (A) and is transitive on `Ω`.

**(2) Diagonal elements normalize Γ.** Fix `w in V` and a branch
`f = h_q τ_g h_p^-1` on `B(p)`. For `κ in δ_w(B(p))`,

```text
(δ_w f δ_w^-1 κ)(s) = φ_(g^-1 s)( κ(g^-1 s) ),
φ_t(c) = w( q(gt) · strip_(p(t)) ( w^-1 c ) ),   c in w([p(t)]).
```

If `t` is outside the finite set `F = supp p ∪ g^-1 supp q`, then `φ_t` is the
identity of `C`. For `t in F`, `φ_t` maps the clopen set `w([p(t)])` onto
`w([q(gt)])`. It is a composite of finitely many piecewise prefix replacements,
so there are cone partitions `[a_(t,j)]` of its source and `[b_(t,j)]` of its
target with `φ_t(a_(t,j) z) = b_(t,j) z`.

For a choice `j = (j_t)_(t in F)`, let `u_j(t) = a_(t,j_t)` for `t in F`, and
let `v_j(gt) = b_(t,j_t)`, both empty elsewhere. On the brick `B(u_j)` the
conjugate equals `h_(v_j) τ_g h_(u_j)^-1`. These bricks partition
`δ_w(B(p))`. Doing this for every branch of `f` gives finite brick partitions
of `C^S`, since `δ_w` is a homeomorphism. So `δ_w f δ_w^-1 in Γ`.

`δ : V -> Homeo(C^S)` is an injective homomorphism.

**(3) Diagonal elements miss Γ.** Suppose `δ_w in Γ` and take a branch
`h_q τ_g h_p^-1` of it on `B(p)`. `S` is infinite, so choose `s` outside the
finite set `supp p ∪ g(supp p) ∪ supp q ∪ g^-1(supp p)`. For `κ in B(p)`, the
branch gives `κ(g^-1 s)` at coordinate `s`, while `δ_w` gives `w(κ(s))`.
- **Case `g^-1 s != s`.** The coordinates `κ(s)` and `κ(g^-1 s)` range
  independently over `C` on `B(p)`, which contradicts
  `w(κ(s)) = κ(g^-1 s)`.
- **Case `g^-1 s = s`.** Then `w(c) = c` for all `c`, so `w = 1`.

Hence `δ(V) ∩ Γ = 1`.

**(4) `Z wr Z` in `F <= V`.** Use the piecewise-linear model of `F` on `[0,1]`.
- **The shift.** The generator `t = x_0` is `x/2` on `[0,1/2]`, `x - 1/4` on
  `[1/2,3/4]`, and `2x-1` on `[3/4,1]`. It satisfies `t(x) < x` on `(0,1)`, and
  the intervals `t^k([1/4,1/2))`, `k in Z`, partition `(0,1)`.
- **The lamp.** Let `λ(x) = 1/4 + x/4`. Then `b = λ x_0 λ^-1`, extended by the
  identity, lies in `F` and is supported in `[1/4,1/2]`.
- **The base group.** The conjugates `t^k b t^-k` have pairwise disjoint open
  supports, so they commute. Each has infinite order, since `F` is torsion
  free. A finite product of their powers is trivial only if every exponent is
  0. So they generate `B ≅ ⊕_Z Z`.
- **The wreath product.** Every element of `B` is the identity on all but
  finitely many `t^k([1/4,1/2))`, while `t^m` for `m != 0` fixes no point of
  `(0,1)`. So `<t> ∩ B = 1`, and `<b, t> = B x| <t> ≅ Z wr Z`.

`F` embeds in `V` in the standard way (Cannon--Floyd--Parry).

**(5) The [A_2] cover.** Put `Q = δ(<b,t>)`. By (2), `Q` normalizes `Γ`, and by
(3), `Q ∩ Γ = 1`. By `normalizer-extension-of-type-a-actor-is-a2-cover` with
`m = 2`:
- `G~ = Γ x| F_2` acts on `Ω` with type `[A_2]`;
- its kernel is isomorphic to `φ^-1(Q ∩ Γ) = ker φ`;
- its image is `ΓQ ≅ Γ x| (Z wr Z)`.

`Q/(Q ∩ Γ) ≅ Z wr Z` is not finitely presented: a restricted wreath product of a
nontrivial group by an infinite group is never finitely presented (Baumslag
1961). So the image is not finitely presented.

**(6) The simple quotient.** FFWZ Theorem B makes `SV_(G~)` finitely presented,
since the action is of type `[A_2]`. By `abstract-btb-simple-quotient-fp-gate`,
its canonical simple quotient is finitely presented exactly when the image is.
By (5) the image is not.

**(7) The kernel can be removed.**
- **The larger pair.** Let `ψ : F_2 * V -> V` be `φ` on `F_2` and the identity on
  `V`. Let `G' = Γ x| (F_2 * V)`, where `u` acts on `Γ` by conjugation by
  `δ_(ψ(u))`, and let `G'` act on `Ω` by `(γ,u) . U = γ δ_(ψ(u)) U`.
- **It is [A_2].** The checks of step (5) apply unchanged. `G'` is finitely
  presented, point stabilizers are extensions of `Stab_Γ(U)` by `F_2 * V`, and
  pair orbits are finite.
- **Its kernel.** By (3) the kernel is `{1} x ker ψ`. It is normally generated
  by the two elements `(1, a_i^-1 φ(a_i))`, with `φ(a_i)` written in generators
  of `V`.
- **Sharpness.** The inclusion `G~ <= G'` is compatible with the actions, and
  `G~ ∩ ker = {1} x ker φ`, which is the kernel of `G~`.

So the pair is sharply embedded in a type `[A_2]` pair with finitely normally
generated kernel. `∎`
