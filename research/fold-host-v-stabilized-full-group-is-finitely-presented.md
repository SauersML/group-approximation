---
rg: 2
id: fold-host-v-stabilized-full-group-is-finitely-presented
kind: claim
title: E3 prime for the fold host - for a free minimal quantum rigid fibre with a determining half-plane, the V-stabilized full group of F_n x Z acting on the ABHT fold is finitely presented; open, with the tree coordinate certified, the fibre coordinate provably not, and the question isolated as a fibre filling
distinct_from:
  fold-transfer-theorem-for-fibres-with-a-determining-half-plane: that transfers freeness, minimality and quantum rigidity along the fold; this asks for the group-level finite presentation (E3′), which rigidity alone is not known to give.
  measure-preserving-fibres-block-finite-shadow-bases: that proves the finite-shadow-basis route is closed for this host; this is the E3′ question that remains after it.
  v-stabilized-horofunction-hosts-need-upstream-certification: that is E3′ for hyperbolic seeds, blocked by the failure of upstream certification in the base; here the base (a tree) certifies, and the block is in the fibre.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `fold-transfer-theorem-for-fibres-with-a-determining-half-plane`, `measure-preserving-fibres-block-finite-shadow-bases`, `one-scale-filling-decides-fp-of-v-times-subshift-hosts`.

**OPEN** (posed by bh-g2-abh, 2026-09-18).

## Statement

Let `X` be a free, minimal `Z^2` SFT that is quantum rigid over `F_2` and satisfies (D) of
`fold-transfer-theorem-for-fibres-with-a-determining-half-plane`. Let `Z` be its fold over
`Λ = F_n × Z`, with `n >= 2`. Then `F(G_V × (Λ ⋉ Z))` is finitely presented.

## Payoff

With the fold theorem, this makes `(Λ, Z)` a complete Track A instance over a one-ended, non-amenable,
finitely presented group:
- E1 (free, minimal SFT);
- E2 (rigidity);
- E3′.

`F(G_V × (Λ ⋉ Z))` would then be a finitely presented simple group of type (A) containing `F_n × Z`. The
known necessary condition is met: the fold theorem makes `Z` rigid, as
`fp-v-times-subshift-full-groups-force-quantum-rigidity` requires.

## What is known

1. **One scale suffices.** By `one-scale-filling-decides-fp-of-v-times-subshift-hosts`, Part 1, the
   statement is equivalent to this: the loops of one cocompact domain level of the Stein space die at a
   larger level.
2. **The tree coordinate certifies itself (calibration).** `Z ≅ X̂ × ∂T`, with `Λ` acting through the
   Busemann cocycle. Half-tree splits `∂H(e) = ⊔ ∂H(e')` of the base satisfy upstream certification with
   one edge (`v-stabilized-horofunction-hosts-need-upstream-certification`, item 2). A tree split acts on
   the fibre coordinate only by re-basing: the vertical shift `σ^((0,1))`, a homeomorphism.
3. **The fibre coordinate cannot be certified by translates (proved).** By
   `measure-preserving-fibres-block-finite-shadow-bases`, no finite family of tiles has translates forming
   a basis. So the statement is **not** an instance of the finite-shadow-basis or Thumann mechanism.
   - Whatever proves it must fill loops that refine the fibre, using relations of `X` itself.
   - This is the nonlinear one-scale filling left open for `Z^2` hosts in
     `one-scale-filling-decides-fp-of-v-times-subshift-hosts`, Part 5.
4. **Structural remark (sketch, signs unchecked).**
   - Using the Cuntz–Krieger model of `F_n ⋉ ∂F_n`, the groupoid `Λ ⋉ Z` should be the rank-two
     Deaconu–Renault groupoid of two commuting maps on `Σ_A^+ × X̂`:
     - the local homeomorphism `σ_A × σ_(0,1)`;
     - the homeomorphism `id × σ_(1,0)`.
   - So the fold host would be the fibre host `F(G_V × (Z^2 ⋉ X))` with its vertical direction replaced by
     a Cuntz–Krieger compression.
   - The vertical fibre shift is no longer a unit on its own. It appears only coupled with the
     `(2n−1)`-fold tree compression.

## Routes

- **(a) Transfer from the fibre host.** Show that `F(G_V × (Z^2 ⋉ X))` finitely presented implies the
  statement. If true, E3′ transfers along folds just as E2 does.
  - Obstacle: the fibre host is not a sub-host. A pure vertical fibre shift with the end fixed is not a
    germ of `Λ ⋉ Z`.
  - An operad-with-fibre-transformations argument fails as it stands. Elements of the fibre full group
    do not commute with the `C`-splits, so they are not Thumann transformations.
- **(b) Direct one-scale filling.** Treat the vertical compression as a gain.
  - In the fold host, a fibre refinement can be pushed up the tree. Heights rise, and by (D) rows above
    determine rows below.
  - So a fibre loop at the base level is, one tree split later, a loop of wider row-windows at the next
    height.
  - The open question is whether this trade (width for height), together with finitely many
    fibre-local relations, fills every loop of one level.
- **(c) Refutation test.** A non-filling loop family in the fibre direction would refute the statement:
  loops of cone partitions that stay non-null at every level, like wall certificates for rigidity.
  Rigidity of `X` kills the linear shadow of such families, but not the families themselves.

## Lesson for general BH

After the fold, each master-route gate lands in a different place:
- **E1** (freeness, minimality) and **E2** (rigidity) are carried by the fibre and transfer exactly.
- **E3′** does not transfer by compression. The base certifies itself, but the fibre-measure invariant
  blocks every finite tile family.

So Track A over a skew product needs its finite presentation paid in the fibre, as the nonlinear
one-scale form of quantum rigidity. That is now the sharpest single open step of the fold route, and it is
the same step as for the amenable `Z^2` hosts. The two routes stand or fall on the same filling problem.
