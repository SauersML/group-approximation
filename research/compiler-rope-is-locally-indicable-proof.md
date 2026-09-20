---
rg: 2
id: compiler-rope-is-locally-indicable-proof
kind: route
title: The compiler's ropes retract onto locally indicable groups with free-product kernels
target: compiler-rope-is-locally-indicable
requires: [mf-compiler-is-uniform-in-finite-seeds, bidirectional-hnn-bridge-trivial-value-is-residually-finite, centralizer-hnn-is-free-generalized-wreath]
---

We use the construction data of `research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`, Section 4,
items 3--9, with an arbitrary finite seed d retained as in the uniform
compiler premise. Suppress d in the notation. On `e in INF`:

- `K_e = K_e^0 x K^g`, where `K_e^0 = F x F(X_e) x F(X_e)`, `K^g = F x P` and `P = F_2 x F_2`.  All factors are
  finitely generated free groups.
- `L_e = L_e^0 x L^g <= K_e`.
- `Q_e = H = ker(P -> Z)`, the kernel of the exponent-difference character.
- `S_e = <F, F^v> <= Gamma_e`, and `tau_e : S_e -> H` is a homomorphism.
- `R_e ≅ R'_e` is finitely presented (item 9).

**Facts used.**
- (LI1) Subgroups of locally indicable groups are locally indicable.
- (LI2) Extensions: if `N` is normal in `G`, and `N` and `G/N` are locally indicable, then so is `G`.  Take a
  nontrivial finitely generated `A <= G`.  If `A` has nontrivial image in `G/N`, that image maps onto `Z`.
  Otherwise `A <= N`, and `A` maps onto `Z` directly.
- (LI3) Free products of locally indicable groups are locally indicable, including free products with free
  groups.  A finitely generated subgroup of a free product is, by Kurosh, a free product of finitely many
  conjugates of subgroups of the factors and a free group.  A nontrivial free product retracts onto a nontrivial
  factor, which maps onto `Z`.
- (BS) Let a group `N` act on a tree without inversions, with trivial edge stabilizers.  Then `N` is the free
  product of representatives of its vertex stabilizers and a free group (Serre, *Trees*, I.5.5).
- Direct products of finitely many free groups are locally indicable, by (LI2).

**Step 1: `Gamma_e` is locally indicable.**  Define `pi : Gamma_e -> K_e` as the identity on `K_e` and `v |-> 1`.
It is a homomorphism because the relations `[v, l] = 1` map to `1`.  Let `N = ker pi`, and let `N` act on the
Bass--Serre tree of `Gamma_e = K_e *_(L_e) (L_e x Z)`.  Since `N` is normal, for any stabilizer `gXg^-1` we have
`N ∩ gXg^-1 = g(N ∩ X)g^-1`.  The map `pi` is injective on `K_e` and on `L_e`, and on `L_e x Z` its kernel is
`<v>`.  So:
- the edge stabilizers of `N` are trivial;
- its vertex stabilizers are trivial or conjugates of `<v> ≅ Z`.

By (BS), `N` is free.  `K_e` is a product of free groups, so by (LI2) `Gamma_e` is locally indicable.

**Step 2: a retraction of `R_e`.**  Define `rho : R_e -> Gamma_e` by `(g, q) |-> g` on the base `Gamma_e x H`, and
`u |-> 1`.  The defining relation `u(s,1)u^-1 = (s, tau_e(s))` maps to `s = s`, so `rho` is a homomorphism.  The
two associated subgroups are `S_e x 1` and the graph `{(s, tau_e(s))}`, and `rho` is injective on both.

**Step 3: the kernel.**  Let `M = ker rho`, and let `M` act on the Bass--Serre tree of the HNN extension `R_e`.
- Edge stabilizers are conjugates of `S_e x 1`.  `M` meets them trivially, by normality and injectivity on
  `S_e x 1`.
- Vertex stabilizers are conjugates of `Gamma_e x H`.  Since `ker(rho|_(Gamma_e x H)) = 1 x H`, `M` meets them
  in conjugates of `1 x H`.

By (BS), `M` is a free product of copies of `H` and a free group.  `H <= F_2 x F_2` is locally indicable by (LI1),
so `M` is locally indicable by (LI3).

**Step 4.**  `R_e / M ≅ rho(R_e) = Gamma_e`, which is locally indicable by Step 1.  By (LI2), `R_e` is locally
indicable.  Left-orderability follows from Burns--Hale, unique products and the domain property follow from
local indicability, and torsion-freeness follows from left-orderability.  ∎

**Calibration.**
- *The method refuses a false case.*  The Promislow (Hantzsche--Wendt) group, `Z^3`-by-`(Z/2)^2` with finite abelianization, is torsion-free but not
  left-orderable.  Its image in any locally indicable group is a finitely generated locally indicable group with
  finite abelianization, so it is trivial.  The kernel is then the whole group and the argument cannot start.  In `R_e` the retraction exists because the twist `tau_e` is carried
  entirely by the second factor `H`, which `rho` kills.
- *It reproduces a known case.*  On `F_2 x F_2 = <x, y> x <a, b>`, viewed as an HNN extension of `F_2 x <a>` with
  stable letter `b`, the same argument recovers local indicability.

**Remark on the envelope.**
[[twisted-rope-is-a-central-rope-over-an-rf-envelope]] embeds `R_e` into a central rope over `(P x P) ⋊ <sigma>`.
That envelope has the swap as torsion and is not used here.  The retraction `rho` bypasses it.
