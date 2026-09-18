---
rg: 2
id: decidable-groups-lie-in-fp-free-minimal-crossed-products
kind: claim
title: Every decidable group lies in a finitely generated group with a free minimal subshift whose binary crossed-product algebra is finitely presented
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is P1, asking only for a minimal free SFT over a finitely presented overgroup; this also asks for a finitely presented crossed product, so it implies P1 and is implied by P1 with quantum rigidity of the chosen SFT, in particular by P1 and P2.
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that embeds the group algebra F_2[G] in a crossed product over a torsion-free Farrell-Jones group; this puts G inside the acting group itself, torsion allowed, with no algebra embedding.
  decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units: that asks for an arbitrary embedding of G in the Leavitt-tensor unit group over a torsion-free Farrell-Jones acting group; this asks for G <= Lambda, which gives such an embedding but may need torsion in Lambda.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one rigid instance over Z^2; this needs rigid instances over overgroups of every decidable group.
---

**OPEN.** Premise (E) of `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`.

## Statement

For every finitely generated group `G` with solvable word problem, there are:
- a finitely generated group `Λ >= G`;
- a finite alphabet `A` and a nonempty subshift `X ⊆ A^Λ` on which `Λ` acts freely and minimally;

such that `LC(X, F_2) ⋊ Λ` is finitely presented as an `F_2`-algebra.

## Automatic consequences (established imports)

- `Λ` is finitely presented (`fp-crossed-products-force-finitely-presented-acting-group`).
- `X` is an SFT (`fp-crossed-products-force-sft-over-any-group`).
- For `G` infinite, `X` is a Cantor space and `LC(X, F_2) ⋊ Λ` is central simple
  (`free-minimal-cantor-crossed-products-are-central-simple`).
- The difference sets of `X` are coarsely connected (`fp-crossed-products-force-connected-differences`),
  and `X` has no homoclinic pairs (`fp-minimal-crossed-products-have-no-homoclinic-pairs`).
- If `Λ` has more than one end, `X` maps onto `Ends(Λ)` (`fp-minimal-crossed-products-map-onto-ends`).

So (E) implies P1, `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`.

## Equivalent form

(E) holds iff every decidable `G` lies in a finitely presented `Λ` that carries a free minimal SFT which
is quantum rigid over `F_2` in the sense of `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
- "If" is `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.
- "Only if" is known only over `Z^2` (`sft-crossed-product-fp-iff-quantum-rigid`). The form above is
  therefore stated as a sufficient condition in general.

**P1 and P2 imply (E)** (established; see the Consequence section of
`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`). P2 is used there only to make the
P1 shift quantum rigid. So P1 ∧ P2 ⇒ (E) ⇒ P1. (E) asks for one rigid shift over one overgroup,
where P2 demands a finitely presented group from every minimal free SFT. Whether either implication
reverses is open.

## Refutation shape

A decidable `G` such that no finitely presented overgroup carries a free minimal SFT that is quantum
rigid over `F_2`. The necessary conditions above say where to look: every such overgroup needs a
shift whose difference sets are coarsely connected, with the compass map onto its ends.

## Attempts

- **Reduction to Z^2 blocks (not closed).** If `G <= Λ_0` with `Λ_0` fp, then `Λ = Λ_0 × Z^2`
  contains `G`. A free minimal quantum rigid `Z^2`-SFT `Ω` (the target of
  `free-minimal-z2-sft-is-quantum-rigid`) pulled back along `Λ -> Z^2` is not free, since `Λ_0` acts
  trivially. A free minimal SFT `Y` over `Λ_0` is also needed. The product `Y × Ω` is free, but a
  product of minimal systems need not be minimal, and rigidity of the product needs a tensor argument
  (compare `tensor-product-algebra-fp-iff-factors-fp`). It stops at: P1 for `Λ_0` plus rigidity of
  `Y`, which is (E) again. So `Z^2` blocks cannot supply the rigidity for `Λ_0`.
