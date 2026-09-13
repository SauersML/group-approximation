---
rg: 2
id: amenable-action-of-a-sofic-group-need-not-be-sofic
kind: claim
title: An amenable transitive action of a finitely generated sofic group need not be sofic, and its direct-sum wreath product can be nonsofic
distinct_from:
  coordinate-action-not-sofic: that is the nonsofic coset action of a Kun-Thom pair, which is not amenable because the actor has property (T); this places that orbit inside a co-amenable coset space of a sofic wreath product, so amenability of the action does not give soficity.
  kun-thom-stabilizer-not-co-amenable: that says the Kun-Thom stabilizer is not co-amenable in its own actor; this builds a different actor, G wr Z, in which a subgroup meeting G_0 in Gamma is co-amenable.
  gkp-sofic-action-toolkit: that imports the positive permanence results; this is a negative example showing that amenability of the action cannot replace their soficity hypothesis.
---

ESTABLISHED (unreviewed).

Let `(G, Gamma)` be a Kun--Thom pair: `Gamma` is infranormal but not normal
in `G`, both have property (T), and `G` is residually finite (Theorem E of
[[kun-thom-nonsofic-wreath]]). Put

```text
H = G wr Z = ( directSum_(n in Z) G_n ) x| <t>,     t G_n t^-1 = G_(n+1),
K = Gamma_0 x directSum_(n >= 1) G_n  <=  directSum_(n in Z) G_n  <=  H,
X = H/K.
```

Then:

- **(A1)** `H` is a finitely generated sofic group;
- **(A2)** `K` is co-amenable in `H`, i.e. `ell^infinity(X)` has an
  `H`-invariant mean, so the action `H ↷ X` is **amenable**;
- **(A3)** the action `H ↷ X` is **not sofic**, in the sense of
  Gao--Kunnawalkam Elayavalli--Patchell Definition 2.1(5);
- **(A4)** `(Z/2) wr_X H = (directSum_X Z/2) x| H` is **not sofic**.

DERIVATION [[amenable-action-of-a-sofic-group-need-not-be-sofic-proof]].

## What this corrects

"Amenable actions are sofic" is false in the sense in which GKP's permanence
theorems use soficity of an action. What is true:

- every action of an amenable **group** is sofic (GKP Theorem 2.17, quoted in
  `research/artifacts/gkp-2401-04945-verified.md`);
- consequently an action whose image `H / ker(alpha)` is amenable is sofic
  (Theorem 2.17 with Proposition 2.15(1)).

An invariant mean on `X` does not suffice. Følner sets of `X` do give finite
models with the correct local orbit pattern. But Definition 2.1(3) also asks
that each model point `s` carry an injective equivariant labelling
`pi_s : E -> B` of the tested points. In the models built from Følner sets
the labels are orbit labels of the diagonal action, and those merge the orbits
of the point stabilizer on `X`. So a model has to resolve how the stabilizer
acts on `X`. In the example the stabilizer `K` contains `G_1`, which acts on
the orbit of `tK` as the Kun--Thom action `G ↷ G/Gamma`.

Two statements rested on the false principle:

- `free-wreath-over-amenable-action-is-sofic`, both its target and its remark
  "amenable actions are sofic";
- the justification in item 1 of `mikhailova-coset-action-two-sided-proof`.
  That conclusion is still true, because there the action factors through
  the amenable group `Q x Q`, and GKP Theorem 2.17 applies.

## Scope

`H` contains the Kazhdan group `G`, so it is not a-T-menable. By Gruenberg's
criterion (not re-verified here) it is also not residually finite. The
example does not decide the conjecture in
`compiler-rope-is-coset-wreath-of-an-a-t-menable-base` that coset actions of
residually finite a-T-menable groups are sofic.
