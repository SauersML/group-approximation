---
rg: 2
id: simple-in-bader-shalom-lattice-forces-compact-presentation
kind: claim
title: If a Bader-Shalom lattice in a product of two groups contains an infinite simple subgroup, both factors are compactly presented
distinct_from:
  product-lattice-fp-iff-factors-compactly-presented: that is the established reduction of finite presentability of a uniform product lattice to compact presentability of the factors; this is the open assertion that the presence of an infinite simple subgroup forces those factors to be compactly presented.
  decidable-simple-groups-embed-in-bader-shalom-lattices: that asks for the lattice to exist for every decidable simple group; this asks that any such lattice, once it exists, be finitely presented. Either can fail while the other holds.
  just-infinite-over-simple-subgroup-gives-fp-simple-host: that shows the lattice is virtually a power of a finitely generated simple group T; this asks whether T is finitely presented.
---

**OPEN.**

Let `G_1`, `G_2` be non-discrete, compactly generated, locally compact groups that
are just-non-compact and have no nontrivial abelian normal subgroup. Let
`Γ < G_1 × G_2` be a cocompact lattice with dense projections. Suppose `Γ` contains
an infinite simple subgroup. Then `G_1` and `G_2` are compactly presented.
Equivalently, `Γ` is finitely presented.

This is prerequisite P2 of `boone-higman-via-bader-shalom-lattice-hosts`.

## Attempts

1. **Exact reformulation, the cheapest prerequisite attacked (heretic lane c-bhdec1,
   2026-09-17).**
   - *Finite presentation is a factor property.* By
     `product-lattice-fp-iff-factors-compactly-presented`, `Γ` is finitely
     generated, and `Γ` is finitely presented iff both factors are compactly
     presented. So the "equivalently" in the statement is established.
   - *Structure of `Γ`.* By `bader-shalom-normal-subgroup-theorem`, `Γ` is
     just-infinite. `Γ` is finitely generated and contains an infinite simple `S`.
     So `just-infinite-over-simple-subgroup-gives-fp-simple-host`, clauses 1–3,
     gives a finite-index normal `R ≅ T^k ◁ Γ`, with `T` a finitely generated
     infinite simple group, `R` without proper finite-index subgroups, and
     `Γ` fp iff `T` fp.
   - *Reformulation.* **P2 is equivalent to: the simple group `T` produced by the
     lemma is finitely presented.** This is a statement about compact
     presentability of each factor, and it does not see `S` at all.
   - *No automatic implication.* Finite generation plus simplicity does not force
     finite presentation, even for tree-acting groups. Caprace, arXiv:1709.05949,
     p. 35, Theorem 4.30 (Le Boudec) gives "a finitely generated infinite simple
     group Γ acting edge-transitively on the regular tree T of degree 20", which "is
     not finitely presented". But Caprace also warns that it "is very different from
     the projection of a lattice", having locally finite vertex stabilizers. So this
     example neither refutes P2 nor supports it.
   - *Known cases where P2 holds.* If both factors act properly and cocompactly on
     simply connected geodesic spaces, for instance on trees or buildings, then
     `Γ` is finitely presented, and the known virtually simple Burger–Mozes lattices
     satisfy P2. But those are exactly the factor classes that
     `decidable-simple-groups-embed-in-bader-shalom-lattices`, Attempt 1(b)–(c),
     rules out for universality. **The interaction of P1 and P2 is the whole
     difficulty.** The factor classes where P2 is free are the ones where P1 is
     dead, so a proof of P2 must work for non-CAT(0), non-Haagerup factors.
   - *Where a refutation would have to come from.* A just-non-compact,
     compactly generated, non-compactly-presented factor without abelian normal
     subgroups, containing a dense lattice projection. The standard
     non-compactly-presented examples (for instance `K^2 ⋊ SL_2(K)` over a
     non-discrete local field, which Cornulier–de la Harpe, arXiv:1403.3796v4,
     p. 184, derive from Proposition 8.A.10(2) to be "not compactly presented") have abelian normal subgroups and are
     excluded by hypothesis.

   **Status after this attempt:** OPEN, reduced exactly to finite presentability of
   `T`. If P2 fails, the route survives in the weaker form that consumes
   `decidable-simple-groups-embed-in-bader-shalom-lattices` with compactly
   presented factors (P1c).
