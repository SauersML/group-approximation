---
rg: 2
id: amenable-edge-division-ring-embeddings-proof
kind: route
title: The closure of an amenable edge group ring in any vertex division ring is its Ore localisation, which makes both compatibility conditions automatic
target: amenable-edge-graphs-of-groups-preserve-division-ring-embeddings
requires:
  - compatible-graphs-of-groups-with-loops-embed-in-division-rings
  - product-of-trees-lattices-embed-in-division-rings
---

**Imported.**
- **Tamari** (D. Tamari, Proc. ICM 1954, published 1957; used in the same form by Kropholler--Linnell--Moody and by
  Kielak, arXiv:1802.07049). Theorem numbers were not re-checked on 2026-09-17. If `C` is amenable and `k[C]` is a
  domain, then `k[C]` satisfies the left and right Ore conditions. The right condition follows by applying the
  involution `g -> g^-1`. Its classical ring of quotients `Ore(k[C])` is a division ring.
- **Universal property of Ore localisation.** An injective ring homomorphism from an Ore domain into a division ring
  extends uniquely to its classical quotient ring, by `s^-1 a -> f(s)^-1 f(a)`. The extension is injective, since
  the source is a division ring.

**1. The edge closures are Ore localisations.**
- Let `e` be an edge with `C = G_e -> G_(t(e)) = V`, and `k[V] -> D_V`.
- `k[C]` is a subring of `D_V`, so it is a domain. By Tamari it is Ore.
- The image of the extension `Ore(k[C]) -> D_V` is a division subring containing `k[C]`. It is contained in every
  division subring containing `k[C]`. So `Div(k[C], D_V)` is the image of `Ore(k[C])`.

**2. Condition (3) is automatic.**
- `D_e` and `D_ebar` are both `k[C]`-isomorphic to `Ore(k[C])`, via the edge maps into `D_(t(e))` and `D_(o(e))`.
- By uniqueness of the extension, the composite is a `k[C]`-isomorphism.

**3. Condition (2) is automatic.**
- Let `S` be a right transversal of `C` in `V`, so `k[V] = ⊕_(s in S) k[C] s`.
- Suppose `sum_(i=1)^m d_i s_i = 0` in `D_V`, with `d_i in D_e` and distinct `s_i in S`.
- By step 1 and the left Ore condition there is a common left denominator `c in k[C] \ 0` with `d_i = c^-1 a_i`
  and `a_i in k[C]`.
- Multiplying on the left by `c` gives `sum a_i s_i = 0` in `D_V`. This element lies in `k[V]`, which embeds in
  `D_V`.
- The summands have disjoint supports `C s_i`, so every `a_i = 0`, and hence every `d_i = 0`.

**4. Conclusion.**
- The graph of groups is D-compatible with the given vertex rings.
- [[compatible-graphs-of-groups-with-loops-embed-in-division-rings]] embeds `k[G]` in a division ring. That result
  covers loops and infinite graphs.
- The same proof works over a division ring `k`, provided Tamari's theorem is used over `k`. The Følner counting
  argument is dimension-theoretic over `k`.

**5. The example `G = Lambda *_Z P`.**
- **Vertex data.**
  - `P` is torsion-free and virtually `Z^3`. By Kropholler--Linnell--Moody, `k[P]` is an Ore domain, so it embeds in
    `Ore(k[P])`.
  - `k[Lambda]` embeds in a division ring by [[product-of-trees-lattices-embed-in-division-rings]].
  - The edge group `Z` is amenable.
- **Steps 1 to 4.** `k[G]` embeds in a division ring.
- **Properties of `G`.**
  - `G` is torsion-free (an amalgam of torsion-free groups) and finitely presented (finitely presented factors,
    finitely generated edge group).
- **Not locally embeddable into unique-product groups.**
  - `P` contains finite sets `X, Y` with no uniquely represented product (Promislow).
  - A homomorphism `phi : G -> H` injective on a finite set containing `X ∪ Y ∪ XY` preserves the product
    multiplicities: `phi(x)phi(y) = phi(xy)`, and `phi` separates distinct products.
  - So `phi(X)`, `phi(Y)` witness that `H` fails unique products.
- **Not locally embeddable into amenable groups.**
  - `G` is finitely presented, so a partial homomorphism defined on a ball containing the relators extends to a
    homomorphism `G -> H`. Local embeddability therefore gives homomorphisms injective on arbitrarily large balls.
  - A homomorphism injective on a ball of radius at least the word length of some `1 != g in Lambda` is nontrivial
    on `Lambda`.
  - `Lambda` is simple, so the homomorphism is injective on `Lambda`, and `F_2 <= Lambda` then embeds in `H`.
- **Not locally embeddable into residually finite groups.**
  - Compose with finite quotients of `H`: the homomorphism would be nontrivial on `Lambda` in a finite group, which is
    impossible.
  - The same argument shows `G` is not residually finite, so `G` is not virtually special, not a 3-manifold group,
    and not in any `CS(u,d,p)`.
- **Elementary amenability.** `G` is not elementary amenable, because it contains `F_2`.
- **Strong Atiyah.** In characteristic zero, Strong Atiyah for `G` is not recorded.
  - `G` is not locally indicable, because it contains the perfect group `Lambda`.
  - Fisher--Sanchez-Peralta's Atiyah graph corollary would need Strong Atiyah for `Lambda`.

**Calibration.**
- `Z *_Z Z`, with any `k(x)`, recovers `Z` sitting in `k(x)`.
- `BS(1,2) = Z *_Z` with `phi(c) = c^2` and `D_A = k(x)`:
  - the closures of `k[x^(±1)]` and `k[x^(±2)]` are `k(x)` and `k(x^2)`;
  - `{1, x}` is independent over `k(x^2)`;
  - `phi` gives `k(x) ≅ k(x^2)`.

  Step 2 of the loop theorem gives `k[BS(1,2)]` in a division ring, which agrees with Kropholler--Linnell--Moody.
- The method cannot "prove" anything false for torsion-free inputs: every vertex input is a domain by hypothesis.
  With torsion in an edge group, `k[C]` is not a domain, so Tamari does not apply and step 1 fails at the first
  line.
