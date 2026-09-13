---
rg: 2
id: boone-higman-closed-under-finite-direct-products
kind: claim
title: The direct product of two groups that embed in finitely presented simple groups embeds in a finitely presented simple group
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that is the known closure of the permutational class B_A under finite direct products; this asks for the same closure for the class of subgroups of finitely presented simple groups, where no product construction is known.
  boone-higman-implies-relative-permutational-bh: that places each Boone--Higman group in a relative actor whose action image need not be finitely presented; this asks for a finitely presented simple envelope of a product, which the relative form does not supply.
  boone-higman-conjecture: that is the universal embedding conjecture for decidable groups; this is one permanence property of the class of groups that already have envelopes, and it would follow from the conjecture itself.
  relative-pbh-closed-under-finite-direct-products: that is the proved closure of the RELATIVE permutational form and of kernel removability under products; this is the open closure of the Boone--Higman class itself.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, one sufficient hypothesis for this closure; this is the closure statement.
artifacts:
  - research/artifacts/bh-product-closure-2026-09-12.md
  - research/artifacts/bh-simple-products-embed-2026-09-12.md
---

**OPEN.** Let `G <= S` and `H <= T` for finitely presented simple groups `S` and
`T`. Then `G x H` embeds in a finitely presented simple group.

**Equivalent form.** Because subgroups inherit envelopes, the claim is equivalent to:
for all finitely presented simple `S` and `T`, `S x T` embeds in a finitely
presented simple group.

**Routes into this claim.** None fires while its premises are open.
- **From the conjecture.** `bh-product-closure-via-boone-higman-conjecture`: `S x T`
  is finitely presented with solvable word problem, so Boone--Higman covers it.
- **From kernel removal.** `bh-product-closure-via-a2-kernel-removal` uses:
  - FFWZ Theorem C (`boone-higman-implies-relative-permutational-bh`);
  - the product lemma `relative-pbh-closed-under-finite-direct-products`;
  - the first part of FFWZ Question 5.9 (`a2-pairs-embed-in-a2-pairs-with-fng-kernels`),
    applied to the product pair.
- **From MIF envelopes.** Enlarge `S` and `T` to finitely presented simple MIF
  groups (BFFHZ Question 3.4, `fp-simple-groups-embed-in-fp-simple-mif-groups`),
  then use BFFHZ Theorem C (iv)⇒(i) and closure of `B_A` under products. Route:
  `bh-direct-products-via-mif-envelopes`.
- **From relatively simple kernel removal.**
  `bh-product-closure-via-relatively-simple-kernel-removal` uses:
  - FFWZ Theorem C and the product lemma, as above;
  - the finitely presented relatively simple group of the product actor
    (`abstract-btb-pairs-fp-and-relatively-simple`);
  - the second part of FFWZ Question 5.9
    (`fp-relatively-simple-pairs-embed-with-fng-kernels`), applied to that group.

**Why it matters.** It is step (P) of `fp-metabelian-groups-satisfy-boone-higman`.
A finitely generated metabelian group embeds in a product of linear groups over
fields of different characteristics, and the known envelopes for those factors
live in different hosts. The embedding is Wehrfritz's Corollary 1.2, recorded in
`fg-metabelian-groups-embed-in-products-of-coprimary-quotients`.

**Sources checked** (PDF texts extracted on MSI; see the artifact for line numbers).
- **BBMZ survey** (arXiv:2306.16356v3): no closure under direct products is stated
  for the Boone--Higman class. Checked by lane `bh-metabelian-5-3-7`.
- **BFFHZ** (arXiv:2503.21882v2): "PBH is stable under commensurability and direct
  products [Zarb]". That is only the permutational class. Their Question 3.4 note:
  "If the answer is yes, then BH is equivalent to PBH".
- **FFWZ** (arXiv:2603.24687v2), Question 5.9, first part: "For G ↷ S an action of
  type [A_2] with kernel K, does there always exist an action G′ ↷ S′ of type
  [A_2] with kernel K′ finitely normally generated, such that (G,K) sharply
  embeds in (G′,K′)?"

## Attempts

1. **Through the permutational class** (lane `bh-metabelian-5-3-7`). `B_A` is
   closed under finite direct products. BFFHZ Theorem C shows every subgroup of a
   finitely presented simple highly transitive or MIF group lies in `B_A`. So the
   closure holds whenever `S` and `T` enlarge to finitely presented simple MIF
   groups. *Stops* at BFFHZ Question 3.4.
2. **Relative actors multiply, the image gap does not shrink** (lane
   `bh-metabelian-5-3-7`, formalized by lane `bh-product-closure`).
   - **The product actor.** `S` and `T` sharply embed in type [A_2] pairs `(G_1,K_1)`
     and `(G_2,K_2)`. The product actor on the disjoint union is of type [A_2] with
     kernel `K_1 x K_2`, and `S x T` sharply embeds in it.
   - **Kernel removal.** Removability passes to products
     (`relative-pbh-closed-under-finite-direct-products`).
   - *Stops.* The simple quotient of the abstract twisted Brin--Thompson group is
     finitely presented iff the action image is
     (`abstract-btb-simple-quotient-fp-gate`). The product image
     `(G_1/K_1) x (G_2/K_2)` is finitely presented iff both factors are. That is
     the kernel-removal question for each factor, unchanged by the product.
3. **Theorem C actors.** For the actor `Aut_S(S * F_n)` acting on
   `Hom_S(S * F_n, S)`, non-recursive one-variable mixed identities of `S` make
   the image non-finitely-presented and the kernel non-removable
   (`a2-kernel-removal-forces-recursive-kernel`). The product of two such actors
   inherits this from either factor. *Dies* as an unconditional route: it needs
   the recursiveness hypothesis for both `S` and `T`, and it still needs kernel
   removal.
4. **No product is MIF.** For nontrivial `S` and `T`, `S x T` has the nontrivial
   mixed identity `w(x) = [[x,(s,1)],(1,t)]` with `s != 1`, `t != 1`. The inner
   commutator lies in `S x 1`, which commutes with `(1,t)`. So a MIF envelope of
   `S x T` must be strictly larger than `S x T`. *Consequence only*: this does not
   obstruct Attempt 1.
5. **Self-square envelopes.** A finitely presented twisted Brin--Thompson group
   `SV_G` contains `SV_G x SV_G`, as the stabilizer of a clopen set
   (`twisted-btb-clopen-action-is-type-a`). So two groups with a common finitely
   presented simple twisted Brin--Thompson envelope have their product inside it.
   *Stops*: a common such envelope for arbitrary finitely presented simple `S` and
   `T` is PBH for both.
6. **Unit-group hosts over one field** (lane `bh-metabelian-5-3-7`).
   `G <= A^x/F^x` and `H <= B^x/F^x` give `G x H <= (A ⊗_F B)^x / F^x` via
   `(a,b) -> a ⊗ b`. *Stops*: it raises the tensor degree of Leavitt hosts, whose
   finite presentation in higher degree is open, and it cannot mix characteristics.
7. **Coordinatewise abstract twisted Brin--Thompson groups** (lane
   `bh-simple-products-embed`).
   - `SV_{A_1} x SV_{A_2}` is finitely presented, and `S x T` meets
     `SK_{A_1} x SK_{A_2}` trivially. That pair is not relatively simple, since
     `SV_{A_1} x SK_{A_2}` is a proper normal subgroup outside it.
   - The relatively simple group built from both actors is `SV_A` for the product
     actor `A`, and `S x T` sharply embeds in it
     (`abstract-btb-pairs-fp-and-relatively-simple`).
   - *Stops* at the gate of Attempt 2. Removing `SK_A` is the second part of FFWZ
     Question 5.9 (`fp-relatively-simple-pairs-embed-with-fng-kernels`).
8. **"Every finitely presented simple group satisfies PBH"** (lane
   `bh-simple-products-embed`). By BFFHZ Theorem C (i)⇔(iv) this is Question 3.4,
   so it is Attempt 1.
   - **A sufficient intrinsic condition.** `S` has a proper finitely generated
     subgroup `H` with finitely many double cosets `H\S/H`. Then `S ↷ S/H` is
     faithful of type [A_2], and `SV_S` is a finitely presented simple group
     containing `S`.
   - *Stops*: no general source of such `H`.
9. **Wreath and automorphism overgroups** (lane `bh-simple-products-embed`).
   - `S ≀ Z/2` and `Aut(S x T)` contain `S x S` and `S x T` as normal subgroups. So
     neither is simple, and their envelopes pose the same problem.
   - For `B ≀_X Q` with `B` perfect and `Q` simple acting non-trivially, FFWZ
     Lemma 3.1 makes the base the largest normal subgroup. A subgroup meeting the
     base trivially embeds in `Q`, so nothing is gained.
   - *Dies.*
10. **Joint embedding and squares** (lane `bh-simple-products-embed`). The claim
    holds iff both of the following hold:
    - (JE) any two finitely presented simple groups embed in a common one;
    - (SQ) `U x U` embeds in a finitely presented simple group for every finitely
      presented simple `U`.

    For the converse, take `S, T <= U`; then `S x T <= U x U`. *Stops*: (JE) is
    known for PBH groups through free products (BFFHZ Corollary F), and (SQ) for
    PBH groups by Attempt 5. Neither is known in general.
11. **The Theorem C actor of `S x T` itself** (lane `bh-simple-products-embed`).
    Rerun FFWZ's proof of Theorem C with `Γ = S x T`.
    - `Aut_Γ(Γ * F_n)` is finitely presented (trivial center), stabilizers are
      finitely generated, and the Γ-translations act freely.
    - Finitely many pair orbits came from high transitivity, which FFWZ derive from
      simplicity. This was not rechecked here.
    - The action is never faithful. With `w` from Attempt 4, `x_1 ↦ x_1 w(x_2)` is a
      non-trivial automorphism that acts trivially.
    - *Dies*: at best one more relative actor, behind the gate of Attempt 2.
