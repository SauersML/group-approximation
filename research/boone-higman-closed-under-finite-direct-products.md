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
  then use BFFHZ Theorem C (iv)⇒(i) and closure of `B_A` under products. The
  route node `bh-direct-products-via-mif-envelopes` was drafted by lane
  `bh-metabelian-5-3-7` and is not yet on main.

**Why it matters.** It is step (P) of `fp-metabelian-groups-satisfy-boone-higman`.
A finitely generated metabelian group embeds in a product of linear groups over
fields of different characteristics, and the known envelopes for those factors
live in different hosts. That lane's draft was not yet on main when this node landed.

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
