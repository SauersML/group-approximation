# Boone–Higman swarm 6, lane `bh-product-closure`: is the Boone–Higman class closed under direct products?

2026-09-12. Question: if `G <= S` and `H <= T` with `S`, `T` finitely presented simple, does `G x H` embed in a finitely presented simple group?

**Outcome: not settled.** Three things landed:
- **A proved lemma.** The relative permutational form, and removability of its kernels, are closed under finite direct products.
- **Two conditional routes.** One from the Boone–Higman conjecture, one from the first part of FFWZ Question 5.9.
- **A sharpened open claim** with six Attempts.

The closure is not a formal permanence property. Every route found needs one of these open inputs:
- the conjecture itself;
- FFWZ Question 5.9, first part (kernel removal);
- BFFHZ Question 3.4 (MIF envelopes).

## 0. Sources (PDF text extracted on MSI)

**BFFHZ**, Belk–Fournier-Facio–Hyde–Zaremsky, arXiv:2503.21882v2, file `/scratch.global/sauer354/bh-outfn-mcg/2503.21882v2.txt`.
- **Lines 145–151**, Theorem C: "For a finitely generated group G (with solvable word problem) the following are equivalent:
  (i) G satisfies the permutational Boone–Higman conjecture, i.e., it embeds in a group admitting an action of type (A).
  (ii) G embeds in a finitely presented (simple) twisted Brin–Thompson group.
  (iii) G embeds in a finitely presented simple group that is highly transitive.
  (iv) G embeds in a finitely presented simple group that is MIF."
- **Line 178:** "PBH is stable under commensurability and direct products [Zarb]."
- **Lines 492–499**, proof of Theorem C: (iv)⇒(i) goes through "G embeds in Aut_G(G ∗ F_2) … and Aut_G(G ∗ F_2) admits an action of type (A) by Theorem E".
- **Lines 545–548**, Question 3.4: "Does every finitely presented simple group embed in a finitely presented simple MIF group? If the answer is yes, then BH is equivalent to PBH, and finitely presented twisted Brin–Thompson groups are universal among finitely presented simple groups."
- **Line 621:** "PBH is invariant under commensurability [Zarb, Proposition 5.6]."

**FFWZ**, Fournier-Facio–Wu–Zaremsky, arXiv:2603.24687v2, file `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`.
- **Lines 152–156**, Definition 1.6: "(G,N) embeds in (G′,N′) if there exists an injective homomorphism ι: G ֒→ G′ such that ι(G) ∩ N′ = ι(N). We say a group Γ sharply embeds in a normal pair (G,N) if the normal pair (Γ,{1}) embeds in (G,N)."
- **Lines 161–164**, Conjecture 1.8 (relPBH): "Let Γ be a finitely generated group with solvable word problem. Then there exists a group G with a type [A2] action on a set S such that Γ sharply embeds in (G,ker(G ↷ S))".
- **Lines 185–186**, Theorem C (Theorem 5.1): "If a group satisfies the Boone–Higman conjecture then it satisfies the relative permutational Boone–Higman conjecture."
- **Lines 1339–1349**, Question 5.9, first part: "For G ↷ S an action of type [A2] with kernel K, does there always exist an action G′ ↷ S′ of type [A2] with kernel K′ finitely normally generated, such that (G,K) sharply embeds in (G′,K′)?" The note after it: "a 'yes' answer to the first part of Question 5.9 would tell us that (relPBH) implies (PBH)".

Not re-read here: the definition of type [A_2] (FFWZ Definition 1.3) and Zaremsky arXiv:2405.18354. Both are used at main's recorded verification level (`twisted-brin-thompson-finite-presentation-criterion`, `type-a-action-gives-boone-higman-for-subgroups`).

## 1. Lemma: relative actors and kernel removability multiply

`relative-pbh-closed-under-finite-direct-products`, proof `relative-pbh-finite-direct-products-proof`.

**Setting.** For i = 1, 2 let G_i ↷ S_i be of type [A_2] with kernel K_i, and S_i nonempty. Let G_1 x G_2 act on S_1 ⊔ S_2 coordinatewise.

1. **The product action.** It is of type [A_2]:
   - the product of finitely presented groups is finitely presented;
   - Stab(s) = Stab_(G_1)(s) x G_2 is finitely generated;
   - orbits on the four blocks of (S_1 ⊔ S_2)^2 are finite, the mixed blocks having |S_1/G_1|·|S_2/G_2| orbits.

   Its kernel is K_1 x K_2 and its image is (G_1/K_1) x (G_2/K_2).
2. **Sharp embeddings.** If Γ_i sharply embeds in (G_i, K_i), then Γ_1 x Γ_2 sharply embeds in the product pair, since intersections are taken coordinatewise.
3. **Removability.** If (G_i, K_i) embeds in (G_i′, K_i′) with K_i′ = ⟨⟨F_i⟩⟩ finitely normally generated, then the product pair embeds in (G_1′ x G_2′, K_1′ x K_2′), whose kernel is ⟨⟨F_1 x 1 ∪ 1 x F_2⟩⟩.

This is the relative analogue of Zaremsky Proposition 5.6. No novelty is claimed.

## 2. Routes into `boone-higman-closed-under-finite-direct-products`

**(R1) From the conjecture.** `bh-product-closure-via-boone-higman-conjecture`.
- S x T is finitely presented.
- It has solvable word problem, by Kuznetsov (`simple-envelope-forces-solvable-word-problem`) applied coordinatewise.
- So Boone–Higman embeds it.

**(R2) From kernel removal.** `bh-product-closure-via-a2-kernel-removal`.
1. FFWZ Theorem C puts S sharply in (G_1,K_1) and T sharply in (G_2,K_2).
2. Lemma 1 gives the product pair.
3. Question 5.9 (first part) embeds the product pair in (G′,K′) with K′ finitely normally generated.
4. Then S x T ∩ K′ = S x T ∩ K = 1, so S x T ≤ G′/K′.
5. G′/K′ acts faithfully on S′ and is finitely presented, its point stabilizers are finitely generated, and it has finitely many pair orbits. So the action is of type (A).
6. Zaremsky's Corollary B gives the envelope.

**(R3) From MIF envelopes.** `bh-direct-products-via-mif-envelopes`, drafted by lane `bh-metabelian-5-3-7`, not yet on main. Enlarge S and T to finitely presented simple MIF groups (Question 3.4). BFFHZ Theorem C (iv)⇒(i) places them in B_A, and B_A is closed under products.

## 3. Obstructions and attempts

**(a) The image gap is invariant under products.** By `abstract-btb-simple-quotient-fp-gate`, the simple quotient of the abstract twisted Brin–Thompson group of an [A_2] actor is finitely presented iff the action image is. For the product actor the image is (G_1/K_1) x (G_2/K_2). A direct product of groups is finitely presented iff each factor is: a factor is a retract, and retracts of finitely presented groups are finitely presented. So multiplying actors neither creates nor removes the finite-presentation gap.

**(b) Theorem C actors.** By `a2-kernel-removal-forces-recursive-kernel` (c), if S has non-recursive one-variable mixed identities, the image of Aut_S(S ∗ F_n) ↷ Hom_S(S ∗ F_n, S) is not finitely presented and its kernel cannot be removed. The product of the actors of S and T fails in the same way. No finitely presented simple group with non-recursive mixed identities is known.

**(c) Products are never MIF.** Let s ∈ S and t ∈ T be nontrivial, and put c = (s,1), d = (1,t).
- **The word.** w(x) = [[x,c],d] = c^{-1}x^{-1}c x d^{-1} x^{-1}c^{-1}x c d is a reduced nontrivial element of (S x T) ∗ ⟨x⟩.
- **It is an identity.** For g = (a,b), [g,c] = ([a,s],1) commutes with d, so w(g) = 1.

So S x T satisfies a mixed identity. A MIF envelope, as in BFFHZ (iv), must be strictly larger. This does not obstruct (R3).

**(d) Self-square envelopes.** By `twisted-btb-clopen-action-is-type-a`, the stabilizer of a proper clopen U in a finitely presented twisted Brin–Thompson group SV_G is D(U) x D(U^c) ≅ SV_G x SV_G. So SV_G contains its own square, and any two subgroups of one such SV_G have their product inside SV_G. For arbitrary finitely presented simple S and T, a common such envelope is PBH for both, i.e. (R3)'s input.

**(e) Converse directions not found.**
- Closure under products is not known here to imply Question 3.4 or Question 5.9.
- Iterating the closure on S (S x S ≤ W_1, W_1 x W_1 ≤ W_2, …) produces no single finitely presented self-square envelope. So closure does not obviously give (d).

## 4. What remains

- **The claim** stays OPEN. It is implied by each of the conjecture, the first part of Question 5.9, and Question 3.4.
- **Smallest test case:** S x T for two finitely presented simple groups that are not known to be MIF or highly transitive. Two candidates:
  - the Leavitt unit groups L_(F_p)(1,2)^x / scalars from `positive-char-surface-linear-groups-satisfy-boone-higman`, for different primes p and q, so that no single-field tensor host applies;
  - a finitely presented simple group paired with any group in B_A.
- **Not attempted:**
  - HNN or amalgam constructions over S x 1 and 1 x T inside the envelope of S ∗ T;
  - whether the Boone–Higman class is closed under free products. That is only known for B_A (BFFHZ Corollary F).

## 5. Credit

- **Source results:** the ingredients are BFFHZ Theorem C and Corollary F, and FFWZ Theorem C, Definition 1.6 and Question 5.9. The disjoint-union product is Zaremsky Proposition 5.6.
- **Lemma 1** is an elementary relative version. No priority search was possible beyond these texts; the session web-search budget is exhausted.
- **Attempts 1, 2 and 6** on the claim node are from lane `bh-metabelian-5-3-7`'s unlanded draft, credited there.
