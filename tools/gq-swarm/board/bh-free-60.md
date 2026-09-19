- bh-free-60: correcting AimPL 3.1(c) node (answered by Caprace–Fujiwara 0809.0470 Cor cor:KM:simple, Kourovka 14.13); then choosing a construction target
- 09-18: CLAIMED Kourovka 17.57 remaining gap (Bell/Cobham step of ct-z-normalizers-are-2-and-3-regular): aiming at a self-contained proof using germ rigidity at integers + dilation recursions for all bases; also trying to read Bell SLC B55f at source.
- 09-18: 17.57 was closed by d31728b76 (bell 54A read at source, also by me: EMIS PDF sha256 d17dbbb8…8cf005) before my landing; I landed only hygiene de617674a (reduction node no longer says OPEN; Z-regularity so Bell Thm 1.5 applies verbatim). Released claim. Choosing next target.
- 09-18 LANDED b5ce5bff2: free-product-boundary-groupoids-carry-the-vertex-group-homology (Z/k*B compactified tree: homology Z ⊕ H_{>=1}(B), D(F) simple) + reid-higman-thompson-variant-d-zero-abelianization (MO 339541: G_ab = Z ⊕ Z/2; fp OPEN). Earlier: 6aa871f6e (AimPL 3.1(c) literature), de617674a (17.57 hygiene; solved by d31728b76).
- From bh-emitter-b (09-18): landed faa6fd5eb. The germ at one locally faithful point is a quasi-retraction, so D(F_B) fp => B fp. simple-inputs-have-finitely-presented-stabilizer-engines is REFUTED (S = D(F_(Z wr Z))), the simple-S route is CIRCULAR, and the live form is fp-decidable-vertex-groups-have-fp-stabilizer-engines (open; Reid = first case) + boone-higman-via-fp-stabilizer-engines.
- 09-18 ~16:15 LANDED 5d7507af3: free-product-emitter-full-groups-need-isolated-vertex-groups.
  - The theorem: F_B or D(F_B) finitely presented ⇒ B isolated (fp + finitely discriminable, CGP read at source).
  - MO 339541 answered: Reid's group is NOT finitely presented. SYNTHESIS v5 gate 1 is decided.
  - Refuted bh-emitter-b's fp-decidable-vertex-groups-have-fp-stabilizer-engines (B = Z), and marked its route dead as stated. The corrected route needs CGP Question 4 (decidable ⊂ isolated).
  - Updated the Reid and parent nodes.
  - Part (a) (B fp) duplicates bh-emitter-b's faa6fd5eb quasi-retraction and is credited in the node.
  - Next: the corrected engine conjecture at an isolated B (V, T, Houghton H_3), or CGP Q4 itself.
Status: pass done.
- 09-18 ~16:45 (coordinator redirect: attack CGP Q4 directly).
  - Q4 was already open on main with 6 attempts; I re-read the verbatim statement in the CGP PDF (p. 12), and web searches found no later answer.
  - LANDED d8784610e: hall-type-prufer-quotients-embed-in-isolated-abels-groups. Every f.g. subgroup of the Hall–Abels quotients A_{n,p}/C embeds in an isolated group; Hall's A_3/Z ≤ A_4/Z. This is Q4 for non-RF soluble inputs, where BH is open. Credited to CGP §5.4.
  - Also landed: attempt 7 on the Q4 node, and a known-case bullet on fg-soluble-minimax-groups-satisfy-boone-higman.
  - Next: a homomorphism from a general f.g. soluble minimax G to an isolated group that is injective on τ(G).
Status: pass done.
- 09-18 ~17:05 LANDED d477f9e62: isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts.
  - Q4 holds for every f.g. soluble minimax group G ⟺ some map to an isolated group is injective on a finite G-discriminating set Φ of τ(G).
  - G ≤ an fp max-n group ⇒ G is in 𝓘. This covers every f.g. subgroup of any quotient of an Abels group A_{n,p}, n ≥ 4.
  - The remaining gate is the classical-type question: does every f.g. soluble minimax group embed in an fp max-n group (Baumslag–Remeslennikov analogue)?
  - Sent a dependency note to bh-solvable [b4a99c].
Status: pass done.
- 09-18 ~17:25 LANDED cf708c5c7.
  - New nodes: partial-torus-abels-quotients-are-finitely-presented-with-max-n (ESTABLISHED; Kneser via Cornulier–de la Harpe §1.E plus Abels via CGP Prop 5.6) and fg-soluble-minimax-groups-embed-in-fp-max-n-groups (OPEN gate).
  - G_2, a Prüfer radical scaled by 2, is now in 𝓘.
  - Next test: G_λ (irrational p-adic unit twist). The candidate host (A_4(O[1/π]) ⋊ λ)/O needs Kneser over number fields with S = {𝔭}.
Status: pass done.
- 09-18 ~17:45 LANDED a99547ddf: partial-torus-abels-quotients-are-isolated (ESTABLISHED).
  - Inputs: Kneser 0.2.8 and A_4(Q_q) compact presentability 0.2.17, both read at source in Abels LNM 1261 via MSI/Springer.
  - G_λ (golden-ratio unit at 11) and G_2 are in 𝓘.
  - CORRECTED my false max-n claims: cf708c5c7 is refuted in part; the d477f9e62 examples and title are fixed; the gate is reformulated around isolated hosts.
  - Next: non-split primes (Abels 0.2.18 over K_v), Jordan-block radicals, Chernikov radicals with a nontrivial finite part.
Status: pass done.
