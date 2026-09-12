# Boone--Higman swarm, lane `bh-twisted-brin-thompson`: embedding conditions and type (A) permanence

2026-09-12. Two parts:
1. what an action must satisfy for the twisted Brin--Thompson and Rover--Nekrashevych hosts to be finitely presented and simple, pinned to sources and to the Cairn nodes that already carry each statement;
2. one new permanence result for the type (A) route.

## 1. Embedding conditions, with sources

Source verification level:
- **Zaremsky arXiv:2405.18354:** statements quoted from the abstract, and in Cairn from the paper.
- **FFWZ and the BBMZ survey:** read through a summarizing fetch of the arXiv HTML, not line by line. Treat theorem numbers as indicative.

**Twisted Brin--Thompson groups SV_G (faithful action).**
- **Zaremsky, arXiv:2405.18354, abstract:**
  - `SV_G` is finitely presented iff G is finitely presented, there are finitely many orbits of two-element subsets of S, and point stabilizers are finitely generated.
  - SV_G is simple, so every subgroup of such a G satisfies Boone--Higman (Theorem A and Corollary B).
  - Cairn: `twisted-brin-thompson-finite-presentation-criterion`, `type-a-action-gives-boone-higman-for-subgroups`.
- **Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2:**
  - Definition 1.3: type [A_n] means G is of type F_n, Stab_G(T) is of type F_(n-|T|) for finite T, and the diagonal action on S^n has finitely many orbits.
  - Theorem A (3.6): abstract SV_G is relatively simple.
  - Theorem B (4.1): SV_G is finitely generated iff [A_1], finitely presented iff [A_2], of type F_infinity iff [A_infinity].
  - Corollary 4.2: the canonical simple quotient is finitely presented iff the action image G/K is. Cairn: `abstract-btb-simple-quotient-fp-gate`.

**Rover--Nekrashevych hosts.**
- **Zaremsky, arXiv:2405.09722, Theorem 1.1:** every finitely presented self-similar group embeds in a finitely presented simple group, namely [V_d(G), V_d(G)]. Finite presentation of V_d(G) does not pass automatically to its commutator subgroup.
- **Zaremsky, arXiv:2405.09722, Theorem 1.2:** every f.g. subgroup of GL_n(Q) satisfies Boone--Higman. Cairn: `fp-self-similar-groups-embed-in-fp-simple-groups`.
- **BBMZ survey, Corollary 4.16:** contracting self-similar groups embed in finitely presented simple groups.
- **Cairn:** `contracting-srn-rational-stabilizers-are-fp` (finite rational-set stabilizers of contracting V_d(G) are finitely presented) and `fp-full-binary-cantor-groups-have-type-a-actions` (a finitely presented full Cantor group containing V has a type (A) action on proper clopen sets).

**What a new class must supply on this route.** An overgroup Gamma of the input with:
- finite presentation;
- a faithful action with finitely many pair orbits, i.e. a finitely generated core-free subgroup of finite bi-index in the transitive case;
- finitely generated point stabilizers.

Equivalently, via the full-group node, a finitely presented full Cantor group containing V. For Problem 5.3 of the survey:
- **fp residually finite (12):** open. Cairn: `every-fp-rf-group-embeds-in-fp-self-similar-group`.
- **Automatic (11) and CAT(0) (10):** open. The rational-embedding preprint of Belk--Bleak--Chatterji--Matucci--Perego proves no finite presentation of the full groups (Cairn audit 2026-08-30).
- **Complexity:** every universal overgroup family must have unboundedly complex word problem (`complexity-bounded-host-classes-are-not-universal`).
No new class was reached in this lane session.

## 2. Permanence of the type (A) route (known result, verified and wired)

**Credit correction, from lane `bh-lit-map`.** This permanence is NOT new.
- **Direct products and commensurability:** BFFHZ arXiv:2503.21882v2 say the permutational Boone--Higman property, i.e. membership in B_A, "is stable under commensurability and direct products". They cite Zaremsky arXiv:2405.18354, Proposition 5.6.
- **Free products:** BFFHZ Corollary F.
- **What was done here:** the nodes below record elementary verifications with that credit.

- `type-a-actions-closed-under-products-and-finite-wreaths`, with proof `type-a-products-finite-wreaths-proof`:
  - Gamma_1 x Gamma_2 on S_1 ⊔ S_2 is of type (A);
  - Gamma wr S_k on S x [k] is of type (A).
- `boone-higman-type-a-class-closed-under-finite-extensions`, with proof `type-a-class-finite-extensions-proof`:
  - the class B_A of subgroups of type (A) actors is closed under finite direct products and finite-index overgroups (Kaloujnine--Krasner);
  - every member satisfies Boone--Higman.

Why it matters for the swarm:
- **Finite extensions for free.** Any lane that places a class inside a type (A) actor gets virtually-that-class, and finite products with other B_A classes, at no cost.
- **Mixed products.** Products of inputs from different constructions stay covered, as long as each construction passes through a type (A) actor.

**Not claimed:**
- closure of the full Boone--Higman class under products or finite extensions;
- that the literature's hyperbolic, contracting or GL_n(Q) envelopes pass through type (A) actors. This was not checked.

**Novelty:** none. The first search, of the arXiv abstract of 2405.18354 and fetch summaries of 2603.24687v2 and 2306.16356v3, missed Zaremsky Proposition 5.6 and BFFHZ's citation of it. See the credit correction above.

**Open follow-ups for this route:**
- **Free products:** already known for this class (BFFHZ Corollary F).
- **Amalgams over finitely generated subgroups with solvable membership.**
- **Which literature envelopes are type (A) actors.**
