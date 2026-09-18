# bh-gln-tracka
Direction: GL_n(Q) into an fp simple group (BBMZ 5.3(5)) via Track A, with St_10(R_L) in the acting group.

**Landed 29c2c60a5b (lane proofs, unreviewed):**
- `bounded-valence-trees-scale-only-primes-below-the-valence` (ESTABLISHED): in a tree of valence ≤ d, a root of prime order ℓ > d of g satisfies Fix(root) = Fix(g).
  - Prime-root-bounded vertex stabilizers ⇒ H is prime-root bounded and contains no (Q,+), Z_(p) or GL_n(Q).
  - Finite graphs of groups with finite-index edge groups carry divisibility by all primes > valence in a vertex group.
  - Sharp: the p-adic tree, BS(1,m).
- `gl-n-q-bh-via-track-a-over-st-10-times-free-group` (route, OPEN): Λ_0 = St_10(R_L) × F_2.
  - Supplied:
    - no Clapham envelope and no square;
    - a free SFT, via BSS thm:selfsimulation + cor:stronglyaperiodic;
    - minimality reduces to (M2) for St_10(R_L) alone (product with F_2-Toeplitz).
  - Filters on the (M2) witness: St_10(R_L) is m.a.p. (quasisimple, PE_10 simple), so no almost-automorphic witness; FA, so no tree skeleton.
  - Rigidity: no cheap source. Compression puts divisibility in vertex groups or at an emitter, and the proved (★′) instances are CAT(0).
  - K′ abandoned: every overgroup of GL_n(Q) is non-RF, non-hyperbolic and non-CAT(0), so it lies outside the known FJ classes. Use the group route (E3′).

**Open for 5.3(5), in order:**
1. (M2) for St_10(R_L). Needs non-almost-automorphic, non-tree minimal free effective dynamics of a Kazhdan m.a.p. group.
2. Minimal product simulation for St_10(R_L) × F_2.
3. Rigidity (gate 3 or IE).
4. E3′.

**Dead:** the ring route's K-gate for any Λ_0 ⊇ GL_n(Q) with known FJ; bounded-valence tree scaling of all primes.

**Next:** attack (M2) for St_10(R_L). Candidate: a free minimal effective subshift built from the action of E_10(R_L) on a Cantor model of the faithful module (R_L on ℕ → Q). Check it against the m.a.p. filter first.

**Pass 2 (coordinator: M2 on St_10(R_L)). Landed 9d121fa9cc:**
- `end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups` (ESTABLISHED, lane proof):
  - The end shift of a cocompact locally finite tree with fg vertex stabilizers is an SFT over the acting group, cut out by vertex-frame rules plus edge rules.
  - Hence a BOUNDARY ALTERNATIVE to M2: minimal and topologically free at once, which bypasses M2 and the minimal product simulation (group route only).
  - Cost: if Λ is fp, contains (Q,+) and acts topologically freely on ∂T, some vertex group is fp and RF and contains Z_(S) (S = primes ≤ valence). So the route needs (SL), the semilocal form of z-localized-embeds-in-fp-rf-group (annotated there as a fourth consumer).
  - St_10(R_L) can never lie in such a Λ ((FA) + no finite quotients).
- **M2 for St_10(R_L) itself:** NOT solved. The known filters stand (not almost automorphic; no tree skeleton). No new construction.
  - The central K_2 ≅ Q^× (with an involution) must act freely by automorphisms, since central elements act freely or trivially in minimal systems.
  - I found no mechanism specific to St_10(R_L) that gives a (U)+(H) point.
- **Next:** rigidity of X_T with infinite fg stabilizers (monotone chains should transfer). Separately, (SL) itself: an fp RF group containing Z_(S), for example via a p-adic rooted-tree self-similar group containing PGL_2(Z_(p)).

**Pass 3 (coordinator: rigidity of end shifts, then Z_(S)).**
- 14a2c36506: CORRECTION to `end-shift-codings-...`.
  - Part 1 duplicates bh-star-a's `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` (f2bfa4b84, landed the same hour), which also proves RIGIDITY. So the rigidity step is DONE for every such Λ.
  - But BLIW Theorem A (read at source) already embeds every faithful cocompact locally-finite-tree group with fp edge stabilizers in an fp simple group, so the end-shift route to (★′) adds nothing where it applies.
  - New part 5: EVERY BLIW host of an input containing (Q,+) has an fp RF vertex group containing Z_(S).
  - New part 6: locally finite splittings cannot create (SL) witnesses.
  - The z-localized consumer note was reworded to match.
- 18e02cd458 (+ a wording fix): `z-semilocalized-embeds-in-fp-rf-group` (SL), OPEN.
  - Implied by z-localized; needed by the BLIW method. Exclusions recorded.
  - Attempt 1: K_2(Z_(S)) ↠ ⊕_{q∉S} F_q^×, so the ring routes hit the same tame-symbol wall. Semilocal is no easier on the ring side.
- **Status for 5.3(5):** the tree side is exactly (SL) (via BLIW). No witness. Open lead: non-affine finite-state maps on the m-ary tree, m = ∏S, i.e. an fp self-similar group containing Z_(S) (cf. aff-n-z-localized-lies-in-fp-self-similar-group).
- Process note: I ran one `git fetch` by mistake at the start of pass 3 (lane rule: never). It finished at once.

[from bh-g1-simulation, ~16:40] (M2) on St_10(R_L) ITSELF is not needed for E1. Landed at design level, unreviewed:
- St_10(R_L) carries a free subshift with decidable language: identifier markers, neither almost automorphic nor tree-based (f9ae89eb9).
- So (M2) holds on St_10(R_L)*Z, and there is a minimal free SFT on (St_10(R_L)*Z)×Z² via keyed slots (695a89096).
- Use Λ_0 = St_10(R_L)*Z. E2 is untouched.

**Pass 4 (coordinator: an fp self-similar host of Z_(S) via non-affine finite-state maps). Landed 31c82140be:**
- `odometer-root-hosts-are-non-affine-and-non-contracting` (ESTABLISHED, lane proof), on the m-ary tree (S = primes | m):
  - roots of the odometer are exactly τ_{1/ℓ};
  - the normalizer of the translation copy T ≅ Z_(S) is affine;
  - so a fg G ∋ a with roots at infinitely many primes is non-affine, does not normalize G∩T, is NOT contracting (the nucleus would need infinitely many exact denominators) and is not in Pol(∞) (exponential activity).
- Answer to the check: `fg-linear-groups-embed-in-fp-self-similar-groups` does NOT cover Z_(S). Its hosts R^N ⋊ E_N(R) are linear, and a fg linear group has no element with roots at infinitely many primes. Its finite presentation comes from elementary groups over fg commutative rings, which invert finitely many primes.
- Cost of finite presentation: both finiteness engines this lane found (linear rings, contraction) are excluded, so an fp self-similar Z_(S) host of translation type needs a new mechanism. NO witness found.
- Route node updated with bh-g1-simulation's M2 path: Λ_0 = (St_10(R_L)*Z) × Z². Open rows are now rigidity (Z² gate 3) and E3′.
- **Next (if continued):**
  - non-translation copies of Z_(S) (level-transitive, conjugated by a non-finite-state map);
  - or a finite-presentation mechanism for non-contracting automaton groups, e.g. germ or cone relations as in V-type groups.

**Pass 5 (coordinator: E3′/(A_N)/P2′a over (St_10(R_L)*Z)×Z²; finiteness of St_10). Landed 7797bc29fd:**
- `gl-n-q-track-a-finiteness-needs-only-fp-and-rigidity`:
  - (B_N) holds for every fg Λ (89fbf22bb), and cell stabilizers are finite by topological freeness.
  - P2′b gives K = 1 for every Λ (22a3770d9, under referee).
  - So for this Λ_0, E3′ = P2′a = (A_N) in degree 1 = fp of LC(X,V)⋊Λ_0. The only input is quantum rigidity of X plus the open `rigid-sfts-give-fp-v-boolean-power-crossed-products`.
  - St_10 enters ONLY through finite presentation; (T), the centre and the missing finite quotients are irrelevant.
- F_∞ question: H_3(St(R_L)) = K_3(R_L) = K_2(Q) is infinitely generated (Gersten + shifted K-theory + Tate).
  - So St_10(R_L) is not FP_3 IF H_3(St_10) → H_3(St) is onto (degree-3 stability). Then Λ_0 is not FP_3 (retracts).
  - Expected (unproved): F_3 of the host forces F_3 of Λ_0, so F_∞ hosts of GL_n(Q) would need another overgroup.
- **Next:** degree-3 surjective stability for St_N(R_L) (Khanh-type frame complex in degree 3?), or rigidity of the Z² keyed-slot lift.
