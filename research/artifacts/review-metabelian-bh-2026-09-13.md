# Review: every finitely generated metabelian group lies in the permutational Boone–Higman class

Lane `review-metabelian-bh`, 2026-09-13. This is an independent adversarial review of the candidate that lane `bh-metabelian` landed in f6aade283, b51c04469, e6f83e6c1, b1dd51dfa, 8c8f25fa6 and 5578e0b78. I wrote none of those nodes.

**Verdict: review PASS.**
- Every step of the chain holds.
- The landed theorem answers item (7) of BBMZ Problem 5.3 in full, and proves more: every finitely generated metabelian group lies in `B_A`.
- No node should get `invalidates:`. Five nits (§9) change no status.
- The novelty search is bounded (§7).

| # | Item | Verdict |
|---|---|---|
| 1 | BBMZ Problem 5.3(7) answered in full | PASS |
| 2 | `positive-char-polynomial-affine-groups-are-self-similar` | PASS |
| 3 | `elementary-groups-over-polynomial-f-p-rings-are-fp` | PASS |
| 4 | `char-p-linear-groups-embed-in-polynomial-f-p-groups`; route `char-p-linear-pbh-via-polynomial-self-similar-hosts` | PASS |
| 5 | Products inside `B_A` | PASS, one attribution nit (N1) |
| 6 | Quasi-linear claim and the metabelian route | PASS |
| 7 | Novelty and subsumption | PASS (bounded), subsumption nit (N3) |
| 8 | `cairn why` displays | PASS |

## Sources read for this review

- **BBMZ**, arXiv:2306.16356v3. Extracted text on MSI (`bh-outfn-mcg/2306.16356v3.txt`).
- **Zaremsky**, arXiv:2405.09722. Extracted text on MSI (`bh-reviewer/2405.09722.txt`), l.109–111.
- **Zaremsky**, arXiv:2405.18354. PDF pages 14–18, read locally from `bh-type-a/2405.18354.pdf`.
- **BFFHZ**, arXiv:2503.21882v2. Extracted text on MSI (`bh-reviewer/2503.21882.txt`).
- **Weibel, *K-book*.** Chapter PDFs read locally from `bhcharp/`: III pp. 1–3, 38–39, 48 and V pp. 40–41.
- **Wehrfritz**, Canad. J. Math. 27 (1975), pp. 1355–1356, from `bhmeta/wehrfritz1975.pdf`.

## 1. The printed problem

**The problem.** BBMZ l.823–830: "Problem 5.3. Prove the Boone–Higman conjecture for: … (7) Finitely presented metabelian groups 9."

**Footnote 9.** l.839–841: "By a theorem of Baumslag and Remeslennikov, every finitely generated metabelian group embeds into a finitely presented one [4, 94]. Such groups have solvable word problem [5], though the same does not hold for solvable groups of derived length three [69]."

**Status in the survey.** Remark 5.4 (l.845–859) lists the items resolved since the survey was first written: (4) and (8) fully; (1); (2), (3) and (13) partially. Item (7) is not mentioned, so it is still open in v3.

**Why the theorem answers it.** Finitely presented metabelian groups have solvable word problem (footnote 9). The Boone–Higman conjecture for such a group asks exactly for an embedding in a finitely presented simple group, and the root proves that. The converse direction is automatic. So item (7) is answered in full.

**Stronger form.** `B_A` is closed under subgroups, so every finitely generated metabelian group is covered, in the permutational form (BFFHZ l.127–130).

## 2. The char-p host is self-similar

**Definition checked.** Zaremsky arXiv:2405.09722 l.109–111, verbatim: "Definition 2.1 (Self-similar). A subgroup G ≤ Aut(T_d) is self-similar if its image in S_d ≀_d Aut(T_d) under the above isomorphism is contained in S_d ≀_d G."

**Setting.** `R = F_p[s_1..s_k]`, `O = F_p[[u]]`, `G = R^n x| Γ` with `Γ = E_n(R)`, acting on `X = O^n x O^(k-1)` by `(g,b)·(v,a) = (g<a>v + b<a>, a)` with `P<a> = P(u, a_2, …, a_k)`. I re-derived every step without using the proof route.

1. **Action.** Each `ev_a : R -> O` is a unital ring homomorphism, and `g<a>` is invertible. So `G` acts by bijections, and the product rule is compatible.
2. **Tree.**
   - Iterating `x = x_0 + u x'` identifies `X` with the boundary of the rooted `p^(n+k-1)`-regular tree, whose level `j` is `X/u^jX`.
   - Coefficients lie in `F_p`, so `P<a> mod u^j` depends only on `a mod u^j`.
   - So every element and its inverse permute each level compatibly with the projections.
3. **Faithful.**
   - `s_1 -> u`, `s_i -> y_i` embeds `R` in `O[y_2..y_k]`, since `u` is transcendental over `F_p`.
   - A polynomial over the infinite domain `O` that vanishes on all of `O^(k-1)` is zero.
   - Apply this first to `b`, at `v = 0`, then to the entries of `g - I`.
4. **States.** Fix a first-level vertex `(e,α)` with `e ∈ F_p^n` and `α ∈ F_p^(k-1)`, and let `σ_α : s_1 -> s_1, s_i -> α_i + s_1 s_i`.
   - Then `σ_α(P)<a'> = P<α + u a'>`.
   - `σ_α(P) - P(0,α)` vanishes at `s_1 = 0`, so it is divisible by `s_1` in `R`.
   - With `c = g(0,α)e + b(0,α)` and `w = (σ_α(g)e + σ_α(b) - c)/s_1 ∈ R^n`, we get `g<α+ua'>(e+uv') + b<α+ua'> = c + u(σ_α(g)<a'>v' + w<a'>)`.
   - The parameter coordinate `α + u a'` is unchanged.
   - The state is `(σ_α(g), w)`. It lies in `G`, because the unital ring endomorphism `σ_α` sends `e_ij(r)` to `e_ij(σ_α(r))`.
   - The identification `(e+uv', α+ua') <-> (v', a')` is the same digit shift for every child, as the wreath decomposition requires.
5. **All children.** All `p^(n+k-1)` children are covered by one formula.
6. **No clash with the obstruction node.** `affine-self-similar-coordinate-rings-are-one-dimensional` assumes all of the following, and none holds here:
   - a domain of characteristic zero;
   - a digit tree of `O^n`;
   - constant coefficients.
   Here the characteristic is `p`, the tree carries `k-1` parameter coordinates, and the linear part varies with the parameter point. That node's own Scope lists "Affine groups acting on a tree with extra parameter coordinates" under "What it does not exclude".

PASS.

## 3. `E_N(F_p[s_1..s_k])` is finitely presented for `N >= max(4, k+3)`

Verbatim sources:
- **Weibel III, Remark 5.5.2 (p. 38):** "The kernel of St_n(R) → E_n(R) is written as K_2(n,R), and there are natural maps K_2(n,R) → K_2(R). If R is noetherian of dimension d, or more generally has sr(R) = d+1, then the following stability result holds: K_2(n,R) ≅ K_2(R) for all n ≥ d+3."
- **Weibel V, Theorem 6.3 (p. 40):** "If R is a regular noetherian ring, then the base change K(R) → K(R[s]) is a homotopy equivalence, so K_n(R) ≅ K_n(R[s]) for all n."
- **Weibel III, Corollary 6.1.1 (p. 48):** "K_2(F_q) = 1 for every finite field F_q."

The chain:
1. `F_p[s_1..s_j]` is regular noetherian. Applying Theorem 6.3 `k` times gives `K_2(R) ≅ K_2(F_p) = 1`.
2. `R` is noetherian of dimension `k`, so `K_2(N,R) ≅ K_2(R) = 1` for `N >= k+3`.
3. So `St_N(R) = E_N(R)`.
4. `R` is a finitely presented ring: generators `s_i`, with `p·1 = 0` and the commutators. So `St_N(R)` is finitely presented for `N >= 4`, by `steinberg-finite-presentation-and-kazhdan-theorem`.

**Not re-read here.** Two imports come through reviewed nodes: Krstić–McCool Theorem 3, and Weibel IV Cor. 1.7.1 identifying Quillen's `K_2` with Chapter III's. This is the same trust surface as the reviewed characteristic-zero node.

PASS.

## 4. The char-p embedding and the composition

**The embedding** (`char-p-polynomial-embedding-via-noether-normalization`). I re-derived every step.
1. **Restriction of scalars.** It gives an injective unital `M_N(K_0) -> M_(Nd)(F_p(t))`.
2. **Denominators.** `A = F_p[t][1/f] = F_p[t,u]/(uf-1)`.
3. **Nagata substitution.**
   - Put `s_i = t_i - u^(D^i)` with `D > max a_i`.
   - `u t^a` is monic in `u` of degree `1 + Σ a_i D^i`, and distinct `a` give distinct degrees.
   - So `uf - 1` has leading coefficient `c_(a*) ∈ F_p^×`, which is a unit. Hence `u` is integral over `P = F_p[s]`.
   - `A = P[u]` is finite over `P`.
   - The `s_i` are algebraically independent, since `F_p(t)` is algebraic over them.
   - The constant case `f ∈ F_p^×` gives `W = 1` and works too.
4. **Flat.** `A` and `P` are regular, and `P` is normal, so going down holds. The fibres have dimension `0`, so `dim A_q = dim P_p`, and miracle flatness makes `A` flat over `P`. Being finite over noetherian `P`, it is projective.
5. **Free.** It is free by Quillen–Suslin.
6. **Matrices.** Multiplication matrices give `Γ -> GL_(Ndr)(F_p[s])`.
7. **`k = 0`.** It lands in `GL_(Nd)(F_p)`.

**The composition** (`char-p-linear-pbh-via-polynomial-self-similar-hosts`).
- **Into `SL_N`.** `g -> diag(g, (g^T)^-1, I)` is an injective homomorphism into `SL_N`.
- **`SL_N(R) = E_N(R)` for `N >= k+2`.** Verbatim sources:
  - Weibel III, Remark 1.2.5 (p. 3): "if R has stable range d+1 then E_n(R) is a normal subgroup of GL_n(R) for all n ≥ d+2. Vaserstein proved [V69] that K_1(R) = GL_n(R)/E_n(R) for all n ≥ d+2."
  - Weibel III, Example 1.1.1 (p. 2): "K_1(R) = R^× ⊕ SK_1(R)".
  - Weibel III, Example 1.1.2 (p. 2): "If F is a field, then K_1(F) = F^×".
  - With Theorem 6.3 these give `K_1(R) = F_p^× = R^×`, so `SK_1(R) = 0`.
- **Finite presentation of the host.** `N = max(k+4, 2M)` satisfies both ranges, and `affine-extension-of-fp-elementary-group-is-fp` (reviewed) applies.
- **`B_A` for subgroups.** Part (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, which passed review in b5b808dc0.

PASS.

## 5. Products inside `B_A`

**Zaremsky arXiv:2405.18354** (PDF p. 15–16), verbatim:
- "Proposition 5.5. If two groups satisfy the permutational Boone–Higman conjecture, then so does their direct product." The proof uses the action of `G x H` on `S ⊔ T`.
- "Proposition 5.6. Let G be a group. If a finite index subgroup of G satisfies the permutational Boone–Higman conjecture, then so does G. In particular, satisfying the permutational Boone–Higman conjecture is a commensurability invariant."

**BFFHZ.** l.203: "PBH is stable under commensurability and direct products [Zarb]". l.806: "[Zarb, Proposition 5.6]" for commensurability.

**The graph's own proof.** `type-a-actions-closed-under-products-and-finite-wreaths` passed review in `review-backlog-2-2026-09-12.md` §19. I re-checked part (a) against the graph's definition of type (A):
- The action on the disjoint union is faithful.
- A product of finitely presented groups is finitely presented.
- Point stabilizers `Stab(s) x Γ_2` are finitely generated.
- There are finitely many orbits of 2-element subsets: within one part by hypothesis, and mixed pairs through finitely many point orbits.

PASS, with nit N1.

## 6. Quasi-linear groups and the metabelian step

**Wehrfritz 1975**, p. 1355, verbatim:
- "1.1 THEOREM. If the group G is a finite extension of a finitely generated metabelian group G_0 whose derived group G_0' is a p-group for some prime p, then G has a faithful representation of finite degree over some field of characteristic p."
- "A quasi-linear group is a group of matrices over a direct sum of a finite number of fields, its characteristic being the set of the characteristics of the ground fields. … by the characteristic of G we mean the set of prime divisors of the orders of the elements of G' of finite order, together with zero if G' is not a torsion group."
- "1.2 COROLLARY. If the group G is a finite extension, of a finitely generated metabelian group of characteristic π, then G is isomorphic to a quasi-linear group of characteristic π."

**Coverage.** Corollary 1.2 applies to every finitely generated metabelian group.
- `GL_n(K_1 ⊕ … ⊕ K_r) = Π GL_n(K_i)`, so this is exactly the hypothesis of `quasi-linear-groups-satisfy-permutational-boone-higman`.
- The route's own primary decomposition agrees:
  - `p`-power exponent pieces are covered by Theorem 1.1 ("a p-group");
  - torsion-free pieces by Remeslennikov, read through Wehrfritz's quote (N4).

**The quasi-linear route.**
- Each projection is a finitely generated linear group over one field, so it lies in `B_A` (§4, or the reviewed characteristic-zero claim).
- `G` embeds in the product, which lies in `B_A` (§5).
- Part 3 of `boone-higman-type-a-class-closed-under-finite-extensions` gives the finitely presented simple envelope.
- The open `boone-higman-closed-under-finite-direct-products` is never used.

PASS.

## 7. Novelty and subsumption

**Searched on 2026-09-13.**
- The arXiv listing for "Boone-Higman", all fields, newest first. All 17 results were checked; the newest is 2609.01868, on permutational wreath products. None is about metabelian groups, positive characteristic or soluble classes.
- Zaremsky's arXiv author page, 53 papers. No metabelian or positive-characteristic paper.
- Three web searches, covering metabelian BH, 2025–2026 permutational BH in positive characteristic, and Kochloukova–Sidki. The hits were 2405.09722, 2405.10234, 2306.16356, 2503.21882, 2309.06224, 2306.14863, 2408.05673, 2609.01868, 2509.05798 and 2603.14556.
- Previously quoted and still consistent: FFWZ arXiv:2603.24687v2 l.145–148 lists the known PBH classes without metabelian groups.

**Verdict: no prior answer found.**
- Not searched: MathSciNet or zbMATH.
- Kochloukova's arXiv author page returned 404.
- As the artifact says, a specialist may know the positive-characteristic host. No priority is claimed.

**Duplicate scan.**
- Checked the 17 nodes mentioning metabelian groups together with Boone–Higman. None is a duplicate.
- Now special cases of the new claims:
  - `global-field-soluble-linear-products-satisfy-boone-higman`;
  - `positive-char-linear-groups-satisfy-boone-higman`;
  - `positive-char-surface-linear-groups-satisfy-boone-higman`;
  - `baumslag-char-zero-metabelian-group-satisfies-boone-higman`.

## 8. `cairn why` on MSI

Snapshot of origin/main 0183c4b57, with missing non-research artifacts stubbed.
- **ESTABLISHED, every leaf ✓:** `fp-metabelian-groups-satisfy-boone-higman` (via `fp-metabelian-bh-via-quasi-linear-pbh`), `quasi-linear-groups-satisfy-permutational-boone-higman` and `char-p-linear-groups-satisfy-permutational-boone-higman`.
- **ESTABLISHED:** `positive-char-polynomial-affine-groups-are-self-similar`, `elementary-groups-over-polynomial-f-p-rings-are-fp` and `char-p-linear-groups-embed-in-polynomial-f-p-groups`.
- **Still OPEN, as expected:** `boone-higman-closed-under-finite-direct-products` and the old route `fp-metabelian-bh-via-linear-factors-and-products`.

## 9. Nits (no status change)

- **N1. Wrong proposition number.**
  - Where: `quasi-linear-groups-satisfy-permutational-boone-higman` (Credit) and `boone-higman-type-a-class-closed-under-finite-extensions` (Credit).
  - What: both cite arXiv:2405.18354 "Proposition 5.6" for closure under direct products. In the source, products is **Proposition 5.5** (p. 15) and 5.6 is commensurability (p. 16).
  - Effect: none, since the graph's closure proof is independent.
- **N2. Stale review lines.** The root and the four new nodes still say "Not independently reviewed", and so does artifact `bh-quasi-linear-pbh-2026-09-13.md` §6. Their owner should record this review.
- **N3. Subsumption.** The four nodes listed in §7 could each add a line saying the new claims subsume them.
- **N4. Trust surface.** Remeslennikov's characteristic-zero theorem is read only through Wehrfritz's quote. Wehrfritz's Corollary 1.2 itself relies on it.
- **N5. Trust surface.** Three imports are taken through reviewed nodes and not re-read here: Bass's bound `sr(R) <= dim R + 1` (implicit in Weibel III Remark 5.5.2's "or more generally"), Weibel IV Cor. 1.7.1, and Krstić–McCool Theorem 3.

## Separate note: a cairn check error that is not this candidate's

Lane `bh-metabelian` reported `cairn check` exit 4 at tip 82a047afd, on `relatively-simple-removal-via-twisted-product-actor` requiring `a2-kernel-removal-via-product-with-image-actor`.
- At 0c61b41d6 the required id is indeed a route (`kind: route`, target `a2-kernel-removable-iff-image-in-type-a2-actor`), so requiring it would be an error.
- I did not re-check the full `requires:` list, and I did not edit either node. It belongs to the product-closure nodes, not to this chain.
