# Referee report (gq-referee-a, proof-gap lens): central-deformation Euler host, Attempts 6–9

**Reviewed:** Attempts 6–9 of the OPEN node `central-deformation-euler-host-has-fng-steinberg-residual` (lane gq-k2-q),
read on origin/main (cec484d63), on the coordinator's request.

**Verdict: PASS.** Every claim marked proved in Attempts 6–9 is correct. I found no gap that would change the lane's
decision.
- N1 supplies a proof for the one Attempt 6 sentence that was stated without one, "only `b_k^r` stay torsion-free".
- N2 makes Attempt 7's injectivity argument work at the finite level.
- N3 notes that "the stable `K_2(T_p)` is finite" in Attempt 9 depends on the unread Berrick–Keating theorem.
- The Dennis–Stein detector remark and the Farrell heuristic are marked as heuristic. Quillen and NK-vanishing for
  regular `D` are for the citation lens.

## Preliminary: `u` is central in the lamp subring
- `b_k u = x^k b x^(−k) u = x^k b (u − kl) x^(−k) = x^k (u − kl) b x^(−k) = u b_k`.
- `b_kπ_k = π_k b_k = x^k p x^(−k) = p`. ✓

## Attempt 6: the positional relations
- *`u` times a word.* `u·w = b_(k_1)⋯(u b_(k_i))⋯ = p(w∖i) − (1 + k_i l)w`, because `u` and `p` are central in the
  lamp subring.
- *Positional relations.* Equating two positions gives `p(w∖i − w∖i') = (k_i − k_(i'))l·w`. ✓
- *`p[b_j,b_k] = 0`.* Take `w = b_k b_j b_k` with `i = 1`, `i' = 3`. ✓
- *The other annihilators.*
  - `π_j[b_j,b_k] = p b_k − b_k p = 0`, and likewise for `π_k`.
  - The `r = 2` case gives `(k−j)l[b_j,b_k] = 0`, as in Attempt 3. ✓
- *The span over `Z[p]`.* Positive-degree elements are spanned by lamp words, because `u` is eliminated letter by
  letter. ✓
- **N1: "in `B/(p)` only the powers `b_k^r` stay torsion-free".** The torsion of mixed words follows from the
  positional relations. The torsion-freeness of `b_k^r` needs a model. Here is one:
  - Let `u` act on `⊕_(j∈Z) Z[β] e_j` by `−1 − jl`, let `x e_j = e_(j+1)`, and let `b` be `β` on `e_0` and 0 elsewhere.
  - All relations hold with `p = 0`:
    - `bπ_0` vanishes, since `π_0 = −jl` on `e_j`;
    - `b` is diagonal, so `bu = ub`;
    - `xux^(−1) = u + l` on each `e_j`.
  - `b_k = x^k b x^(−k)` acts by `β` on `e_k`, so `b_k^r` acts by `β^r` and is not torsion.
  - Add this, or soften the sentence.

## Attempt 7: `B ⊗ Q` and the torsion kernel
- *Rationally the lamps commute.* `(k−j)l` is invertible in `Q`. So the lamp subring of `B⊗Q` is a quotient of
  `S = Q[u,p,b_k]/(b_kπ_k − p)`. ✓
- **The domain claim covers every finite piece (the coordinator asked about this).** Fix a finite `K`, and eliminate
  `p = b_(k_0)π_(k_0)`.
  - Over `Q`, two lines `π_j = 0` and `π_k = 0` never meet, since `π_j − π_k = (j−k)l ≠ 0` in `Q`. So at each point at
    most one `π_k` vanishes. There the others are units, forcing `b_j = 0` for `j ≠ k` and leaving the line `E_k`.
  - `E_k` lies in the closure of the surface `b_k = p/π_k`: let `u → −1−kl` with `p = βπ_k`. So `Spec S_K` is
    irreducible of dimension 2.
  - The ideal has `|K| − 1` generators and height `(1+|K|) − 2`. Unmixedness in the Cohen–Macaulay ring
    `Q[u, b_K]` makes it a complete intersection. So `S_K` has no embedded primes.
  - `S_K[1/Ππ_k] = Q[u,p][1/Ππ_k]` is reduced, so `S_K` is reduced (`R_0 + S_1`), and hence a domain.
  - This holds for every finite `K` and every `l`. `S = colim S_K` is a directed colimit of domains, so it is a
    domain. ✓
- **N2: injectivity of `S → A_p ⊗ Q`.** "Domains of the same dimension" needs finite generation, and `S` is not
  finitely generated. Argue at the finite level instead:
  - `S_K → A_K` (the image) is a surjection of finitely generated domains of dimension 2, so its kernel is a prime of
    height 0, that is, 0.
  - Then take the colimit.
  - Alternatively: `Ππ_k^e·z = F(u,p)` for `z ∈ S`, and `u, p ↦ u, t` are algebraically independent.
- *`B⊗Q ≅ (A_p⊗Q)[x^±;σ]`.* `B = Σ_k L x^k`, and `Σ ℓ_k x^k ↦ Σ φ(ℓ_k)x^k` with `L⊗Q ≅ A_p⊗Q`. So the map is
  injective without a separate freeness argument. ✓
- *The kernel is exactly the `Z`-torsion.* The target is torsion-free, and the kernel dies in `B⊗Q`. ✓
- *`A_p[x^±;σ] ⊆ D[t]` is residually finite.* Evaluating `t ↦ n ∈ Z` is a ring map. A Vandermonde argument over the
  torsion-free `D` separates `f ≠ 0`, and `D` is residually finite. So `B` is residually finite if and only if its
  torsion is separated. ✓

## Attempt 8: the two Baumslag-letter no-go computations
- *On `M`.* `p` is central and kills `m_0 − pm_0`, so it acts as 1. So `b_kπ_k = π_k b_k = 1`, and the `b_k = π_k^(−1)`
  commute.
- *The additive letter.*
  - `y(b_0)y^(−1) = b_0 + b_1 = (2π_0 + l)/(π_0π_1)`, which is invertible, being a conjugate of `b_0`. So `2π_k + l` is
    invertible on `M`, and `yπ_0y^(−1) = h(π_0)` with `h(a) = a(a+l)/(2a+l)`.
  - `xy = yx` gives `x(yuy^(−1))x^(−1) = yuy^(−1) + l`, that is, `h(π_1) = h(π_0) + l`.
  - `h(a+l) − h(a) = 2l(a+l)²/((2a+l)(2a+3l))`. So `l[2(a+l)² − (2a+l)(2a+3l)] = −l(2a² + 4al + l²) = 0` on `M`.
  - On `m_0`, `π_0 = 1`, so `l(2 + 4l + l²)m_0 = 0`. ✓
- *The multiplicative letter.* `yπ_0y^(−1) = π_0π_1`, and `yπ_1y^(−1)` is computed two ways:
  `π_0π_1 + l = π_1π_2`.
  - So `π_1·2l = l`, that is, `l(2π_1 − 1)M = 0`.
  - On `m_0`, `π_1 = 1 + l`, so `l(1 + 2l)m_0 = 0`. ✓
- Both computations are correct. They exclude these two letters, as the node says, and the "Why" paragraph is an
  explanation, not a claim.

## Attempt 9: the grading and homotopy
- *The splitting.* Every generator has `b`-degree at least 0 and every relation is homogeneous, so `B_+` is an ideal.
  - `B_0` is presented by the degree-0 relations only, since products involving degree-1 relators have positive
    degree. So `B_0 = Z[u][x^±;σ]`.
  - `B → B_0` is split by the inclusion. So `K_n(B) → K_n(B_0)` is surjective for all `n`, and
    `K_2(B) = K_2(B_0) ⊕ K_2(B, B_+)`. ✓
  - `|K_2(B_0)| ≤ 4` by ABC, as in Attempt 4.
- *`K_2(B,B_+)` dies where `p` is a unit.*
  - `B[p^(−1)] ≅ D[t^±]`, with inverse maps `π_k^(−1) ↦ p^(−1)b_k`, `t ↦ p`, and `φ` extended by `p^(−1) ↦ t^(−1)`.
    The lamps commute because `p[b_j,b_k] = 0`.
  - `φ(B_+) ⊆ tD[t]`, and `K_2(D[t], tD[t]) = NK_2(D) = 0` for regular `D`. So `K_2(B,B_+)` maps to 0 in `K_2(D[t])`,
    hence in `K_2(D[t^±])`, and hence in `K_2` of every finite quotient where `p` is a unit, since those factor
    through `B[p^(−1)]`. ✓
- *The `p`-nilpotent quotients.* `p^n = 0` and `p = 1` on `M` give `M = 0` there. ✓
- *The grading homotopy.* `τ(b_d) = b_d t^d` is a ring map, with `ev_1τ = id` and `ev_0τ = (B ↠ B_0 ⊆ B)`.
  - If `NK_2(B) = 0`, then `K_2(ev_0) = K_2(ev_1)` on `K_2(B[t])`. So the identity and the projection agree on
    `K_2(B)`, and `K_2(B,B_+) = 0`. ✓
- **N3.** "The stable `K_2(T_p)` is finite" follows only with `K_2(T_p) = K_2(B) ⊕ K_2(Z)`, the Berrick–Keating
  triangular theorem, which the node itself marks unread in (C2). Without it, only the summand `K_2(B) ⊕ K_2(Z)` is
  known to be finite. Say so there.

## For the lane's parking decision
Nothing here fails. The open questions are the ones the node already names:
- residual finiteness of the `Z`-torsion of `B`;
- `NK_2(B)`, or the part of `K_2(B,B_+)` that dies in every finite quotient of every `B/(p^n)`.

N1's representation shows that the `p`-fibre has non-torsion positive-degree classes, the `b_k^r`. So `B/(p)` is not
torsion in positive degree, and a detector in characteristic 0 on the fibre exists at least for these classes.
