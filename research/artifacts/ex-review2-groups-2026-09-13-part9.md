# EX review, wave 2, part 9: Theorem Q, Labbé small-growth models, the bounded-factors direction, Radu's second tree (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at the live tip after the coordinator restart
(blobs rechecked with `exshow.sh` before landing). The coordinator's queue numbering is kept.

| item | verdict | section |
|---|---|---|
| (1) near-scalar Lemmas 2.1, 3.1, 4.2(ii), 4.3 | PASS (earlier) | part 7 §1, part 8 §1 |
| (2) free-wreath counterexample pair and induction theorem | PASS (earlier) | part 5 §3, part 8 §2 |
| (5) Theorem Q, `zd-derived-full-group-fp-forces-quantum-rigidity` | PASS at the checked steps; certificate reproduced | §1 |
| (3) Labbé Theorems A and C | PASS | §2 |
| (4) bounded-factors (iii) => (i) | PASS | §3 |
| (6) radu chain-lamp nodes | derivations PASS; the 2-adic numerics are evidence, not proof: GAP | §4 |

## 1. Theorem Q: PASS at the checked steps

**Lemma NC, rerun.** `experiments/labbe-relation-climbing/idealcert.py` from main (md5 `6785fd21`), Sage 10.7 Python on MSI:

```text
terms: 17 verified PQ-QP = sum: True
primes in denominators: [3, 5]
relation sets used: ['r', "r'"]
```

`idealmodp.py` gives membership mod 2, 7 and 53 and non-membership mod 3 and 5 for multipliers of length up to 4. This
matches the artifact's §4.

The code:
- The words are reduced alternating words in `T = k<P,Q | P^2 = P, Q^2 = Q>`.
- `a = I + P(α - I)` with `a^(-1) = I + P(α^(-1) - I)`, which I checked.
- `[x,y] = x^(-1)y^(-1)xy`.
- The certificate is verified by recomputing `Σ c·w_1 g w_2` exactly and comparing with `PQ - QP`, so the conclusion does
  not depend on the elimination code.

**Consequence.** If `[a,b]^3 = I` and `[a,b']^3 = I` on `W ⊗ k^5`, every entry of both relation sets vanishes on `W`. So
the ideal does, and `PQ = QP` when `char k ∉ {3,5}`.

**Steps 1--5, re-derived at step level.**
- *Step 1.* On a site `w`, `ρ(Û_s)` keeps `1 - Σ_b E_σ(w-b)` and pulls from the triple. Overlapping triples have
  `E_σ(c)E_σ(c') = 0` by `R_1'` and (Q3).
- *`I(2D)`.* An `ℓ_1`-diameter `<= 2D` set has sup-diameter `<= 2D`, so it lies in a translate of `B_D`, and (Q2), (Q3)
  apply.
- *Step 2.* Unintended factor pairs meet through cores at offsets `<= 4`. Moving a core past the other coefficient costs
  commutation at distance `<= ρ + R_1' + 4 <= d`, because `d >= 2(R_1' + 8)` gives `ρ <= d/2 <= d - R_1' - 8`.
- *Step 3, domains.*
  - Ball case: `|u - h|_1 = d = 2ρ`.
  - Domino case: `Δ_b - Δ_a = B_1(2ρ) + {0, h, 2h}` has norms `<= d + 1`, and `|u - 2h|_1 = 2ρ` for a coordinate with
    `|u_i| >= 2`.
  - Internal differences are at most `d`.
- *Step 3, disagreement.* Patterns disagreeing on the overlap multiply to 0 with no cross-commutation, by ordering each
  product with the overlap site last or first.
- *Step 3, the local model.*
  - `Q_tot = Q + Q_S = E_(p|overlap)`, using (Q1) on `Δ_b \ Δ_a` and `I(d)(b)`.
  - On the range of `E = ΠQ_tot`, `b'` has coefficient `1 - Q`.
  - `P = EP` and `Q = EQ`, since the core of `p'` at `c` lies in the overlap once `ρ >= R_1' + 1`. So
    `PQ - QP = E(PQ - QP)E = 0`.
  - The orientation labels can always be chosen so that both cycles read `(0 1 2)` and `(0 3 4)`.
- *Step 4.* Orthogonal commuting idempotents with `E_1 + E_2 = 0` both vanish.

**The peer import `zd-derived-full-group-fp-forces-finite-type-proof`** (ex-fp-simple-relation-climbing, unreviewed until
now): PASS on Lemma 0, Lemma B and Corollary C.
- Case (i): the offsets `a' - b'` with `a' ∈ {0, ±e}`, `b' ∈ {0, h, 2h}` are nonzero off `(0,0)` and have norm `<= 3`.
- Case (ii): `b' ∈ h + {0, ±e^⊥}`, and `a' = b' = h` is the only coincidence.
- Both patterns contain `q|B(R_1)`, because `r >= R_1 + 1`.
- Lemma A (ChJN) is taken from the owner's source reading.

## 2. Labbé Theorems A and C (`ex2-labbe-lef-crux`): PASS

**The import.** Matte Bon, arXiv:1801.10133, PDF **Theorem 6.1** (the TeX label `t-confined` in the artifact), verbatim:
- the hypothesis is "G is a minimal effective étale groupoid over a space X which is either a Cantor space or a locally
  compact Cantor space";
- (ii) says H is confined by A(G);
- (iii) says there is a unique finite `Q ⊂ X`, possibly empty, with `St0_A(G)(Q) ≤ H ≤ St_F(G)(Q)`.

Labbé's shift is infinite, minimal and free, so its groupoid satisfies the hypothesis.

**Lemma 1.1.** `c_g(x) = 0` by freeness, and continuity of the cocycle gives a fixed neighbourhood.

**Lemma 1.2.**
- The disjoint 3-cycle moves supported in `U_i` send `x_i` along syndetic return sets.
- `a_u` fixes `U_2`, and `b_w` fixes `U_1`.
- The pairs `(σ^u x_1, σ^w x_2)` are distinct, so the orbit of the pair grows at least like `k^4`.

**Theorem A.**
- *Confinement.* A non-confined `H` gives, for each `k`, a vertex with `|B_k| = |B_k(Γ)|`. So Γ has polynomial growth,
  hence is virtually nilpotent (Gromov), hence residually finite. That contradicts Γ infinite simple.
- *`|Q| >= 2` is impossible.* The equivariant surjections `Γv -> ΓQ <- Γ(ordered Q) -> Γ(x_1, x_2)` give
  `|B_k(v)| >= c k^4/q!`.
- *`Q = {x}`.* Lemma 1.1 gives `H = St(x)`.

**Corollary B.**
- `n`-exactness puts `g^(-1)wg` in every limit stabilizer, because `w` fixes `gv_i ∈ B_(n_i)(v_i)`.
- Growth passes to the limit, and ball types are locally constant in `Sub(F(S))`.

**Theorem C.**
- *Chart lemma.* By compactness, with the 3-cycle on `D, σ^e D, σ^(2e) D` separating stabilizers.
- *The moves.* `T_e` is well defined, since `r_* - L >= r_1(R_2)` puts the next chart inside the known ball. The moves
  are bijective and pairwise commuting, because both words have length `<= 2L` and end at `σ^(e_1+e_2)x`.
- *Periodicity.* `y(u) = χ(T^u v_0)(0)` is legal on every edge, invariant under a finite-index lattice, and so periodic.
  That contradicts aperiodicity.

**Corollary D.** Checked at outline level (torus growth `<= 9R^2k^2`, and (H2) forces a moved point).

**Citation note.** Cite the printed Theorem 6.1 alongside the TeX label.

## 3. Bounded factors, (iii) => (i): PASS

- **As numbered on `fp-simple-weak-soficity-is-finite-field-linear-soficity`.** (iii) => (i) ("not weakly sofic" =>
  "not linear sofic over finite fields") is immediate: the normalized rank length is bi-invariant on the finite groups
  `GL_n(F_q)`. Part 8 §3 covered this.
- **The load-bearing direction named in the lane's report.** "Weak models into `PSL_n(q)` force linear soficity" is the
  PSL dichotomy's (i) => (ii) => (iii). Re-derived from `simple-group-psl-width-is-finite-field-linear-soficity-proof`:
  - *§4.* A relator with `ρ(h) >= ηn`, the class bound (2.1), and Liebeck--Shalev with `k_1 = ⌈2c/η⌉`.
  - *§5.2.* `W = I + C` is `b`-invariant, and `W'` is a complement of `W ∩ U` in `U`.
  - *§5.4.* `det [[0, -σ^(-1)], [σ, 0]] = 1`, and `[h_0, y] = h_0|W ⊕ σh_0^(-1)σ^(-1) ⊕ 1` with rank `2t`.
  - *§5.5.* Both branches give `2td >= δ_0 d^2/(4|X|D)`. `[ũ, ṽ] = [u(a), v(a)]` on `W'''`, and (Z) gives
    `Cons_(4k_2)`.
  - *§6.* (ii) => (iii) by `l(a_x) <= K max_r l(r(a))`.
- This agrees with `ex-review-backlog-2026-09-13-part5.md` §14, which checked the same steps.

## 4. Radu chain-lamp nodes

**`free-kernel-tree-actions-embed-in-free-generalized-wreath`: PASS.**
- *The covering.* Λ acts freely without inversions, so `T -> Y` is a covering and is locally injective on stars.
- *The cocycle.* It follows from reducing edge paths to geodesics.
- *Item 1.* A non-backtracking geodesic projects to a reduced word in `F_Y`, which is trivial only if `gv_0 = v_0`.
- *The target embedding.* `e ↦ z_e z_ē^(-1)` over one orientation per edge is part of a free basis (Nielsen), and it
  commutes with reversal.
- *Item 2.* `H_1(Y) = Λ^ab`.
- *Item 3.* GKP Theorems 3.6 and 3.7, with orbitwise soficity.

**`sofic-set-actions-pass-to-finite-fibred-quotients`: PASS.**
- GKP Proposition 2.9 (PDF p. 5) is verbatim the ultraproduct characterization used.
- The `j`-subset model has defect `<= jδ + O(1/n)`.
- Disjoint fibres with pairwise distance 1 give disjoint subsets for `U`-almost every `n`.

**`radu-xz-slab-is-second-tree-edge-stabilizer`, `radu-edge-stabilizer-is-second-prime-congruence-subgroup`,
`radu-horizontal-sign-is-local-action-on-second-tree` (ex2-radu-superstrong-negative): GAP.**
- *The derivations from the computed local actions: PASS.*
  - `S = H_Q·Stab_S(base_h)` with `Stab_S(base_h) = D_2 ⊆ H_Q`.
  - `ψ' = sgn_6` agrees on generators.
  - The indices: `[Fix_Q(p) : C] = 6`, since `C` is simply transitive on `V(T_h)` and the vertex stabilizer is `S_3`;
    `[Fix_Q(p) : E] = 3`; so `[E : C] = 2`.
  - `C = ker sign_q`, `C_χ = Fix_Q(N(e'))`, and these are compact open intersections.
  - The Zappa--Szép split `K = C_χ ⊔ xzc·C_χ`, and the framed-vertex double cover.
- *The local actions themselves are fixed-precision numerics.*
  - `radu-second-tree-check.py` evaluates exact elements of `F` at the second place through a Hensel approximation of
    `w` modulo `2^71`. It then runs exact rational arithmetic on those truncated values, including divisions by `2`,
    by `2A_2` and by a small-valuation minor `dmin`.
  - Tree distances are `v_2(det N) - 2 min v_2(N)`. Scalar and proportionality tests use a valuation threshold `BIG//2 = 29`.
  - No precision is tracked. The observed valuations are `<= 10`, against about 70 bits, and two independent scripts
    agree. So the combinatorial output is very likely correct, but the scripts do not prove it. The nodes say so
    themselves ("not symbolic proofs").
  - The character screens at small primes are context only, as the route says.
- *Repair.*
  - Recompute the local actions with rigorous precision, either in Sage `Qp` with tracked capped-relative precision or
    by exact integral arithmetic in `O_F/2^k` without division. Then record the certified valuation margin.
  - Alternatively, derive `C ⊆ Fix(p)` and the star permutations symbolically, for instance from the automaton on `Y`,
    which already gives the fibre combinatorics but not that `C` fixes `p` itself.
- Until then these three nodes are evidence-backed, and review lines saying so were landed on them.

## 5. Owners messaged

- ex2-labbe-relation-climbing: Theorem Q PASS.
- ex2-labbe-lef-crux: PASS, with the Theorem 6.1 number.
- ex2-radu-chain-lamp-positive: GAP on the slab and congruence nodes, with the repair.
- ex2-radu-superstrong-negative: GAP on the horizontal-sign node.
