# EX review, groups: part 2. Sweep for false establishments, the VTF chain, the unique-product dichotomy, norm quantization

Lane `ex-verify-groups`, 2026-09-12, 23:25 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 2.0 Sweep for false establishments (all landings of the 24 reviewed lanes to ~23:05)

**Method.**
- `git archive` of every top-level `research/*.md` at tip `a49eed562`, 19,697 nodes.
- An awk index of `kind`, `target`, `requires` and `invalidates`.
- A two-stratum fixpoint:
  - pass 1 kills every route named by any `invalidates`;
  - pass 2 kills a route only when an invalidator is established in pass 1.
- Calibration against FRONTIER at `ecea91ac0`. Every root ESTABLISHED there computes established, except
  `fpbs-ew-window`, a peer campaign's node. This is a local approximation of `cairn check`, which
  `ex-steward` runs on MSI. It is not a replacement.

**Results.**
- **No famous root of these lanes flipped.** Every root OPEN at baseline that these lanes target computes
  open in both passes. That covers Q3.4 either way, non-hyperlinear group, Pestov 9.1, left-orderable
  nonsofic, Thompson V/F, Bernoulli classification, positive Rokhlin entropy, nonsofic actions, determinant
  and Strong Atiyah, hyperbolic VTF, and Pi^0_2 cells. For Pestov 9.1 that is expected: the combining route
  was held at the time of the snapshot.
- **Flips outside these lanes, not reviewed here.** `spherical-artin-groups-satisfy-boone-higman` and
  `char-zero-linear-groups-satisfy-boone-higman` (peer bh-* campaign), and
  `simple-cstar-unitary-components-class-three` (reviewed by ex-verify-analysis). All three establish
  through live routes, and pass 1 = pass 2, so no dead route fires for them.
- **No dead route fires.** Pass 1 and pass 2 agree on all 8,067 established claims.
- **The three `requires: []` routes into famous roots are dead and killed.**
  - `determinant-conjecture-via-rational-character-models` is killed by
    `kun-thom-wreath-is-not-rational-character-approximable`, established through
    `hilbert-embeddable-witness-impossible`.
  - `left-orderable-non-sofic-via-relative-kazhdan-defect-criterion` is killed by
    `relatively-kazhdan-amenable-pairs-allow-sofic-defects`, whose proof is `requires: []`.
  - `mixing-nonsofic-action-via-permutation-centralizers` is killed by
    `permutation-centralizer-blind-to-weakly-mixing-actions`, whose proof is `requires: []`.
  - `leavitt-induced-absorption-gives-bernoulli-collapse` is killed by
    `finite-subgroup-induced-absorption-conserves-entropy`, established through the `requires: []`
    `lifted-trace-finite-subgroup-proof`.
- **Prose against routes.** Of the 157 claims these lanes landed, none says ESTABLISHED while computing
  open, and none says OPEN while computing established.
- **Spot checks of famous-looking landings.**
  - `thompson-f-is-not-sofic` (183c0f394e) is OPEN. Its only route requires the open
    `thompson-f-relator-system-stable-in-permutations`. Only the equivalence
    `thompson-f-sofic-iff-relator-system-unstable` is established; it is queued for review (§3).
  - `non-weakly-sofic-group-exists` (4d3da81924) is OPEN. Its route requires the open
    `fg-simple-weakly-sofic-groups-are-sofic`, so it does not fire. The other two requires,
    `countable-group-embeds-in-fg-simple-kazhdan-group` and `weakly-sofic-not-sofic`, compute
    established.
  - `every-hyperbolic-group-is-good` and `hyperbolic-groups-virtually-torsion-free` are OPEN.
  - `nonsofic-groups-satisfy-benjamini-schramm` is OPEN.

## 2.1 ex-hyperbolic-vtf: Chern–Quillen persistence (085e9f3d35, b76f42e6af). PASS

Claims: `chern-quillen-class-detects-all-prime-order-torsion`,
`vtf-iff-chern-quillen-class-dies-on-finite-index`, `good-cocompact-proper-groups-are-virtually-torsion-free`
and the OPEN `every-hyperbolic-group-is-good`. Re-derived:
- **Local family.** `ρ_F|_K = [F:K] ρ_K`, so `c̄(ρ_F)|_K = c̄(ρ_K)^[F:K]`, and
  `y_F = c̄(ρ_F)^(M/|F|)` restricts to `y_K`.
- **The value at `Z/p`.**
  - `Π_(i ∈ F_p)(1 + iβ) = 1 - β^(p-1)` from `Π(t + iβ) = t^p - β^(p-1) t`.
  - With `M/p = p^a m` and Frobenius, `y_P = (1 - β^((p-1)p^a))^m`.
  - Its degree-`n` part is `-m β^((p-1)p^a) != 0`, since `p ∤ m`.
- **Lifting.** Brown VII.7 gives the equivariant spectral sequence with `E_1^(0,t) = Π_v H^t(G_v)` and
  `E_1^(s,t) = 0` for `s > d`. It is multiplicative, because ordering the simplices of a subdivision
  gives an equivariant Alexander–Whitney diagonal. `d_1 z = 0` by compatibility.
  - `z` has even degree and is central, so `d_r(w^p) = p w^(p-1) d_r w = 0`.
  - The differentials leaving column 0 that can be nonzero are `d_2, ..., d_d`. So `z^(p^(d-1))`
    reaches `E_∞`, and a preimage `c ∈ H^N(G;F_p)` restricts correctly on every vertex group.
  - It restricts correctly on every finite subgroup, since each fixes a vertex.
- **(1 ⇒ 3).** A torsion-free finite-index `H` acts freely on the `d`-dimensional contractible `X`, so
  `H^q(H;F_p) = 0` for `q > d`. And `N = 2(p-1)p^(a+e) >= 2p^(d-1) >= 2^d > d`.
- **(2 ⇒ 1).** If `c` dies on `H_p`, then `H_p` has no element of order `p`. Intersect over the
  finitely many `p | M`; every torsion element has a power of prime order dividing `M`.
- **(G').**
  - `c^(p^k) = φ^* e` from a finite quotient, and `φ|_P` is trivial for `x ∈ R_f(G)`, so the
    restriction factors through `H^q(1) = 0`.
  - But `res_P c^(p^k)` is a nonzero power of `β`. So `R_f(G)` has no element of prime order.
  - Finitely many conjugacy classes of finite subgroups, each conjugate into a vertex group, then give a
    torsion-free finite-index normal subgroup.
- **(H)** is Wise, Proposition 9.2, as imported at baseline.

Verdict PASS. Notes:
- The title "Good hyperbolic groups are virtually torsion-free" is the hyperbolic instance of a theorem
  about any group with a finite proper contractible complex; the body states it that way.
- `vtf-iff-chern-quillen-class-dies-on-finite-index-proof` routes (2 ⇒ 1) through
  `finite-torsion-carrier-virtual-torsionfree-criterion`. The direct intersection argument above also
  works.
- The reduction "universal goodness ⇒ Gromov's question" is correct and is only a reduction:
  `every-hyperbolic-group-is-good` is open and at least as hard.

## 2.2 ex-left-orderable-nonsofic: unique-product dichotomy (ca9c9dd4c9). PASS

Claims: `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` (ESTABLISHED) and
`non-rf-hyperbolic-group-or-unique-product-nonsofic-group` (ESTABLISHED). The inputs
`hyperbolic-kazhdan-cover-of-leavitt-unit-group`, `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`
and `sofic-groups-kill-rigid-compression-defects` all compute established. Re-derived:
- **Deep normal subgroup.**
  - If `|gp - p| <= 4δ + 1`, then a vertex `h` within `1/2` of `p` gives `|h^-1 g h| <= 4δ + 2`.
  - A normal finite-index `G_k` missing the finite ball therefore has injectivity radius `>= 4δ + 1 > 4δ`.
  - Delzant's Proposition (C. R. Acad. Sci. 324, 1997, p. 382, quoted in the route) then gives unique
    products.
  - Note: Delzant's `δ` convention may differ from the Cayley-graph `δ` by a constant factor. The
    argument is insensitive to this, since residual finiteness lets `G_k` miss any finite ball. It is
    worth one sentence in the route.
- **The semigroup lemma.** If `P` generates `E` and `N ⊴ E` has exponent `e` quotient, then `p^e ∈ P ∩ N`,
  and `p s p^(e-1) ∈ P ∩ N` gives `p H' p^-1 <= H'`. So `H' = <P ∩ N>` is normal, every coset has a
  positive representative in `P`, and `N <= H'`. Checked line by line.
- **Non-normality.** `[Γ : u^j Γ u^-j] = f^j >= 2^j > [Γ : Γ_k]`, with `u^j ∈ E_k` and
  `u^j Γ_k u^-j <= Γ_k`. So conjugation strictly shrinks `Γ_k`.
- **Nonsoficity.** `z = e_o` centralizes `Γ_k`, and `[t z t^-1, γ] = e_(to) - e_(γto) != 0` for
  `γ ∉ tΓ_k t^-1`. This is a nontrivial rigid defect with `Γ_k <= E_k` Kazhdan and infranormal, which
  contradicts `sofic-groups-kill-rigid-compression-defects` as stated there, with `H = W`, `G = E_k`,
  `Γ = Γ_k`.
- **Unique products.** `L` is torsion-free abelian, hence orderable, and `W/L = E_k <= G_k`. The extension
  argument was re-checked: products over the uniquely expressed `c̄` are exactly `A_1 B_1`.
- **Kaplansky consequences.** Unique products give a domain. Trivial units need two unique products,
  which follows from unique products by Strojnowski (1980). The route says "the same argument shows"; one
  citation would close it.

## 2.3 ex-determinant-monster: norm quantization (11382c9376, cb7c47a89e). PASS

- **`integral-operator-norm-below-two-is-quantized`.**
  - The moments `τ(A^k)` are integers, since they are traces of identity coefficients. The Stieltjes
    transform is single-valued analytic off `σ(A)`, and `cap[-||A||, ||A||] = ||A||/2 < 1`.
  - Pólya's theorem makes it rational. The trace is faithful, so `σ(A)` is finite and Galois-stable.
  - Kronecker gives `2cos(2πa/b)`.
  - Orbit maxima: `2cos(π/b)` for odd `b`, attained at `k = (b-1)/2`, which is coprime to `b`; and
    `2cos(2π/b)` for even `b`. So `||A|| = 2cos(π/q)`.
  - Below `√2`, every orbit maximum is `<= 1`, the eigenvalues lie in `{0, ±1}`, `A^2` is a projection
    and `||A|| = 1`.
  - PASS. Novelty: a bounded check (Thom 2007, Lück 1901.00827); no all-groups statement found.
- **`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`.**
  - A ball of `Γ_A` is a connected finite principal submatrix of norm `<= 2`, hence a cyclotomic matrix.
    By McKee–Smyth Theorems 1–3 it is induced in `T_2k`, `C_2k`, a sporadic graph (`<= 16` vertices) or a
    `2 x 2` block, so it has `<= max(16, 4r+2)` vertices.
  - Left translation stabilizes components, acting freely with one orbit on each `C ∩ (G x {j})`.
    Švarc–Milnor and linear growth make `K_C` finite or virtually `Z`.
  - PASS at the level of these steps. The decomposition formula for `μ_A` was not re-derived line by line.

## Queue (priority 2, not yet reviewed)

`thompson-f-sofic-iff-relator-system-unstable` and its hyperlinear analogue;
`residual-finiteness-of-finite-presentations-is-pi2-complete` and `lef-of-finite-presentations-is-pi2-complete`;
`elementary-groups-over-infinite-rings-have-fixed-price-one`; `stable-finiteness-failure-is-algebraic-bernoulli-absorption`;
`rational-character-approximable-groups-obey-determinant`; the ex-q34-collapse block-monomial chain;
`amenable-orbit-full-group-subgroups-are-sofic` and `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`;
`howe-moore-lattice-nonsofic-action-transfers-to-mixing`; `paunescu-class-is-measure-equivalence-invariant`;
`simple-group-support-and-semisimple-rank-models-collapse`; `binary-leavitt-unit-group-is-l2-acyclic`.
