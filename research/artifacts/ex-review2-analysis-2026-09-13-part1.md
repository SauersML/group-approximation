# EX review wave 2, part 1: the class-four chain and the depth limits of unitary brackets (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0.

**Landings reviewed.**
- ex-unitary-string-trapping: `2dc91dbfe6`, `91e5310614`, `70bd275443`, `cbbcd12588`, `93f1b42734`,
  `b3ad7449ee` and `5c0398225b`.
- ex-unitary-higher-brackets: `97882e595`, `344f59a964` and `2d7d577ab3`.

**Sources read.**
- `research/artifacts/class-four-lambda-mod-eight-trapping-2026-09-13.md` and its parts 2, 3 and 4.
- Every node and route named below.
- Toms arXiv:2609.09535v1 was **not** re-read here. The chain uses the same detector, recursion and limit
  lemmas that the first wave checked against pp. 5--22 of the PDF (`ex-review-analysis-2026-09-12-part1.md`,
  §1.2, Items 1 and 4): Lemma 3.1, Definition 3.2, Theorem 3.3, Proposition 4.2, Lemmas 6.2 and 6.3,
  Proposition 6.4 and Lemma 7.1.

## 1.1 Structure, and which roots flip

`simple-cstar-unitary-components-class-four` is established through exactly one live route:
- `class-four-via-lambda-mod-eight-trapping-tower` requires `simple-ah-algebra-with-class-four-component-group`.
- That claim's proof route requires four claims:
  - `trapped-lambda-mod-eight-class-over-seed-factor`, whose proof requires the Toms import;
  - `eta-cubed-commutator-has-nonzero-lambda-mod-eight-class`, requiring
    `u2-quadruple-samelson-class-four-stage` (PASS, first wave part 1 Item 5) and
    `eta-cubed-survives-in-lambda-mod-eight-bordism`;
  - `quaternionic-grassmannian-trapping-defect-is-rank`;
  - `toms-trapped-spin-bordism-class`, through its citation route.
- The new `requires: []` routes are proof routes with complete bodies:
  - `eta-cubed-lambda-mod-eight-bordism-proof` and `quaternionic-grassmannian-trapping-defect-proof`;
  - `commutators-ko-eta-powers-proof` and `quaternionic-flag-string-steps-no-go-proof`;
  - the peer's `rank-two-trapping-depth-four-stable-null-proof` and `spin-trapping-fourfold-blind-every-rank-proof`.
  None is a dead-route placeholder.

**Consumers.** A fixed-string `git grep` at `7d41d1a16` found exactly two routes consuming these claims.
- The class-four root route above.
- `nonnilpotent-via-glued-trapping-towers`, into `simple-cstar-unitary-component-group-not-nilpotent`. It also needs
  the open `trappable-unitary-commutator-seeds-of-every-depth`, so it cannot fire.

The second route into the class-four root, `class-four-via-non-nilpotent-component-group`, needs the same open
claim. No other root flips. The class-four root is a question built in this repository, not a named external
problem.

## 1.2 `eta-cubed-survives-in-lambda-mod-eight-bordism`: PASS

Re-derived.
- **Well-defined invariant.** For a framed L = ∂W with W spin, the framing trivializes λ(TW) on ∂W, so it
  defines λ(W, ∂W) ∈ H^4(W, ∂W; Z).
  - Two choices glue to a closed spin V, and the numbers differ by λ[V] = p_1[V]/2 = 3σ(V)/2.
  - Rokhlin gives 16 | σ(V), so 24 | λ[V], and e(L) ∈ Z/24 is well defined.
  - A framed bordism glued onto W is another choice, so e is a framed-bordism invariant. It is additive.
- **Normalization.** The Lie framing of S^3 differs from the bounding framing of D^4 by q ↦ L_q in π_3(SO).
  - The clutched bundle is the quaternionic line bundle γ over S^4. Here p_1(γ_R) = −c_2(γ ⊕ γ̄) = −2c_2(γ).
  - So λ = ±1 and e(ν) = ±1. Then e is an isomorphism π_3^s ≅ Z/24, and e(η^3) = e(12ν) = 12.
- **The mod-8 step.** Suppose a Spin_8-null-bordism W extends the framing structure on ∂W.
  - Its nullhomotopy of λ mod 8 restricts on ∂W to the reduction of the framing's integral trivialization.
  - The obstruction to extending it rel ∂W is λ(W, ∂W) mod 8 ∈ H^4(W, ∂W; Z/8). Hence 8 | e(L).
  - Since 8 ∤ 12, η^3 ∉ ker(π_3^s → Ω^8_3). The kernel lies in {0, 8ν, 16ν}.
- **Fibre bookkeeping.** The fibre of BSpin_8 → BO is built from Z/2, K(Z/2,1) and K(Z/8,3), so π_0 = Z/2. On a
  contractible base a structure is an orientation, and framings induce structures.

## 1.3 `trapped-lambda-mod-eight-class-over-seed-factor`: PASS

The generalization runs through each step Toms uses.
- **Normal bundle.** Left translation by g^{-1} identifies the normal space of D(E) at g with the off-diagonal
  skew-Hermitian block, which is W_R. This holds continuously in g (Toms Lemma 3.1).
  - So a transverse locus has T Z(v) ⊕ W_R|_Z ≅ TB|_Z. The splitting is a contractible choice, and
    σ_M ⊕ τ restricts to a well-defined structure on T Z(v).
- **Dimensions.** codim D(E) = dim u(2+r) − dim(u(2) ⊕ u(r)) = 4r = dim X. So dim Z(v) = m.
- **Invariance.** A transverse homotopy has locus 𝒵 ⊂ B × I with T𝒵 ≅_s (TB ⊕ R − W_R)|_𝒵. The same
  restriction structures it, compatibly at the ends. So Toms's proof of Theorem 3.3 goes through verbatim.
- **Values.** Perturbing by R_{εs} gives the loci M × Z(s).
  - On M × {ξ} the second summand of TM ⊕ (TX − W_R)|_ξ is a structured virtual bundle over a point,
    trivialized by εD_ξ s. That is an element of π_0(F) = Z/2, a sign.
  - So each copy carries ±σ_M. The signed count is <e(W_R), [X]> = <c_{2r}(Q* ⊕ Q*), [X]> = <c_r(Q)^2, [X]>.
- **Note, no verdict change.** Toms's f_v is ρ ∘ a_v, landing in SU(2). The rank-p version in Part 3 uses a_v,
  landing in U(2), and needs no ρ. Either convention works:
  - SU(2) is a retract of U(2) as a space, so Ω̃(SU(2)) is a direct summand of Ω̃(U(2));
  - det c_4 = 1.
  So nonvanishing transfers both ways.

## 1.4 `eta-cubed-commutator-has-nonzero-lambda-mod-eight-class`: PASS

- **Fat wedge.** c_4 = 1 when some s_j = 1, since α(1) = 1, and when z = 1, since the innermost bracket dies. So c_4
  factors through S^6.
- **The class.** [c̄_4] = ω∘η_3∘η_4∘η_5 by the first-wave PASS of `u2-quadruple-samelson-class-four-stage`. It is the
  unique element of order two in π_6(S^3) ≅ Z/12; the lane's "6ν′" means that element. It stabilizes to
  η^3 = 12ν ≠ 0.
- **The preimage.** A regular preimage L of y ≠ 1 lies in the open top cell U ≅ R^6.
  - On U every Spin_8-structure is an orientation, so L carries its framing structure up to sign.
  - Pontryagin--Thom then identifies [L] with the image of 12ν. It is nonzero by §1.2, and the sign is irrelevant
    in order two.

## 1.5 `quaternionic-grassmannian-trapping-defect-is-rank`: PASS

Recomputed.
- **Cells and count.** Cells of Gr_k(H^n) have dimensions 4|μ| with μ in the k × 2d box, so the space is
  3-connected and H^4 = Z·q_1.
  - Borel's presentation doubles the degrees of Gr_k(C^n).
  - Pieri adds a vertical k-strip to a partition with at most k rows, one box per row. So σ_{1^k}^{2d} = σ_{(2d)^k}
    is the point class, and <c_{2k}(ζ)^{2d}, [G]> = ±1.
- **Tangent bundle.** TG ⊕ Hom_H(ζ,ζ) = Hom_H(ζ, H^n) and Hom_H(A,B) ⊗_R C = Hom_C(A,B). With c_1 = 0,
  c_2(A* ⊗ B) = β c_2(A) + α c_2(B), which follows from ch_2 = −c_2.
  - This gives c_2(Hom_C(ζ, C^{2n})) = 2n q_1 and c_2(End_C ζ) = 4k q_1, so p_1(TG) = −(2n − 4k) q_1.
- **Detector bundle.** W_R ⊗ C = 2dζ* ⊕ 2dζ, so p_1(W_R) = −4d q_1.
- **Defect.** H^4 is torsion-free, so λ = p_1/2. The defect is −(2d − k) q_1 + 2d q_1 = k q_1.
- **Checks.** k = 1 reproduces p_1(HP^m) = 2(m − 1)u. Also dim_R G = 8kd = rank_R W, and w_2(W_R) = c_1(W) mod 2 = 0.

## 1.6 `simple-ah-algebra-with-class-four-component-group` and the root: PASS

- **Lemma 5.1.**
  - r_{i+1} = r_i + 16 d_i and dim X_{i+1} = 4r_i + 64 d_i = 4 r_{i+1}.
  - W_{i+1} = pr^*W_i ⊕ pr^*W_{G_i} and TX_{i+1} = pr^*TX_i ⊕ pr^*TG_i. So τ_{i+1} = τ_i ⊕ (Lemma 4.2 structure),
    using that λ mod 8 is primitive.
  - c_top(Q_{i+1}) = pr^*c_{r_i}(Q_i)·c_16(ζ_i)^{d_i}. Its square integrates to (±1)(±1).
- **Lemma 5.2.** Each evaluation summand w_i(z) ⊗ 1_ζ joins 1 through the connected U(V_{i,l}).
- **Lemma 5.3.** §1.3 at stage i, with X_1 = point and trivial τ_1, gives ν(w_i) = ±[T^3×S^3, c_4]_red ≠ 0 = ν(1).
- **Proposition 5.4.**
  - A nonzero positive a ∈ A_i is nonzero on an open set. Dense evaluation sets put some z ∈ F_j there.
  - The block φ_{i,j}(a)(z) ⊗ 1_{ζ_j} is nonzero in every fibre over Y_{j+1}. A section nonzero in every fibre
    generates Γ(End E) as an ideal, so it is full, and Toms Lemma 6.3 applies.
- **Theorem.**
  - The algebra is separable, unital, nuclear and AH by construction.
  - It is stably finite: a limit tracial state exists by compactness and is faithful by simplicity.
  - The class of c survives: if c ∈ U_0(A), Toms Lemma 7.1 would give some j with φ_{1,j}(w_1) ∈ U_0(A_j),
    contradicting Lemmas 5.2 and 5.3.
  - The extra properties hold: c^2 ≃ 1 because 2[c̄_4] = 0 and pointwise products realize the group law; [c]_1 = 0
    because c is a commutator; diag(c,1) ∈ U_0(M_2(A)).
- **Excess.** dim Y_i − 2 rank E_i = 2 + 2r_i ≥ 2, consistent with
  `block-component-group-class-at-most-excess-plus-two`.

## 1.7 `unitary-word-transfer-to-simple-ah-via-trapping`: PASS

- **Proposition 7.1.** codim D(E) = 2pr = dim X. The count is <e(W_R), [X]> = c_{pr}(p·Q*) = ±<c_r(Q)^p, [X]>.
  No ρ is needed: reduced bordism of U(p) subtracts the constant map, and invariance uses only the block map on
  the homotopy locus.
- **Lemma 7.2.** With n = k + pd:
  - λ(TG) = −(pd − k) q_1 and W_R ⊗ C = pdζ* ⊕ pdζ, so λ(W_R) = −pd q_1, and the defect is k q_1;
  - dim G = 4kpd = rank_R W, and Pieri gives σ_{1^k}^{pd} = [pt].
- **Theorem 7.3.** The tower is Part 2's, with protected block C^p and A_1 = C(M, M_p).
  - Words are computed pointwise, so φ_{1,i}(w(u)) = w(φ_{1,i}(u)) ≃ (f∘pr) ⊕ 1_{Q_i}.
  - The special case m = 1, p = 2 uses steps HP^{2d} = Gr_1(H^{1+2d}): dim 8d = rank_R W and the defect is q_1 ≡ 0
    mod 1.

## 1.8 Route `nonnilpotent-via-glued-trapping-towers` (Part 3, Proposition 9.1): PASS as a conditional route

- **Unital sums.** When the ranks have gcd one, every large integer is a nonnegative combination of them. So the
  auxiliary summands M_{a_{n+1}}, M_{a_{n+1}+1} and each entering C(M_c, M_{N_c}) (N_c ∈ S_c large) receive exact
  unital sums of evaluation blocks.
- **Injectivity.** T_c receives its own coordinate pullback. The matrix summands embed through nonzero
  evaluation blocks.
- **Simplicity.** Dense evaluations into every summand give fullness as in §1.6.
- **Persistence in T_c.** Evaluation blocks only add multiples of ζ to Q, so Lemma 7.2 applies with d the total
  block rank, and the count ±1 and the structure persist.
- **Survival.** The witness is (f∘pr) ⊕ 1 in T_c and 1 elsewhere. Its images elsewhere are constant blocks, which
  contract. Lemma 7.1 at a finite stage lands in ⊕ U_0(summands), and the T_c component is detected.
- The seed hypothesis is open and flagged as possibly false. The route does not fire.

## 1.9 `rank-two-trapping-blind-to-fivefold-sphere-commutators`: PASS

- **Reduction to Samelson products.** π_n U(2) = π_n S^3 for n ≥ 2, so every leaf is kα or ω∘h.
  - Samelson products are bilinear and natural under precomposition.
  - <α,α> = 0, and <α,ω> = ω∘η_3 by the prerequisite `u2-triple-samelson-class-three-stage`.
  - <ω,ω> generates π_6(S^3) = Z/12, with stable image y a unit multiple of 2ν.
- **Four brackets.** They give η^a y^b with a + b = 4, and every such product vanishes:
  - η^4 = 0 and η·ν = 0;
  - η^3 y is a multiple of 12ν^2 = 0;
  - y^4 ∈ π_12^s = 0.
- **Detection.** f = 1 off the open top cell. Under the hypothesis that the structure there is the framing
  structure, [M,f]_red is the unit image of the stable class of f̄. It lands in SU(2), a retract of U(2).
- This claim is contained in the peer's `rank-two-trapping-blind-to-depth-four-brackets` (§1.12), as the node says.

## 1.10 `nested-commutators-pull-ko-of-unitary-groups-into-eta-powers`: PASS

- **Lemma 10.1.** For primitive p in K^{-1}(U(N)): μ^*p = p⊗1 + 1⊗p and inv^*p = −p. So c^*p = 0 on G × G, hence on
  the split summand for G ∧ G. The map c^* is a ring map, and Hodgkin's exterior algebra is generated by
  primitives, so c^* kills all of K̃^*(G).
- **Proposition 10.2.** Künneth holds because K^*(G) is free, so the complexification of (1_X ∧ c)^*z is 0.
  - Wood's exact sequence KO^{*+1} →η KO^* → KU^* gives η z′ with z′ ∈ KO^{*+1}(X ∧ G ∧ G).
  - The induction uses (1_X ∧ c_j)^* = (1_{X∧G} ∧ c_{j−1})^* ∘ (1_X ∧ c)^* with X′ = X ∧ G. Pullbacks commute
    with η.
- **Corollary 10.3.** f = c_j ∘ (g ∧ ... ∧ h) ∘ Δ, and η^3 = 0 in KO_*. Mod 2, H^*(U(N); Z/2) is exterior on
  primitive classes, so reduced classes pull back to 0 once j ≥ 2.
- The node correctly claims no bordism blindness for N ≥ 3 by itself.

## 1.11 `quaternionic-flag-trapping-steps-are-never-string`: PASS

Recomputed.
- **Tangent bundle.** TF = ⊕_{i<j} Hom_H(ζ_i, ζ_j) and λ(Hom_H(A,B)) = −(b c_2(A) + a c_2(B)). So
  λ(TF) = −Σ_i (n − k_i) x_i = Σ_i k_i x_i, using Σ x_i = c_2(H^n) = 0.
- **Detector bundle.** λ(W_R) = −pΣ d_i x_i. The only degree-4 relation is Σx_i = 0, so the defect vanishes iff
  k_i + p d_i = t for all i.
- **Count.** e(W_R) = ±∏_i c_{2k_i}(ζ_i)^{p d_i}. If all d_i ≥ 1 it contains c_{2n}(H^n) = 0, so some d_s = 0 and
  k_s = t.
- **Dimension.** 2(n^2 − Σk_i^2) = 4(tn − Σk_i^2) gives Σk_i^2 = t^2 − m^2 with m = n − t ≥ 1. That forces
  Σ_{i≠s} k_i^2 = −m^2, which is impossible.

## 1.12 ex-unitary-higher-brackets: three PASS

- **`rank-two-spin-trapping-blind-to-depth-three-brackets`: PASS, one import not re-read.**
  - Σ^∞U(2) is a wedge of spheres, so KO^*(G ∧ G) = KO~(G) ⊗ KO~(G).
  - c^* kills the primitives a, b and their product ab in KU. So c^*z = η·Σ y_i ⊗ z_i, and the induction gives η^j.
  - In the fibre step, i_!(1) = f^*u and the projection formula kills every KO-number at depth three. x_3 is
    primitive mod 2 because H^2(U(2); Z/2) = 0.
  - Anderson--Brown--Peterson detection by SW- and KO-numbers is recalled; its theorem number is not re-verified
    (the node says so).
- **`rank-two-trapping-blind-to-depth-four-brackets`: PASS.**
  - Base case: components of s_2 lie in π^s_{d_1+d_0−3}. They are 0 for (1,1), η for (1,3), η^2 for (1,4), multiples
    of ν for (3,3), and 0 when both d ≥ 3 with one d = 4.
  - Induction: s_{j+1} = s_2 ∘ (1 ∧ s_j), with the S^3 summand equal to SU(2) under (z,g) ↦ diag(z,1)g. Each
    component gains a letter x_d ∈ π_d^s.
  - Four letters vanish: η·ν = 0, η^4 = 0 and ν^4 ∈ π_12^s = 0. Reduced h-homology depends only on Σ^∞c̄_5, so
    every homology detector is blind.
- **`spin-trapping-blind-to-fourfold-commutators-in-every-rank`: PASS, standard imports not re-read.**
  - ku ∧ U(N)^{∧j} is free because the AHSS collapses. The Hopf identity Σx′χ(x″) = ε(x) makes c_* = ε ⊗ ε, so
    ku ∧ c̄_2 ≃ 0.
  - Wood's equivalence ko ∧ C(η) ≃ ku gives E ∧ c̄_2 = η·L_2 for ko-modules E. Naturality of η gives η^{j−1}, and
    unit(η^3) ∈ π_3 ko = 0.
  - Anderson--Brown--Peterson split MSpin_(2) into ko-modules: connective covers of ko-modules are ko-modules, and
    HZ/2 is a ko-module through ko → HZ/2. Odd primes and Q go through BP and HQ.
  - A homomorphism vanishing at every localization vanishes.

## Notes

- **Trust surface.** The chain rests on Toms's unrefereed preprint. The steps it uses were read by the first wave,
  and every generalization here was re-derived.
  - Standard inputs not re-read: η^3 = 12ν (Toda); Rokhlin's theorem; the Lie framing represents ν; Borel's
    presentation; Anderson--Brown--Peterson; Wood's theorem.
- **Novelty** of the λ-mod-8 detector and the quaternionic steps was not checked against the literature.
- **No finding needs a correction on main.** No owner message is required for this part.
