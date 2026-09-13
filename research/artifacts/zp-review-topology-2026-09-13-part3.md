# ZP topology review, 2026-09-13, part 3

Reviewer lane: z-verify-topology. Verdict conventions as in part 1.

## 14. Problem 1.19 answered YES (z1-19-raag-kernel, 7680130aa0): Theorem 7 PASS, Corollary 8 PASS pending the Bestvina–Brady import

Nodes: `raag-finite-index-sigma-m-forces-connected-flag-complex` (+ `-proof`), artifact
`research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md` (Sections 0–5), root
`zaremsky-1-19-raag-virtual-fn-kernel-conjecture`.

**Statement.** L is a finite flag complex, H ≤ A_L has finite index, and m ≥ 1. If Σ^m(H) ≠ ∅,
then L is (m−1)-connected. If Σ^m(H;R) ≠ ∅, then L is (m−1)-acyclic over R.

**Independent re-derivation.**

1. *Inputs.*
   - (Op): Σ^m and Σ^m(−;R) are open in the character sphere for groups of type F_m (Bieri–Renz,
     Renz). H is of type F, being of finite index in A_L.
   - (BR): the geometric criterion [ψ] ∈ Σ^m(H) ⇒ the superlevel filtration of an H-equivariant
     height on a free cocompact contractible complex is essentially (m−1)-connected (homological
     version: essentially (m−1)-acyclic). Only this forward direction is used.
   - The lane uses continuous superlevel sets g^{-1}[r,∞). The usual subcomplex filtration on
     vertices with g ≥ r is interleaved with them by the bounded variation C₁ on cubes: X_{≥r} lies
     in the full subcomplex on vertices with g ≥ r − C₁, and conversely. This only changes λ.
   - With the opposite sign convention, flip every sign s(v). The argument is symmetric.
2. *A good character (Step 1).* In H₁(A_L;Q) = Q^V the class N_v[v] is nonzero, so
   [v^{N_v}] ≠ 0 in H₁(H;Q). So ev_v: χ ↦ χ(v^{N_v}) is a nonzero functional on Hom(H,R), its kernel
   is a proper hyperplane, and finitely many of them are nowhere dense. The open nonempty Σ^m(H)
   therefore contains ψ with ψ̄(v) ≠ 0 for all v. Correct.
3. *The copy of L at the vertex x = 1.*
   - The vertex link of X̃ is the octahedralization OL.
   - For each simplex σ, x·A_σ is a flat. It is convex: a subcomplex whose links Oσ are full in OL
     is locally convex, hence convex in a CAT(0) cube complex. Also
     x·A_σ ∩ x·A_τ = x·A_{σ∩τ}, because A_σ ∩ A_τ = A_{σ∩τ} and cubes are labelled by generators.
   - Orthants: O_σ ∩ O_τ = O_{σ∩τ}, so S_R ∩ O_σ is a closed spherical simplex, and these glue to
     S_R ≅ |L|.
   - Geodesics from x into O_σ stay in the convex flat and are straight, so dir_x restricted to S_R
     is a continuous bijection from a compact space onto |Λ^s|, hence a homeomorphism.
   - dir_x is continuous on X̃ ∖ {x}: geodesics in CAT(0) spaces depend continuously on their
     endpoints, and near x the space is a cone.
   - Therefore ρ_x = forget ∘ dir_x: X̃ ∖ {x} → |L| is continuous and restricts to a homeomorphism
     S_R → |L| (Lemma A). Correct.
4. *Growth (Lemmas B and C).*
   - Λ_σ = A_σ ∩ H has finite index in A_σ ≅ Z^{|σ|}, so ψ|Λ_σ extends uniquely to a linear
     ψ̄_σ, and ψ̄_σ(v) = ψ(v^{N_v})/N_v.
   - Writing a = λb with b among finitely many coset representatives gives
     g(a) − g(1) − ψ̄_σ(a) = g(b) − g(1) − ψ̄_σ(b), which takes finitely many values. Uniformity over
     σ comes from finitely many simplices.
   - On orthant vertices, ψ̄_σ(a) = Σ a_i|ψ̄(v_i)| ≥ c‖a‖₁ ≥ c‖a‖₂.
   - A point p ∈ O_σ at distance R lies in a cube with a vertex of norm ≥ R − √k. Distances in X̃
     equal flat distances by convexity.
   - So g ≥ g(1) + cR − C′ on S_R. Correct.
5. *Contradiction (Step 3).*
   - Take an essential f: S^k → |L| with k ≤ m−1 (for k = 0, two components), and lift it to S_R.
   - By (BR) it is null inside X_{≥r−λ} with r = g(1) + cR − C′. For large R that set misses x.
   - Composing with ρ_x null-homotopes f in |L|, a contradiction.
   - The homological version runs verbatim with singular cycles.
   Correct.

**Corollary 8 (the answer).**
- H is of type F. A kernel of type F_n gives [ψ] ∈ Σ^n(H), by Bieri–Renz: ker ψ is of type F_n iff
  ±[ψ] ∈ Σ^n(H), for H of type F_n.
- Theorem 7 then makes L (n−1)-connected, and Bestvina–Brady (Invent. Math. 129 (1997)) makes BB_L of
  type F_n. So A_L maps onto Z with a kernel of type F_n, which is exactly Zaremsky's conjecture 1.19,
  for every n ≥ 1.
- Graph: the lane has deliberately NOT let the root compile as established. Both answer routes
  require `bestvina-brady-kernel-finiteness-theorem`, which stays open until its statement is read
  from the source. That is correct discipline. Once that citation route lands (the "if" direction:
  (n−1)-connected L ⇒ BB_L of type F_n; for FP_n(R), (n−1)-acyclic over R), this review covers the
  resulting establishment.

**Model tests checked.**
- L = S⁰ (A_L = F₂): finite-index subgroups are free of rank ≥ 2, so Σ¹ = ∅.
- L = C₄ (F₂×F₂): Σ² of every finite-index subgroup is empty. This is the Stallings–Bieri phenomenon.
- L = flag RP²: Q-acyclic but not simply connected, so Σ^m(−;Q) can be nonempty while Σ² = ∅.
- L a cone: splits off a Z factor.
All consistent.

**Credit and novelty.** The mechanism is a short argument combining openness of Σ^m, the Bieri–Renz
criterion and CAT(0) geometry at a vertex. It may be known, or implicit in the Σ-invariant literature
on RAAGs and their finite-index subgroups (Meier–Meinert–VanWyk; later work on virtual fibring by
Kielak, Fisher, Jankiewicz–Schreve, Kropholler–Llosa Isenrich). A novelty check has been requested
from z-status-a before anyone calls this a first answer. The conjecture was printed on the list's
original June 15, 2023 version, with no "Added" date.

**Remaining input to import at the source:** the Bestvina–Brady theorem statement (the lane is
reading Invent. Math. 129 (1997)). The Bieri–Renz facts (Op), (BR) and (BRk) are standard and were
recalled rather than re-read, as the artifact says. A citation route for them is welcome but not
blocking for this verdict.

Part 1 of the lane's work (`raag-skew-field-betti-numbers-of-finite-index-subgroups`,
`bi-orderable-fp-n-fibre-kills-malcev-neumann-homology`, `raag-virtual-fp-n-kernel-forces-acyclic-flag-complex`,
`raag-virtual-fg-kernel-implies-fg-kernel`) is now an independent second proof of the homological
corollaries. Its review is queued. It is not needed for the answer.
