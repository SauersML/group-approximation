# EX review, dynamics: part 3. Priority review of the lattice-space soficity theorem

Continues `research/artifacts/ex-review-dynamics-2026-09-12.md` (verdicts in §0 there). Lane `ex-verify-dynamics`,
2026-09-13. Requested by the coordinator as a priority. The first pass is part 1 §8 and part 2 §12; this section
re-derives the four load-bearing steps again and checks both model tests against their sources.

## 8b. ex-lattice-space-action (05d4563791, e3d75e3d00, 6d94d7b74b, 31625a5f8c, e3dd844bba)

| item | verdict |
|---|---|
| (1) Theorem P, `finite-equidistributed-orbits-give-sofic-action` (+ `-proof`) | PASS |
| (2) Smoothing and equidistribution: Lemmas S1–S4, E and Theorem H of `sl3z-lattice-space-action-is-sofic` (+ `-proof`) | PASS |
| (3) Finite orbits are exactly the commensurator points | PASS (derivation below). Only the direction `a ∈ SL_n(Z[1/p])` gives a finite orbit is consumed, and Lemma S3(3) proves it directly, with the exact orbit size |
| (4) Class extension, `sl3-split-class-lattice-quotient-actions-are-sofic` (+ `-proof`) | PASS |
| Model test `n = 2` against Păunescu | PASS, against the source |
| Model test: Kun–Thom generalized Bernoulli action | PASS, against the source |
| Refutation edge on `sl3z-lattice-space-action-is-not-sofic`; conditional routes into `sl3z-admits-nonsofic-action` and `mixing-free-nonsofic-action-of-sofic-group` | correct. The two routes requiring the refuted claim can never fire, and the cocompact-quotient routes require the OPEN `sl3z-on-cocompact-lattice-quotient-is-not-sofic` |

No defect found. Nothing in this cluster decides a famous problem: `sl3z-admits-nonsofic-action` and the mixing
root stay OPEN.

### (1) Theorem P

- **Models.** On `V_k × W_k` let `g` act by `π_k(g) × σ_k(g)`, the honest restriction to the finite invariant set
  times a sofic approximation. A projection letter `1_A` becomes `1_(A ∩ V_k) ⊗ 1`. The two tensor factors multiply
  separately, so a word `w` becomes `(1_(B_w ∩ V_k) π_k(h_w)) ⊗ S_w(σ_k)`. Its normalized trace is
  `|{v ∈ B_w ∩ V_k : h_w v = v}|/|V_k| · tr S_w(σ_k)`.
- **Limits.** `tr S_w(σ_k) → δ_(h_w,1)`, because `S_w(σ_k)` is Hamming-close to `σ_k(h_w)`.
  - If `h_w = 1`, the first factor is `ν_k(B_w)`.
  - If `h_w != 1`, the first factor is at most `1` in modulus.
- **Portmanteau.** `B_w` is built from continuity sets by finitely many complements, intersections and translates
  by `μ`-preserving homeomorphisms, so `μ(∂B_w) = 0`. Vague convergence to a probability measure is tight, hence
  weak, so `ν_k(B_w) → μ(B_w) = τ(w)`.
- **Conclusion.** Lemma LC turns models of every level and error into a sofic embedding. Freeness is not needed,
  because the trace-zero condition comes from the `σ_k` factor.

### (2) Smoothing and equidistribution

Notation: `G = SL_n(R)`, `Γ = SL_n(Z)`, `H = SL_n(Q_p)`, `K = SL_n(Z_p)`, `Δ = SL_n(Z[1/p])` diagonal in `G × H`,
`Y = (G × H)/Δ`.

- **S1.** `Z[1/p] ∩ Z_p = Z`, so `Δ ∩ (G × K) = Γ`. Elementary matrices over dense rings give density of `Δ` in both
  factors. Strong approximation (`SL_n(Z) → SL_n(Z/p^m)` is onto) makes `Γ` dense in `K`. `H = KΔ`, since `Kh` is
  open and `Δ` is dense.
- **S2.** `D × K` is a fundamental domain for `Δ`: move `h` into `K` by `γ ∈ Δ ∩ Kh`, then `g` into `D` by `Γ ⊆ K`.
  It is unique because `Δ ∩ K = Γ`.
- **S3.** `π((g,h)Δ) = gγ^-1 Γ` for `γ ∈ Δ ∩ Kh` is well defined, since two choices differ by `Γ`. It is
  `G`-equivariant and `K`-invariant, and `π_* m_Y = μ`.
  - For `a ∈ Δ` and `U = K ∩ a^-1 K a`, `Φ_a(k) = π((1,ak)Δ)` is constant on `U`-cosets and lands in
    `Γ a^-1 Γ/Γ`.
  - It is onto, since `Φ_a(δ^-1) = δ a^-1 Γ`.
  - The stabilizer of `a^-1Γ` in `Γ` is `Γ ∩ U`, and `[Γ : Γ ∩ U] = [K : U]` by density. So `U\K → V(a)` is a
    bijection, and Haar measure on `K` pushes to counting measure on `V(a)`.
- **S4.** An `H`-invariant `F` is a function of `g` alone, invariant under the dense `Δ`, hence constant. Howe–Moore
  holds for `SL_n(Q_p) = G^+` (Ciobotaru Theorem 1.1 with Definition 4.23), so the coefficients on `L²_0(Y)` are
  `C_0`.
- **E (smoothing).**
  - Choose `U ∋ 1` with `U^-1 U ∩ Γ = {1}`, so that `U ⊆ D`, and a bump `ψ` on `U`.
  - The measure `ψ(u)du ⊗ dk` on `D × K` is `Ψ_U m_Y` with `Ψ_U` bounded.
  - `(u, ak) = (1,a)(u,k)` and `G`-equivariance of `π` give
    `∫ F((1,a)y) dν_U(y) = ∫ψ(u) ∫_K f(u·Φ_a(k)) dk du`, which is within `ω_f(U)` of the `V(a)`-average of `f`.
  - The left side is `⟨λ(a^-1)F, Ψ_U⟩ = ⟨λ(a^-1)F_0, Ψ_0⟩ + ∫ f dμ`, and the first term tends to `0` by S4.
  - Let `U → 1`.
- **H.** `|p^-k|_p = p^k`, so `a_k = diag(p^k, p^-k, 1, …)` leaves compact sets of `H`, and `Γ` is residually finite.

### (3) Finite orbits and the commensurator

For `g ∈ G`, the stabilizer of `gΓ` in `Γ` is `Γ ∩ gΓg^-1`. So the orbit `Γ·gΓ` is finite iff
`Γ_0 = Γ ∩ gΓg^-1` has finite index in `Γ`.

- **One-sided finite index is enough.** If `[Γ : Γ_0] < ∞`, then `Γ_0` is a lattice of `G`.
  `Γ_0 <= gΓg^-1`, and both are lattices, so `[gΓg^-1 : Γ_0] = covol(Γ_0)/covol(gΓg^-1) < ∞`. Hence `g`
  commensurates `Γ`. The converse is the definition.
- **Density.** `SL_n(Q) ⊆ Comm_G(Γ)`: for `q` with entries in `(1/D)Z`, `q Γ(D²) q^-1 ⊆ Γ`. And `SL_n(Q)` is dense
  in `SL_n(R)`.
- **Scope of use.** Theorem H consumes only `a ∈ Δ ⊆ SL_n(Q)` and gets the orbit size from S3(3). The same covolume
  argument gives part 2 §8.4 of the artifact: a finite orbit of `gΛ` would make `Λ` commensurable with
  `g^-1 Γ g`. Commensurable lattices are both uniform or both not, so cocompact `Λ` has no finite orbit.

### (4) Class extension

- **(F)** Factors and **(R)** restriction: a sofic embedding restricts to `L^∞(Y) ⋊ Γ_1` and to `L^∞(X) ⋊ Γ'`.
- **(D)** Duality: `X(Γ_1,Γ_2)` is free, because fixed sets are cosets of proper centralizers and `SL_3(R)` has
  trivial center. The coupling `(γ_1,γ_2)·g = γ_1 g γ_2^-1` restricts on the two fundamental domains to the orbit
  relations of `X(Γ_1,Γ_2)` and, via `Γ_1 g ↦ g^-1 Γ_1`, of `X(Γ_2,Γ_1)`. SOE invariance for free actions (part 1
  §3.1) transfers soficity.
- **(C)** Conjugation: `xΓ_2 ↦ h^-1 x k (k^-1 Γ_2 k)` is well defined and intertwines along `γ ↦ h^-1 γ h`.
- **Chain.** `X(Γ,Γ)` sofic ⇒ `X(Γ_0,Γ)` (R) ⇒ `X(Γ,Γ_0)` (D) ⇒ `X(Γ_0,Γ_0)` (R) ⇒ `X(Γ_0,Γ_1)` (F, through
  `G/Γ_0 → G/Γ_1`) ⇒ `X(Γ_1,Γ_0)` (D) ⇒ `X(Γ_1,Γ_2)` (F). Here `Γ_0 = Γ ∩ Γ_1 ∩ Γ_2` has finite index in all three.

### Model tests, checked against sources

- **`n = 2`.** Păunescu arXiv:1002.0605v5, read from the PDF:
  - p. 14: "Proposition 3.4. Amenable groups are in 𝒮."
  - p. 16: "Theorem 3.9. Class 𝒮 is closed under amalgamated product over amenable groups."
  - Definition 3.2 (p. 13): 𝒮 is "the class of groups for which every action is sofic".

  `SL_2(Z) ≅ Z/4 *_(Z/2) Z/6`, both factors are finite, and the amalgamation is over the finite `Z/2`. So
  `SL_2(Z) ∈ 𝒮`, and every action of `SL_2(Z)` is sofic, including the lattice-space action. Theorem H agrees for
  `n = 2`. This is a calibration: it shows the theorem is consistent where the answer is known, not that it is sharp.
- **Kun–Thom.** arXiv:2608.06222v3, read from the PDF:
  - p. 2: "Let N = ⟨⟨Γ⟩⟩ be the normal subgroup generated by Γ. … Consequently, the profinite closure of Γ contains N."
  - p. 3: "Corollary D. … If (K,κ) is a nontrivial standard probability space, then the generalized Bernoulli
    action G ↷ (K,κ)^{G/Γ} is not sofic."
  - Theorem E: residually finite Kazhdan pairs.

  The test argument:
  - A colouring `c ∈ {0,1}^(G/Γ)` with finite `G`-orbit is fixed by a finite-index normal `M`, so it is constant on
    `M`-orbits of `G/Γ`.
  - For `g ∈ N ∖ Γ`, which exists since `Γ` is not normal, `g ∈ ∩_M MΓ` by the quoted sentence. So `gΓ ∈ M·Γ`, and
    `c(gΓ) = c(Γ)`.
  - Every finite invariant set therefore gives measure `0` to the clopen set `{c(gΓ) != c(Γ)}`, which has product
    measure `1/2`.
  - So no finite invariant sets equidistribute. `G` is residually finite, hence sofic, and Theorem P's hypothesis
    fails exactly on a nonsofic action, as the contrapositive requires.

### Credit and trust

- Equidistribution of Hecke points is classical: Clozel–Oh–Ullmo 2001, Eskin–Oh 2006. The artifact proves the case
  it needs from Howe–Moore alone. No theorem number from those papers is consumed.
- The soficity consequence had only a bounded novelty check, and may be folklore. Theorem P is recorded by the lane
  as folklore-level.
- Remark F (asymptotic freeness of `V_k` for odd `n`) checks and is not consumed.

## 13f. ex-tree-lattice-mixing: Radu's horizontal quotient is an arithmetic lattice (aafc5e8540)

| node | verdict |
|---|---|
| `radu-horizontal-quotient-is-arithmetic-lattice` (+ `-proof`), flipped from OPEN to ESTABLISHED | PASS. The 2-adic matrix model, the fixed vertex `p`, the edge action and the inversions are taken from the landed outputs (`radu-second-tree-checks-output-2026-09-13.txt`, `radu-valuations-checks-output-2026-09-13.txt`) |
| edit to `radu-horizontal-projection-kills-delta-squared` | wiring only |

- **Transitivity on `T'`.** `ρ(x)` inverts edge 0, so the orbit `G·p` contains the neighbour across it.
  `S_3 = ⟨ρ(xz), ρ(xyx)⟩ <= G_p` permutes the three edges at `p` transitively. So all neighbours of `p` are in
  `G·p`, by invariance so are all neighbours of every orbit point, and connectedness finishes.
- **Vertex group.**
  - With `s = xz` and `u = xyx`: `z = xs`, `y = xux` and `xyz = us`. So
    `W = ⟨x,y,z | x²,y²,z²,(xz)²,(xyz)³⟩ = ⟨x,s,u | x², s², u², (xs)², (us)³⟩ = D_2 *_(C_2) S_3`, which is
    `PGL_2(Z)`.
  - In the Bass–Serre tree the `S_3`-vertices have degree 3 and the `D_2`-vertices degree 2.
  - The equivariant map to the subdivided `T'` is well defined, because `S_3` fixes `p` and `D_2 = ⟨x, xz⟩` fixes
    the midpoint of edge 0 (`xz` fixes edge 0, and `x` inverts it). It is locally bijective, since the stabilizer
    of edge 0 in `S_3` is `⟨xz⟩`, so it is an isomorphism of trees.
  - The kernel of `W` on its Bass–Serre tree is the core of `⟨xz⟩` in `S_3`, which is trivial. So `W → ρ(V)` is
    injective, and `Λ_v = ker ρ ⊆ V` is the normal closure of `(xz)²` and `(xyz)³` in `V`.
- **Lattice.**
  - `ρ(A)` is simply transitive on `T_h`, because `A ∩ Λ_v ⊆ A ∩ V = 1`. With transitivity of `ρ(V)` on `T'`,
    `Q` is vertex-transitive on `T_h × T'`, with stabilizer `ρ(V)_p ≅ S_3`, the Bass–Serre vertex group.
  - A discrete group acting with finite stabilizers and one vertex orbit is a cocompact lattice. `N(O)/F^×` is
    discrete and contains it, so the index is finite.
- **Euler characteristic.**
  - The horizontal graph of groups has one vertex and one inverted edge, so
    `χ(Q) = χ(W) − χ(V_a)/2 = −χ(W)/2 = 1/24`, with `χ(W) = 1/4 + 1/6 − 1/2 = −1/12` and `[W : V_a] = 3`.
  - Independent check through the square complex: `(1 − 3/2 − 3/2 + 9/4)/6 = 1/24`.
- **Item 4.** The translation length of `g` on the Bruhat–Tits tree is `max(0, −v(tr²/det))`. `ab`, `bc` and `ca`
  have `v_(𝔮')(1 + w/2) = 2`, and the generators are involutions, so all are elliptic. Serre, *Trees* I.6.5, applied
  on the subdivision, gives a point `p_A` fixed by `ρ(A)`. Then `gA ↦ ρ(g)p_A` is equivariant and Lipschitz, and
  collapses `Λ_v`.
- **Scope.** `Γ_R` is (infinitely generated free)-by-(arithmetic lattice). This does not decide
  `radu-bmw-lattice-nonsofic`: extensions of free groups by residually finite groups need not be sofic. The index
  `[N(O)/F^× : Q]` stays undecided; the Euler-characteristic numerology is recalled, not proved.
