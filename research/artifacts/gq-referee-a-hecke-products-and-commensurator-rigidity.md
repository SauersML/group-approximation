# Referee report (gq-referee-a, proof-gap lens): Hecke members of products, and commensurator-rigid groups lacking faithful members

**Reviewed** (lane bh-cat0), read on origin/main:
- `faithful-hecke-members-products-proof` (1d818075c), which targets `faithful-hecke-members-pass-to-direct-products`;
- `commensurator-finite-no-faithful-bs-proof` (8462f018b), which targets
  `commensurator-rigid-groups-lack-faithful-bs-members`.

**Verdict: PASS for both.** The key dichotomy holds for torsion-free lattices in `Isom(H^n)`, `n ≥ 3`: `BS_G` has a
faithful member with torsion-free vertex groups iff `G` is arithmetic. There are two nits. Mostow–Prasad, Margulis,
Borel density and the reducible-lattice decomposition are for the citation lens.

## 1. `faithful-hecke-members-products-proof`
- **The criterion.**
  - *The kernel satisfies the conditions.* By Britton, `G ∩ t_j^(−1)Gt_j = A_j`, so the kernel `K = core_H(G)` lies
    in every `A_j`, is normal in `G`, and has `φ_j(K) = t_jKt_j^(−1) = K`.
  - *Any such `N` lies in the kernel.* For `N` normal in `G` with `N ⊆ A_j` and `φ_j(N) = N`, we get
    `t_jNt_j^(−1) = N`, and `t_j^(−1)nt_j = φ_j^(−1)(n) ∈ N`. So `N ⊴ H`, and `N ⊆ K`. ✓
- **Products.**
  - `π_1(N)` is normal in `G_1`, and `π_1(N) ⊆ A_j`.
  - `π_1 ∘ (φ_j × id) = φ_j ∘ π_1` on `A_j × G_2`, so `φ_j(π_1N) = π_1N`. The `ψ`-data impose nothing on `π_1`.
  - So faithfulness of `(G_1, φ)` gives `π_1(N) = 1`, and symmetrically `π_2(N) = 1`, so `N = 1`. Induction handles
    finite products. ✓
- **Consequences.**
  - For `Z^n` with `x ↦ 2x`: `N = 2N` forces `N ⊆ ⋂ 2^iZ^n = 0`.
  - The arithmetic data is the lemma's multi-letter data, which the criterion covers.
  - The product is finitely presented, and `BS_G = BS_P` by commensurability. The bs-class node then gives
    `BS_G ⊆ B_A`. ✓

## 2. `commensurator-finite-no-faithful-bs-proof`
- **Step 1.**
  - `VZ(V) ∩ U = VZ(U) ≅ VZ(U') = VZ(G) ∩ U' = 1`. So `VZ(V)` meets a finite-index subgroup trivially, hence has at
    most `[V:U]` elements, and it is trivial because `V` is torsion-free.
  - `ker κ_V = VZ(V) = 1`. ✓
- **Step 3: `ρ` respects the relations (the author asked about this).**
  - Functoriality gives `φ_*(κ(u)) = κ(φ(u))` for `φ = ω_eα_e^(−1)`.
  - For `e ∈ Y_0`, `ι_(t(e)) ∘ φ_* ∘ ι_(o(e))^(−1) = id` by the definition of the transport, so `c_e = 1`.
  - For `e ∉ Y_0`, `ι_(t(e)) ∘ φ_* ∘ ι_(o(e))^(−1)` is induced by a commensuration of `V_(x_0)`, which is `Ad(c_e)` by
    Step 2.
  - So `ρ(ω_e a) = c_e ρ(α_e a) c_e^(−1)` in both cases. These are exactly the Bass–Serre relations of `H`. ✓
  - `ρ` is injective on each `V_x` by Step 1, because the vertex groups are torsion-free.
- **Step 4.**
  - For every `V` commensurable with `G`, `κ_V(V)` has finite index in `Comm(V) ≅ Comm(G)`. A finite-index `U ≤ V`
    corresponds to a finite-index `U' ≤ G`, and `κ_G(U')` has finite index in `κ_G(G)`, which has finite index by
    hypothesis.
  - So the finitely many subgroups `ρ(V_x)`, `ρ(α_eE_e)` and `ρ(ω_eE_e)` have finite index, and so does their normal
    core `P`.
  - `P_x` has finite index in the infinite `V_x`, so it is nontrivial (N1). ✓
- **Step 5: the pull-back inside the edge groups (the author asked about this).**
  - `P ⊆ ρ(α_eE_e)` and `ρ|_(V_(o(e)))` is injective, so `P_(o(e)) ⊆ α_e(E_e)`.
  - Normality of `P` and the relation give `α_e(a) ∈ P_(o(e)) ⟺ ω_e(a) ∈ P_(t(e))`.
  - So `Q_e` satisfies `α_e(Q_e) = P_(o(e))` and `ω_e(Q_e) = P_(t(e))`. ✓
- **Step 6: one normal `N` (the author asked about this).**
  - The tree edges identify `α_e(a) = ω_e(a)`, so all `P_x` coincide with one subgroup `N`.
  - The vertex groups normalize `N`, and `t_eNt_e^(−1) = ω_e(Q_e) = N`. So `N ⊴ H`.
  - `N ≠ 1` lies in every vertex stabilizer, so `H` is not faithful. ✓
- **The instances, and the dichotomy (the author asked me to attack this).**
  - Mostow–Prasad identifies `Comm(G)` with `Comm_(Isom(H^n))(G)`, uniquely, because lattices have trivial
    centralizer.
  - For non-arithmetic `G`, Margulis makes that commensurator discrete, so it contains `G` with finite index. This
    gives the theorem's hypothesis, and `VZ(G) = 1` by Borel density. So "only if" holds.
  - For "if": arithmetic `G` has a dense commensurator in the centerless `PO(n,1)^0`, which has no compact factors.
    The Lie-lattice lemma then gives a one-vertex Hecke member with vertex group `G`, which is torsion-free and
    faithful.
  - The dichotomy holds as stated. ✓

## Nits
- **N1 (commensurator, Step 4).** Say "`P_x` has finite index in `V_x`", which is the reason it is nontrivial. Being
  a preimage of `P` alone does not give that.
- **N2 (instances).** The Mostow–Prasad isometry may lie in `PO(n,1) ∖ PO(n,1)^0`, since it can reverse orientation.
  Work in `Isom(H^n) = PO(n,1)`, and note that Margulis's discreteness passes to this finite extension:
  `Comm_(PO(n,1))(G) ∩ PO(n,1)^0 = Comm_(PO(n,1)^0)(G)`.
