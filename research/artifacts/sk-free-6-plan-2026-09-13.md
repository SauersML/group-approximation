# sk-free-6 plan: invariant measures govern normal generation in G_X (2026-09-13)

Lane sk-free-6 (wave 10, free lane; temperament: dynamics). Main tip at planning time: fddd7a0cb4.

## What main already has (grep of main, not redone)
- **Algebraic K-theory of R_X, and H_2/H_3 of the stable elementary group.** sk-open-4 Theorem K (`research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md`): K_n(R_X) ≅ (K^0(X,T)⊗K_n(F_q)) ⊕ K_{n−1}(F_q). Its firewall F1 notes that these invariants miss the order on K^0.
- **Rank functions from invariant measures.** `cantor-z-crossed-product-embeds-in-continuous-factor` (Ara–Claramunt, by citation): a faithful Sylvester rank function rk_μ with rk_μ(χ_U) = μ(U), unique, completion M_K.
- **Complexity visible as LEF growth.** sk-lef-growth and sk-lef-growth-all.
- **Normal subgroups ↔ subsystems.** sk-k2-*. The unstable n = 3 gap stays open in `aperiodic-subshift-ring-unstable-k2-vanishes`; sr(R_X) = 1 is open.
- **Character rigidity:** `subshift-elementary-groups-are-character-rigid`.
- **Live peers:** sk-iso-rigidity (isomorphism rigidity), sk-free-3 (conjugacy problem; its Lemma K is transvection conjugacy vs [[T]]), sk-free-4 (expanders).

## Choice
Unitary characters of G_X see nothing: only 1 and δ_e. This lane shows that the invariant measures of X appear in the normal generation of G_X, through rank lengths. The question: how many conjugates of a small transvection does it take to write a big one?

For g ∈ G_X∖{e} and h ∈ G_X, let ν_g(h) be the least N such that h is a product of N conjugates of g^{±1}. It is finite because G_X is simple. Let cw(g) = sup_h ν_g(h).

### Theorem A (rank lengths; established from main's nodes)
For every T-invariant probability measure μ, ℓ_μ(g) = rk_μ(g − I_3) is a conjugation-invariant, subadditive, symmetric, faithful length function G_X → [0,3].
- μ ↦ ℓ_μ is an affine injection of M_T(X) into the cone of conjugation-invariant length functions, since ℓ_μ(e_12(1_U)) = μ(U).
- ν_g(h) ≥ ℓ_μ(h)/ℓ_μ(g) for every μ.
- **Corollary:** G_X is simple but not uniformly simple: cw(e_12(1_V)) ≥ 1/inf_μ μ(V) → ∞ as V shrinks.
- Contrast: its characters are rigid.

### Theorem B (two-sided transvection formula; to prove now)
Let U, V ⊆ X be nonempty clopen sets, ρ_max = sup_μ μ(U)/μ(V) and ρ_min = inf_μ μ(U)/μ(V). Then

  ρ_max ≤ ν_{e_12(1_V)}(e_12(1_U)) ≤ ⌊ρ_min⌋ + 2(⌈ρ_max⌉ − ⌊ρ_min⌋) + 3.

- **For uniquely ergodic X:** μ(U)/μ(V) ≤ ν ≤ μ(U)/μ(V) + 3. So μ is recovered from normal generation numbers: μ(U) = lim_n ν_{e_12(1_{V_n})}(e_12(1_U)) / ν_{e_12(1_{V_n})}(e_12(1)) along shrinking V_n.
- **Proof ingredients:**
  - Lower bound: Theorem A.
  - Upper bound: Kakutani–Rokhlin towers refining {U, V}, all heights ≥ L; uniform ratio frequencies on long orbit segments.
  - U-levels are grouped per tower into blocks of #V-levels.
  - A level permutation inside each tower gives a unit w ∈ A_Y with w1_{V′}w^{−1} = 1_{U_t}, and diag(w,w,w^{−2}) is a product of Whitehead elements.
  - A partial block costs 2 conjugates: e_12(1_{V′}) = [e_13(1_{V′}), e_32(1_V)] for V′ ⊆ V, and e_32 is a permutation conjugate of e_12.

### Corollary C (every element normally generates root elements boundedly)
- For every g ≠ e there is M_g such that every root element e_ij(r), r ∈ R_X, is a product of at most M_g conjugates of g^{±1}.
- Route: the simplicity mechanism of the note gives e_12(1_V) from boundedly many conjugates of g; then Theorem B with U = X; then e_ij(r) = [e_ik(r), e_kj(1)].
- So ν_g is bi-Lipschitz to the conjugation-invariant root length λ^c.

### Open D (Burago–Ivanov–Polterovich boundedness)
Is every conjugation-invariant norm on G_X bounded, i.e. cw(g) < ∞? By C, this is equivalent to bounded root length λ^c.
- **Reduction:** a cut lemma writes h = H_1·(Peirce transvection)·Z with H_1 ∈ EL_3(A_Y) (≤ 28 root elements by a block Gauss reduction plus Thompson's commutator theorem), and Z a degree-≤ 1 element over an induced corner.
- Attack the degree-1 remainder, and sr(R_X) = 1 through internal cancellation (exchange ring plus Yu's theorem).

## Relevance to the note
At most one sentence, after the simplicity proof or next to character rigidity: "G_X is not uniformly simple: each invariant measure μ of X gives the conjugation-invariant length rk_μ(g − 1)." The note owner decides; the proposal comes only after a PASS.

## Deliverables and order
1. Nodes for A and B with -proof routes and artifact part 1; queue with sk-verify-13.
2. Corollary C node and route.
3. Open D: an open claim with Attempts (cut lemma, block Gauss, the degree-1 remainder), with sub-results as found.
