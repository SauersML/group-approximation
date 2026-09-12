# Characteristic-three rank models of the ternary Leavitt unit group

Lane `w3-gate-char3`, 2026-09-12. Supports `ternary-leavitt-rank-models-move-z-iff-nontrivial` and
the open gate `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`.

## 0. Setup

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = −1`, `PG = G/<z>`, and `π : G -> PG` the quotient map.
- `ι(g) = s0 g t0 + s1 t1`, the corner embedding (`leavitt-units-embed-in-their-scalar-quotient`).
- A *rank model* of a group `H` is a homomorphism `σ : H -> M^x`, where
  `M = prod_ω M_(n_i)(k_i) / ker ρ` is a rank ultraproduct over fields `k_i` of characteristic three and
  `ρ = lim_ω rk / n_i`. It is *trivial* if `σ(H) = {1}`, *injective* if `ker σ = 1`.
- A rank model `σ` of `G` is *anti-central* if `σ(z) = −1`.
- The lane's question: does `G` have a rank model moving `z`? A yes refutes
  `ternary-anti-invariant-swap-corner-is-full` (`anti-central-rank-models-kill-ternary-corner-witnesses`
  with `Γ = G`).

## 1. Two lemmas

**Lemma 1.1 (normal subgroups).** Every normal subgroup `K` of `G` is `G` or lies in `<z>`.

*Proof.* `K<z>/<z>` is normal in `PG`, which is simple (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`,
`p = 3`). If it is trivial, `K <= <z>`. Otherwise `K<z> = G`. Since `z` is central,
`[G, G] = [K<z>, K<z>] = [K, K] <= K`, and `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`),
so `K = G`. QED

**Lemma 1.2 (tensor squares).** Let `k` be a field of characteristic not two.
- (a) For `A, A'` in `M_n(k)`, `rk(A⊗A − A'⊗A')/n^2 <= 2 rk(A − A')/n`. So `A -> A⊗A` descends to a
  multiplicative map from `prod_ω M_(n_i)(k_i)/ker ρ` to `prod_ω M_(n_i^2)(k_i)/ker ρ`, and a rank model
  `σ` gives a rank model `σ⊗σ`.
- (b) Let `A` be in `GL_n(k)` and `δ = rk(A⊗A − I)/n^2 < 1/3`. Then `rk(A − μ I)/n <= δ` for some
  `μ` in `{1, −1}`.
- (c) If a unit `u` of a rank ultraproduct satisfies `u⊗u = 1`, then `u = 1` or `u = −1`.

*Proof.*
- (a) `A⊗A − A'⊗A' = (A − A')⊗A + A'⊗(A − A')`, and `rk(X⊗Y) = rk(X) rk(Y) <= n rk(X)`.
  Multiplicativity holds on the nose at every stage.
- (b) Identify `k^n ⊗ k^n` with `M_n(k)` by `v⊗w -> v w^T`. Then `(A⊗A)X = A X A^T`, so
  `ker(A⊗A − I) = {X : A X = X B}` with `B = A^(−T)`. That is the space of `k[x]`-module maps from
  `(k^n, B)` to `(k^n, A)`, of dimension at least `(1 − δ) n^2`.
  - Over an algebraic closure its dimension is `Σ_ν Σ_(i,j) min(a_i(ν), b_j(ν))`, with `a_i(ν)` and
    `b_j(ν)` the Jordan block sizes of `A` and `B` at `ν`. Using `min(a_i, b_j) <= b_j`, it is at most
    `Σ_ν g(ν) m_B(ν)`, where `g(ν) = dim ker(A − ν)`. `B` has the Jordan types of `A^(−1)`, so
    `m_B(ν) = m(ν^(−1))`, the algebraic multiplicity of `ν^(−1)` in `A`.
  - So `(1 − δ) n^2 <= Σ_ν g(ν) m(ν^(−1)) <= n · max_ν g(ν)`. Let `ν*` maximize `g`. Then
    `rk(A − ν*) = n − g(ν*) <= δ n`.
  - If `ν* != ν*^(−1)`: `m(ν*^(−1)) <= n − m(ν*) <= δ n` and `Σ_(ν != ν*) g(ν) <= δ n`, so the sum is
    at most `n · δn + δn · n = 2δ n^2 < (1 − δ) n^2`. Contradiction. So `ν* = ±1`, which lies in `k`,
    and ranks over `k` equal ranks over the closure.
- (c) If `uv = 1` in `M`, representatives satisfy `rk(u_i v_i − I)/n_i -> 0`, so `u_i` has rank at least
  `n_i − rk(u_i v_i − I)`, and some invertible `u'_i` differs from `u_i` by at most that rank. Along `ω`,
  `rk(u'_i ⊗ u'_i − I)/n_i^2 -> 0`; (b) gives signs `μ_i` with `rk(u'_i − μ_i)/n_i -> 0`, and `μ_i` is
  `ω`-almost constant. QED

## 2. The theorem

**Theorem 2.1.** The following are equivalent.
1. `G` has a rank model `σ` with `σ(z) != 1`.
2. `G` has a nontrivial rank model.
3. `G` has an injective rank model.
4. `PG` has a nontrivial rank model.
5. `PG` has an injective rank model.
6. `G` has an anti-central rank model.

Explicitly: if `σ` is nontrivial, `σ∘ι` is injective and moves `z`. If `σ` is anti-central, `σ⊗σ`
factors through a nontrivial model of `PG`.

*Proof.*
- (2) ⟹ (3). By Lemma 1.1, `ker σ <= <z>`. Then `ker(σ∘ι) = ι^(−1)(ker σ) <= ι^(−1)(<z>) = {1}`,
  since `ι(G)` meets the scalars only in `1`.
- (3) ⟹ (1) and (6) ⟹ (1): `z != 1`.
- (1) ⟹ (6). `f = 2(1 − σ(z))` is an idempotent commuting with `σ(G)`, nonzero because `2` is
  invertible. The corner `fMf`, renormalized by `ρ(f)`, is again a rank ultraproduct over the same
  fields (as used in `matrix-unit-rank-models-extract-ring-rank-models`), and `g -> σ(g) f` is a model
  with `z -> −f`.
- (6) ⟹ (4). `T = σ⊗σ` is a rank model (Lemma 1.2(a)) with `T(z) = (−1)⊗(−1) = 1`, so it factors
  through `PG`. If `T` were trivial, Lemma 1.2(c) would give `σ(g) = μ(g)` in `{±1}` for all `g`. Then `μ`
  is a homomorphism `G -> {±1}`, trivial because `G` is perfect, so `σ(z) = 1`, contradicting
  `σ(z) = −1 != 1`.
- (4) ⟹ (5). `PG` is simple.
- (5) ⟹ (3). `σ∘π∘ι` is injective, because `π∘ι` is (`leavitt-units-embed-in-their-scalar-quotient`).
- (3) ⟹ (2). `G != 1`. QED

## 3. Consequences

**Corollary 3.1.** If `G` or `PG` has any nontrivial rank model in characteristic three, then
`ternary-anti-invariant-swap-corner-is-full` is false.

*Proof.* Theorem 2.1 gives a model of `G` moving `z`. Apply Theorem 2.1(d) of
`research/artifacts/ternary-corner-state-sources-2026-09-12.md` with `Γ = G`. QED

**Corollary 3.2 (the gate is one question).** The two directions of the lane's question are:
- yes: `G`, equivalently `PG`, has a nontrivial characteristic-three rank model, and the ternary corner dies;
- no: every characteristic-three rank model of `G` and of `PG` is trivial, so neither group is `F_3`-linear
  sofic, since a linear sofic approximation over `F_3` is an injective rank model.

"Moving `z`" is not an extra condition, and nothing is gained by separating `G` from `PG`.

**Remark 3.3 (comparison).** `projective-ternary-group-is-f3-linear-sofic` records that `F_3`-linear
soficity of `PG` kills the anti-central corner through stable finiteness. Theorem 2.1 needs no separation:
one nontrivial model of `PG`, or of `G`, suffices. It also adds the converse direction, from models of `G`
to models of `PG`, through tensor squares.

**Remark 3.4 (corner locality in characteristic three).** For a prefix `P`,
`ι_P(g) = S[P] g T[P] + (1 − S[P] T[P])` is an injective endomorphism with `ι_P(G)` not inside `<z>`. By
Lemma 1.1, `σ` is trivial exactly when `σ∘ι_P` is. The extraction step needs both odd-characteristic
identities `N_12^2 = 0` and `N_23 N_12 = 0` (`el3-unit-root-matrix-units-iff-two-root-identities`), then
`matrix-unit-rank-models-extract-ring-rank-models` and `leavitt-algebra-has-no-unital-rank-model`.
So "no" to the gate is equivalent to: both identities hold in every anti-central rank model of
`EL_3(R)`, identified with `G` through a three-leaf prefix code. An anti-central model satisfying them
would give matrix units, a unital rank model of `R` or triviality, and neither is possible while
`z -> −1`.

## 4. Anti-central models see Haar measure on the signed diagonal

Notation from `signed-thompson-algebra-is-odd-measure-crossed-product`:
- `E = {τ_C = 1 − 2P_C}` over clopens `C` of Cantor space `X`, with `τ_X = z`;
- `V` is the group of monomial Thompson units and `H = E ⋊ V`;
- `F_3[H] eps_- ≅ C(M_-, F_3) ⋊ V`, with `[τ_C] -> (μ -> (−1)^μ(C))`.

For a clopen `C`, `Q_C = eps_- · 2(1 − [τ_C])` is the indicator of `{μ : μ(C) = 1}`. `λ` is the normalized
Haar measure on `M_-` (`odd-measure-space-has-no-honest-thompson-compression`).

**Theorem 4.1.** Let `Γ <= G` contain `H`, and let `σ : Γ -> M^x` be an anti-central rank model, with
linear extension `φ : F_3[H] eps_- -> M`, unital because `σ(z) = −1`. Then `ρ(φ(1_U)) = λ(U)` for every
clopen `U` of `M_-`.

*Proof.*
- **Half split.** Let `C` be a proper nonempty clopen.
  - `σ(τ_(X∖C)) = σ(z τ_C) = −σ(τ_C)`, so `φ(Q_(X∖C)) = 1 − φ(Q_C)`.
  - `V` is transitive on proper nonempty clopens: refine `C`, `X∖C` and their images into cylinders of
    complete prefix codes with matching leaf counts, then map leaves to leaves. So some `g` in `V` has
    `gC = X∖C` and `[g] Q_C [g]^−1 = Q_(X∖C)`.
  - Conjugate idempotents have equal rank, and the two orthogonal idempotents sum to `1`. So
    `ρ(φ(Q_C)) = 1/2`.
- **Atoms.**
  - Every clopen of `M_-` is a finite union of atoms `A_ε = {μ : μ(c_i) = ε_i for all i}`, for a complete
    prefix code `c_1, ..., c_n` and `ε` in `F_2^n` of odd weight.
  - Put `a_ε = ρ(φ(1_(A_ε)))`, and `a_ε = 0` for even `ε`. For `S ⊆ [n]` put
    `χ_S(ε) = (−1)^(Σ_(i∈S) ε_i)` and `c_S = ∪_(i∈S) c_i`.
  - `Q_(c_S)` is `Σ_(χ_S(ε) = −1) 1_(A_ε)`, so `Σ_ε a_ε χ_S(ε) = 1 − 2ρ(φ(Q_(c_S)))`. This is `1` for
    `S = ∅`, `−1` for `S = [n]`, and `0` otherwise by the half split.
- **Inversion.** `a_ε = 2^(−n) Σ_S χ_S(ε) Σ_η a_η χ_S(η) = 2^(−n)(1 − χ_([n])(ε))`, which is `2^(1−n)`
  for odd `ε`. That is `λ(A_ε)`, and ranks of orthogonal idempotents add. QED

**Corollary 4.2.** Let `σ` be any nontrivial characteristic-three rank model of `G`. The anti-central
compression of `σ∘ι` (Theorem 2.1) is a model of `G`, so Theorem 4.1 applies to it. A "yes" to the gate
therefore produces a unital map from `F_3[H] eps_-` to a rank ultraproduct whose diagonal law is `λ`.

**Remark 4.3.**
- **Cylinder idempotents.** A representation of `S[α]T[α]` covariant under `V` would have `V`-invariant,
  additive, halving ranks, hence ranks zero. Anti-central models represent the signed eigen-idempotents
  `Q_C` instead, and their law is the `V`-invariant Haar measure.
- **Recovery.** `q_0 = Q_[0]` has rank `1/2 < 1`, which recovers the corner exclusion of
  `anti-central-rank-models-kill-ternary-corner-witnesses` through
  `hadamard-unit-conjugates-swap-idempotent-to-cylinder`.
- **Finite levels.** The twisted regular representation of a level group `GL_(2^k)(F_3)`, induced from the
  sign of `<z>`, has the Haar law on its diagonal torus. The natural module has torus weights `e_i` only,
  so for `k >= 2` it is never the whole restriction of an anti-central model.

## 5. Torus normal form of root elements

Identify `G = GL_3(R) = EL_3(R)` through the complete prefix code `(0, 10, 11)`
(`leavitt-gl-equals-el-and-perfect-unit-group`). Then `x_12(1) = 1 + S[0]T[10]`, and the constant
diagonal sign matrices form `T_3 = <τ_0, τ_10, τ_11>`, with `τ_0 τ_10 τ_11 = z`.

**Proposition 5.1.** Let `σ` be any rank model of `G` in characteristic three. Let `P_ε`, `ε` in `{±}^3`,
be the joint eigen-idempotents of `σ(T_3)`, `N = σ(x_12(1)) − 1`, and `A = Σ_ε P_(ε') N P_ε`, where `ε'` is
`ε` with its first two signs flipped. Then:
- (a) `N = A − A^2`, `A^3 = 0`, and `A^2` commutes with every `P_ε`;
- (b) `N^2 = A^2`, so `N^2 = 0` exactly when `N` has no weight-preserving component;
- (c) if `σ` is anti-central, the only nonzero weight spaces are `W_1 = (−,+,+)`, `W_2 = (+,−,+)`,
  `W_3 = (+,+,−)` and `W_0 = (−,−,−)`, each of rank `1/4`, and `A` exchanges `W_1` with `W_2` and `W_3`
  with `W_0`.

*Proof.*
- **Allowed components.** `τ_11` and `τ_0 τ_10` commute with `x_12(1)`. So `P_η N P_ε = 0` unless
  `η_3 = ε_3` and `η_1 η_2 = ε_1 ε_2`, that is, unless `η` is `ε` or `ε'`. Write `N = D + A` with
  `D = Σ_ε P_ε N P_ε`.
- **The reflection.** `τ_0 x_12(1) τ_0 = x_12(−1)`. Since `x_12(1)^3 = 1`, `N^3 = 0` and
  `σ(x_12(−1)) − 1 = (1 + N)^−1 − 1 = −N + N^2`. Conjugation by `σ(τ_0)` fixes `D` and negates `A`, so
  `D − A = −D − A + N^2`, and `D = 2N^2 = −N^2`.
- **Squares.** `N^2 = −D` preserves weights, so the weight-flipping part `DA + AD` of `N^2` vanishes and
  `N^2 = D^2 + A^2`. Also `D^2 = N^4 = 0`. So `N^2 = A^2`, `D = −A^2`, `N = A − A^2`, and
  `0 = DA + AD = −2A^3 = A^3`.
- (c) is Theorem 4.1 for the code `(0, 10, 11)`: a reflection `τ_c` acts by `(−1)^μ(c)`. QED

**Remark 5.2 (the first identity, and what escapes).**
- `N_12^2 = 0` fails exactly through the weight-preserving part `−A^2`. It lives on `W_1 ⊕ W_2`, where
  `τ_0 τ_10` acts by `−1`, or on `W_3 ⊕ W_0`, where it acts by `+1`. In a matrix-unit model `A` maps only
  `W_2 -> W_1` and `A^2 = 0`.
- Projective content escapes. A projective module of a level group restricts freely to the Sylow
  3-subgroup `x_12(F_3)`, where `N^2 != 0`. Twisted regular representations also have the Haar law of
  Theorem 4.1. So finite level groups cannot force `A^2 = 0`, even with the anti-central law, and a proof
  must use relations with Leavitt coefficients, as in characteristic two.

## 6. Where it stands

- **Decided.**
  - The characteristic-three gate is one question (Theorem 2.1).
  - Anti-central models carry the Haar law on the signed diagonal (Theorem 4.1).
  - Root elements have the torus normal form (Proposition 5.1).
- **Open.** Whether `G` has a nontrivial characteristic-three rank model. Equivalently, whether
  `N_12^2 = 0` and `N_23 N_12 = 0` in every anti-central model; the first identity is `A^2 = 0` for the
  weight-flipping part.
- **What a construction must satisfy.** It must be free modulo `z` on reflection tori (Theorem 4.1) and far
  from monomial (`monomial-rank-models-are-hamming-models`, since `G` is nonsofic).
