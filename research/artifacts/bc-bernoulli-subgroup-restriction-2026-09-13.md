# Restricting the Bernoulli comparison to subgroup tubes: defects are invisible along every subgroup with Baum--Connes with coefficients

Lane `ex2-bc-cylinder-comparison`, 2026-09-13. Supports `bernoulli-defects-vanish-along-bcc-subgroup-tubes`
(route `-proof`). Notation follows `research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md` (RF) and
`research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md` (CC).

## 0. Setting

- `G` is countable and torsion-free, acting on `Z = G` by left translation. `Λ = {0, ..., n}` with `n >= 1`,
  `X = Λ^G`, `(g·x)_z = x_(g^(-1) z)`, `I_1 = C_0(X \ {0})`.
- A pattern is `s = (F_s, a_s)` with `F_s` finite nonempty and `a_s : F_s -> Λ \ {0}`. Its configuration is `x_s` and its
  cylinder `C_s = {x : x|_(F_s) = a_s}`. `T_r^G : ⊕_([s]) Z -> K_0(I_1 ⋊_r G)` sends `[s]` to `[1_(C_s)]`.
- `H <= G` is a subgroup and `F ⊆ G` is finite. The **tube** is `Y = HF`, a finite union of right cosets `Hf`. It is
  invariant under left multiplication by `H`, and it is a free `H`-set with finitely many orbits.
- `X_Y = {x ∈ X : supp x ⊆ Y} ≅ Λ^Y` is closed and `H`-invariant, and `(H, Y)` is again a Bernoulli datum. Write
  `T_r^(H,Y) : ⊕_([t]_H) Z -> K_0(C_0(X_Y \ {0}) ⋊_r H)` for its cylinder comparison, over `H`-orbits of patterns
  `t ⊆ Y`.
- **Regular representations.** For `x ∈ X`, `π_x` acts on `l^2(G)` by `π_x(f) δ_k = f(k^(-1)·x) δ_k` and
  `π_x(u_g) = ρ_g`, `ρ_g δ_k = δ_(k g^(-1))`. The identity `ρ_g π_x(f) ρ_g^* = π_x(g·f)` holds, so this is the regular
  representation induced from `ev_x`, in the right-regular convention. It is unitarily equivalent to the one in RF, so
  `r_x = K_0(π_x)` is the same rank functional. For `x ∈ X_Y`, `ψ_x` is the analogous representation of
  `C_0(X_Y \ {0}) ⋊_r H` on `l^2(H)`.

## 1. The restriction homomorphism

Let `A_(W,E)` be the finite sums of `f u_g` with `g ∈ E` finite and `f ∈ C(X)`, where `f` depends only on the coordinates
in a finite `W ⊆ G` and `f(y) = 0` whenever `y|_W = 0`. The union over `(W, E)` is dense in `I_1 ⋊_r G`.

**Lemma 1 (localization).** Let `a ∈ A_(W,E)` and `F' = F W^(-1) (E ∪ {e})`. For every `x ∈ X_Y`, `π_x(a)` is supported
on `l^2(HF')`: `π_x(a) = P π_x(a) P`, with `P` the projection onto `l^2(HF')`.

*Proof.* `π_x(f u_g) δ_k = f(g k^(-1)·x) δ_(k g^(-1))`. This is nonzero only if `(g k^(-1)·x)|_W ≠ 0`, that is, if
`x_(k g^(-1) w) ≠ 0` for some `w ∈ W`. So the row index `k g^(-1)` lies in `supp(x) W^(-1) ⊆ H F W^(-1)`, and the column
index `k` lies in `H F W^(-1) E`. Both are contained in `HF'`. Right multiplication preserves unions of right `H`-cosets,
which is why the right-regular convention is used. QED.

**Lemma 2 (covariance).** `π_(h·x)(a) = λ_h π_x(a) λ_h^*` for `h ∈ H`, where `λ` is left translation. `λ_h` preserves
`l^2(HF')`.

*Proof.* `λ` commutes with `ρ`, and `λ_h π_x(f) λ_h^* δ_k = f(k^(-1) h·x) δ_k = π_(h·x)(f) δ_k`. QED.

Write `HF' = ⊔_(i=1..m) H c_i`, and let `V : l^2(H) ⊗ C^m -> l^2(HF')` be the unitary `δ_h ⊗ e_i ↦ δ_(h c_i)`.

**Proposition 3 (restriction).** There is a *-homomorphism
`Res_(H,F) : I_1 ⋊_r G -> K ⊗ (C_0(X_Y \ {0}) ⋊_r H)` such that `(1 ⊗ ψ_x)(Res_(H,F) a) = V^* π_x(a) V` for every
`x ∈ X_Y` and every `a ∈ A_(W,E)`, with `m` and `V` as above for that `(W, E)`.

*Proof.*
- **Formula.** For `a = f u_g`, the `(i, j)` entry is `0` unless `η = c_i g c_j^(-1) ∈ H`. When it is in `H`, the
  entry is `φ_i u_η` with `φ_i(y) = f(c_i^(-1)·y)` for `y ∈ X_Y`.
  - **Check.** `h c_j g^(-1) = h' c_i` means `h' = h η^(-1)`. The value is
    `f(g c_j^(-1) h^(-1)·x) = f(c_i^(-1) η h^(-1)·x) = φ_i(η h^(-1)·x)`, which is the entry of `ψ_x(φ_i u_η)` at
    `(h η^(-1), h)`.
  - **Coefficients.** `φ_i` is continuous on `X_Y`. It is supported in `∪ {y : y_(c_i w) ≠ 0}` over the `w ∈ W` with
    `c_i w ∈ Y`, a compact open subset of `X_Y \ {0}`. So `Res(a) ∈ M_m(C_c(H, C_c(X_Y \ {0})))`.
- **Well defined, multiplicative, *-preserving.** The family `(ψ_x)_(x ∈ X_Y)` is faithful on
  `C_0(X_Y \ {0}) ⋊_r H`: it is the regular representation built from the faithful representation `⊕_x ev_x` of the
  coefficients. So `Res(a)` is determined by the operators `π_x(a)`, `x ∈ X_Y`. Lemma 1 lets `π_x(a)π_x(b)` be computed
  inside `l^2(HF')` once `F'` serves both `a` and `b`, so `Res(ab) = Res(a) Res(b)`, and likewise `Res(a^*) = Res(a)^*`.
- **Contractive.** `||Res(a)|| = sup_(x ∈ X_Y) ||π_x(a)|| <= ||a||`, because each `π_x` factors through the reduced
  crossed product.
- **Enlarging `F'`.** Adding cosets embeds `M_m` as a corner of `M_(m')` and changes nothing on `l^2(HF')`. So `Res`
  extends by continuity to `I_1 ⋊_r G`, with values in `K ⊗ (C_0(X_Y \ {0}) ⋊_r H)`. QED.

## 2. What the restriction does to classes

**Proposition 4.**
1. **Ranks.** For every finite-support `x ∈ X_Y \ {0}`, `r_x^H ∘ K_0(Res_(H,F)) = r_x^G`.
2. **Cylinders.** Put `K_s = {k ∈ G : k F_s ⊆ Y}`, a finite union of right `H`-cosets. Then
   `K_0(Res_(H,F)) [1_(C_s)] = Σ_(Hc ⊆ K_s) [1_(C_(c·s))]`, where `c·s = (c F_s, c·a_s)` is a pattern in `Y`.
   So `K_0(Res_(H,F))` maps `im T_r^G` into `im T_r^(H,Y)` by an explicit finite matrix.

*Proof.*
- **Ranks.** By Proposition 3, `ψ_x(Res a)` and `π_x(a)` agree up to zero blocks; pass to spectral projections of
  approximants.
- **Cylinders.** `π_x(1_(C_s))` is diagonal with entry `[x|_(k F_s) = k·a_s]` at `δ_k`. For `x ∈ X_Y` this needs
  `k F_s ⊆ supp x ⊆ Y`, so `k ∈ K_s`. Since `k f ∈ HF` for a fixed `f ∈ F_s`, `K_s ⊆ HFf^(-1)` is a finite union of
  right cosets. On the block `l^2(Hc)`, the entry at `δ_(hc)` is `[x|_(h c F_s) = h c·a_s] = 1_(C_(c·s))(h^(-1)·x)`, which
  is the diagonal of `ψ_x(1_(C_(c·s)))`. QED.

## 3. Theorem: defects restrict to zero along tubes of good subgroups

**Theorem 5.** Let `H <= G` and `F ⊆ G` finite, and suppose `T_r^(H,HF)` is surjective in both degrees. This holds when
`H` satisfies Baum--Connes with coefficients: CEKN arXiv:2210.09209, Theorem 2.8, second sentence, applied to the free
`H`-set `HF` as in item 3 of CC. Examples are amenable groups, a-T-menable groups (Higson--Kasparov), and hyperbolic groups
(Lafforgue). Then for every `y ∈ K_0(I_1 ⋊_r G)`:
1. the pattern coefficients `n_t(y)` of RF Lemma R5, over patterns `t ⊆ HF`, vanish outside finitely many `H`-orbits;
2. if every rank `r_x(y)` vanishes, then `K_0(Res_(H,F))(y) = 0`;
3. `K_1(Res_(H,F)) = 0` on `K_1(I_1 ⋊_r G)`.

*Proof.*
- **Item 3.** `K_1(C_0(X_Y \ {0}) ⋊_r H) = T_r^(H,Y)(0) = 0`.
- **Item 1.** RF Lemmas R1--R3 and R5 hold verbatim for the free `H`-set `Y`. By surjectivity,
  `Res(y) = T_r^(H,Y)(m)` for a finitely supported `m`, and `m = n^H(Res(y))`. For a pattern `t ⊆ Y`, every
  sub-pattern `u <= t` lies in `Y`. The Möbius formula of R5 uses only ranks at the configurations `x_u`, and
  Proposition 4.1 gives `r^H_(x_u)(Res y) = r^G_(x_u)(y)`. So `n_t(y) = m_([t]_H)`, which is finitely supported.
- **Item 2.** All ranks vanish, so `m = 0` and `Res(y) = T_r^(H,Y)(0) = 0`. QED.

**Corollary 6 (where a Bernoulli witness can live).** Let `G` be torsion-free, and let `y` be a class outside `im T_r^G`,
of one of the shapes of `bernoulli-assembly-injective-beyond-the-host`.
- **Shapes (b) and (c).** The class restricts to zero along every tube `HF` of a subgroup `H` satisfying Baum--Connes with
  coefficients.
- **Shape (a).** The infinitely many `G`-orbits of patterns carrying coefficients escape every such tube: for each such
  `(H, F)`, only finitely many of them have a translate inside `HF`.
  - **Why.** A `G`-orbit `[t]` with `g t ⊆ HF` meets `X_(HF)` in finitely many `H`-orbits, because
    `g ∈ HF f^(-1)` for any `f ∈ F_t`. Theorem 5.1 allows only finitely many nonzero `H`-orbits.
- **Consequence.** Pattern families concentrated near infinite cyclic, free, hyperbolic or amenable subgroups carry only
  finite expansions. The obvious one-dimensional "thin ghost" candidates, such as spectral projections supported along
  a cyclic subgroup, cannot produce a witness. Over an expander monster, a shape-(a) witness must spread its coefficients
  over patterns that no single good subgroup tube contains.

## 4. Model tests

- **`H = {e}`.** `Res_({e},F)` is the finite family of ranks at configurations supported in `F`, and Theorem 5 adds
  nothing. As expected: the trivial group is good, and it sees only finitely many patterns.
- **`H = G` satisfying Baum--Connes with coefficients, `F = {e}`.** `Res` is the identity and Theorem 5 is CEKN's
  isomorphism.
- **`G = Z`, `H = 2Z`, `F = {0, 1}`.** `Y = Z` and `X_Y = X`, and `Res` views the `Z`-system as a `2Z`-system on
  `l^2(Z) = l^2(2Z) ⊗ C^2`. Cylinders of `Z`-orbits split into two `2Z`-orbits, as Proposition 4.2 says.
- **A theorem that detects nothing is excluded.** For a class of shape (a), Theorem 5.1 is a genuine restriction: it
  forbids, for instance, coefficients `n_t = 1` on every path `t = {g, g^2, ..., g^L}` along one infinite cyclic
  subgroup.

## 5. Scope and novelty

- `G` is torsion-free throughout. The version for hosts with torsion, with `R(G_s)` coefficients, is not written.
- The restriction homomorphism is elementary. It works because regular representations at configurations supported in a
  tube live on the tube. Bounded novelty check: not in CC, RF, or CEKN Sections 1--2. No other literature check was
  possible (web search exhausted).
- Theorem 5 constrains where a witness lives. It does not decide `bernoulli-cylinder-comparison-fails-for-some-group`.
