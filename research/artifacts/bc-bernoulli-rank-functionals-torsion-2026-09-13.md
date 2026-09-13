# Bernoulli comparison over hosts with torsion: representation-valued ranks

Lane `ex-bc-measured-coefficient`, 2026-09-13. Extends Section 1 of
`research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md` (RF) and item 4 of
`research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md` (CC) from torsion-free hosts to every countable `G`.
Supports `bernoulli-assembly-injective-beyond-the-host`.

## 0. Setting

- `G` is countable discrete and `Z` a countable `G`-set with finite point stabilizers.
- `Λ = {0, ..., n}` with `n >= 1`, `X = Λ^Z`, `I_1 = C_0(X \ {0})`.
- `S` is the set of patterns `s = (F, a)`, with configurations `x_s` and cylinders `C_s`. Every stabilizer `G_s` is
  finite: it permutes `F`, so it has a finite-index subgroup fixing `F` pointwise, which is contained in a point
  stabilizer.
- `R(K)` denotes the representation group of a finite group `K`.
- `ρ : c_0(S) -> K(l^2 S) ⊗ I_1`, `delta_s ↦ e_(ss) ⊗ 1_(C_s)`, is equivariant for `Ad(lambda_S) ⊗ shift`. Put
  `Θ = [ρ]` composed with the equivariant Morita isomorphism, and `T_r = K_*(Θ ⋊_r G)`.
- Green imprimitivity gives `K_0(c_0(S) ⋊_r G) = ⊕_([s]) R(G_s)` and `K_1 = 0`. The class `[τ] ∈ R(G_s)` is
  represented by `delta_s p_τ`, where `p_τ ∈ C*(G_s)` is a minimal projection of the isotypic block of `τ`.

## 1. `Θ` is a weak K-equivalence for every `G`

**Claim W.** For every finite `H <= G`, `K_*(Θ ⋊ H) : K_*(c_0(S) ⋊ H) -> K_*(I_1 ⋊ H)` is an isomorphism.

*Proof.*
- **Finite windows.** Take finite `H`-invariant `W ⊆ Z`. `I_1^W = {f ∘ pr_W : f ∈ C(Λ^W), f(0) = 0} ≅ C(Λ^W \ {0})` is
  an `H`-subalgebra of `I_1`, since `f ∘ pr_W` is supported in the compact open set `∪_(w ∈ W) U_w`. These subalgebras
  increase with `W` and their union is dense.
- **The source.** Likewise `c_0(S)` is the increasing union of `c_0(S_W)`, the patterns with `F ⊆ W`. `ρ` maps
  `c_0(S_W)` into `K(l^2 S_W) ⊗ I_1^W`.
- **Colimit.** K-theory of crossed products by the finite group `H` commutes with these inductive limits. So it suffices
  to treat a fixed `W`.
- **Level `W`.** `s ↦ x_s|_W` is an `H`-equivariant bijection `S_W -> Λ^W \ {0}`. Both `K_0` groups equal
  `⊕_([t] ∈ H\S_W) R(H_t)`, and both `K_1` groups vanish.
- **The image of a generator.** Take a representative `s` and `[σ] ∈ R(H_s)`, represented by `delta_s p_σ`. The
  untwisting isomorphism `(K ⊗ A) ⋊ H ≅ K ⊗ (A ⋊ H)`, `(k ⊗ a) u_h ↦ k lambda_h ⊗ a u_h`, uses
  `e_(ss) lambda_h = e_(ss)` for `h ∈ H_s`. It sends `ρ(delta_s) p_σ` to `e_(ss) ⊗ 1_(C_s) p_σ`.
- **Splitting over orbits.** Now `1_(C_s) = Σ_O 1_O` over the `H_s`-orbits `O` of points of `Λ^W \ {0}` extending
  `s`, and each `1_O` commutes with `C*(H_s)`. The orbit `O = {s}` contributes `[σ]` in the summand `R(H_s)` of `[s]`.
  Every other orbit consists of points with strictly larger support.
- **Conclusion.** Ordered by support size, the matrix of `K_0(ρ ⋊ H)` is block unitriangular over `Z`, with finitely
  many blocks, so it is invertible. QED.

Consequently the proof of CC item 3 applies with `T = Θ` for every `G`. The cylinder description holds with
`R(G_s)` coefficients: `T_r[τ ⊗ delta_s] = [1_(C_s) p_τ]`.

## 2. Representation-valued ranks and injectivity

**Lemma R1'.** Let `x` be a pattern configuration with stabilizer `G_x`, and let `σ` be an irreducible representation of
`G_x` on `H_σ`. Since `ev_x` is `G_x`-invariant, `(ev_x, σ)` is covariant. Put `π_(x,σ) = Ind_(G_x)^G (ev_x, σ)`, on
`l^2(G ×_(G_x) H_σ)`, where `f ∈ C(X)` acts by `f(g x)` on the fibre over `g G_x` and `u_h` translates. Then
`π_(x,σ)` factors through `C(X) ⋊_r G` and maps `I_1 ⋊_r G` into the compacts.

*Proof.*
- **Reduced.** Representations of `C(X) ⋊ G_x` are weakly contained in its regular representations because `G_x` is
  finite. Induction preserves weak containment, and it carries regular representations to regular representations.
- **Compacts.** For `f ∈ C_c(X \ {0})`, `supp f ⊆ ∪_(i<=m) U_(z_i)`. Now `g x ∈ U_z` iff `g^(-1) z ∈ supp x`, which
  allows at most `|supp x| · |G_z|` elements `g`. So `π_(x,σ)(f)` has finite rank. QED.

Put `r_(x,σ) = K_0(π_(x,σ)) : K_0(I_1 ⋊_r G) -> Z`.

**Lemma R2'.** Let `|F_s| = |supp x|`. Then `r_(x,σ)(T_r[τ ⊗ delta_s])` is `0` unless `s ∈ G·x`. For `s = x` it equals
the multiplicity of `τ` in `σ`, which is `1` if `τ ≅ σ` and `0` otherwise. For `|F_s| > |supp x|` it is `0`.

*Proof.*
- **Invariant subspace.** `π(1_(C_s))` projects onto the fibres over the cosets `g G_x` with `g x ∈ C_s`. The finite
  group `G_s` preserves `C_s`, so the subspace `V` of those fibres is `π(G_s)`-invariant.
- **Rank.** `p_τ` is a minimal projection of the `τ`-block, so the rank of `π(1_(C_s) p_τ)` is the multiplicity of `τ`
  in `V`.
- **Size condition.** If `|F_s| > |supp x|`, then `V = 0`. If `|F_s| = |supp x|`, then `g x ∈ C_s` forces `g x = x_s`.
  So `V ≠ 0` iff `s ∈ G x`.
- **The case `s = x`.** Only the coset `G_x` occurs, and `V = H_σ`. `G_x` acts on it through `σ`: `ξ(k^(-1)) = σ(k) ξ(e)`
  for `ξ(gk) = σ(k)^(-1) ξ(g)`. QED.

**Proposition R3' (injectivity over any host).** `T_r : ⊕_([s]) R(G_s) -> K_0(I_1 ⋊_r G)` is injective, and `T_r` is
injective in degree 1 because the source is `0`.

*Proof.* Let `m = (m_([s]))` be finitely supported with `T_r(m) = 0`, and suppose `m ≠ 0`. Choose `[s']` with
`m_([s']) ≠ 0` and `|F_(s')|` minimal, and represent that orbit by `s'` itself. Put `x = x_(s')`. By R2', for every
irreducible `σ` of `G_x`:
- components of larger size contribute `0`;
- by minimality there are no smaller components;
- same-size components from other orbits contribute `0`.

So `0 = r_(x,σ)(T_r m) = ⟨σ, m_([s'])⟩`, the coefficient of `σ` in the virtual representation `m_([s'])`. Every
coefficient vanishes, so `m_([s']) = 0`, a contradiction. QED.

**Corollary R4' (every host).** For every countable `G` and every `G`-set `Z` with finite point stabilizers:
- `mu_(G, I_1)` is injective in both degrees;
- `mu_(G, C(Λ^Z))` is injective iff `mu_G` is (CC items 1 and 3);
- for `n = p - 1`, reduced assembly for `F_p wr_Z G` is injective iff reduced assembly for `G` is. This combines item 2
  of `amenable-kernel-bc-transfer-and-ktop-half-exactness`, which is Chabert--Echterhoff Corollary 3.5 and needs no
  torsion hypothesis.

## 3. Comparison with the known monster failure

Willett--Yu I (arXiv:1012.4150, Corollary 1.7, read from the text extraction) give, for a group containing a coarsely
embedded large-girth expander, a (commutative) coefficient `A` at which assembly "is injective" but "is not
surjective", while the maximal assembly map is an isomorphism. R4' gives the same sign beyond the host at every Bernoulli
coefficient. Injectivity holds for every host, and only surjectivity of `T_r` remains.

## 4. Model tests

- `G = Z/2` acting on `Z = G`, `n = 1`. Here `X = {0,1}^2`, and `I_1` is functions on the three nonzero points,
  `S ≅ Λ^Z \ {0}`. Crossed products by `G` are finite dimensional and assembly is an isomorphism. The support-2 pattern
  `(1,1)` has `G_s = Z/2`, so it contributes `R(Z/2) = Z^2`. The two support-1 patterns form one free orbit and
  contribute `Z`. So the source is `Z^3`. `K_0(C({three points}) ⋊ Z/2) = R(Z/2) ⊕ Z = Z^3`. `T_r` is unitriangular,
  as Claim W says.
- Torsion-free `G`: `R(G_s) = Z`, `σ` is trivial, and R1'--R3' reduce to RF R1--R3.
