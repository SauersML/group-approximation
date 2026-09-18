# Referee report (gq-referee-c): resolvent-presentation-ring-is-residually-finite

- **Nodes** (landed 8abfde57d by lane `gq-infinite-primes`):
  - `research/resolvent-presentation-ring-is-residually-finite.md` and its `-proof`;
  - `research/resolvent-ring-has-path-normal-form.md` and its `-proof`.
- **Lens:** independent re-derivation, trying to break it at the points the author named:
  - the torsion bookkeeping;
  - the case where the `D`-part and the ideal part mix;
  - `l = 2`.
- **Verdict: PASS** for both nodes, for every prime `l`. One wording nit, which does not affect the proof: in the
  `δ ≠ 0` case the copy index `t + k` matches `δ = Σ f_k x^k`, with coefficients on the left, not `Σ x^k f_k`.

`R_l = Z<u,x,x',B,e | xx' = x'x = 1, xu = (u+l)x, B(u+1) = (u+1)B = 1, ue = eu = 0, e^2 = e>`.

## 1. The normal form (re-derived)

**D.**
- In the ring `U` of the first five relators, `b_k = x^k B x^(-k)` inverts `u+1+kl`. So `C = ⟨u, b_k⟩` is
  commutative and is a quotient of `A = Z[u][(u+1+kl)^(-1)]`.
- `U -> D = A[x^(±1); σ]` is onto and restricts to the identity on `A`. `D` is free over `A` on the powers of
  `x`, so `U ≅ D`.
- Setting `e = 0` gives `R_l/(e) = U`, hence `D ⊆ R_l` and `D ∩ (e) = 0`. ✓

**The corner ring θ.** I re-derived it without the input node.
- `e b_k (u+1+kl) e = e` and `e b_k u e = 0` give `(1+kl) · e b_k e = e`.
- Every integer `m` prime to `l` divides some `1 + kl`, namely `m^(l-1)`. For `l = 2` every odd `m` already has
  that form. So `θ : Z_(l) -> eR_le` exists.
- Put `X = b_k e` and `Y = e b_k e`. Both satisfy `(1+kl)X = e = (1+kl)Y`; for `X` this uses
  `b_k(u+1+kl) = 1` and `ue = 0`. So `X = Xe = X(1+kl)Y = ((1+kl)X)Y = eY = Y`. Hence
  `f e = θ(f(0)) = e f` for all `f ∈ A`. ✓

**Modules.**
- `A/uA = Z[(1+kl)^(-1)] = Z_(l)`.
- `M = W ⊗_D V = D/(uD + Du) = ⊕_k x^k A/(uA + klA) = Z_(l) ⊕ ⊕_(k≠0) Z/l^(v(k)+1)`.
- On `N`, the left and right `Z_(l)`-actions agree, because `f(-kl) - f(0) ∈ kl Z_(l)`. ✓

**Centrality and torsion in the corner.**
- `e x^k u e = 0` and `e(u+kl)x^k e = kl · e x^k e`, so `kl · e x^k e = 0`.
- With `θ((k/l^(v(k)))^(-1))`, this gives `l^(m_k) e x^k e = 0`, and `θ(Z_(l))` is central in `eR_le`. That makes
  `ψ_T : T(N) -> eR_le` well defined. ✓

**R' and the two maps.**
- `R' = D ⊕ (V ⊗ T ⊗ W)` is associative, because the pairing `μ` is balanced over `D`.
- `φ : R_l -> R'`, sending `e` to `v_0 ⊗ 1 ⊗ w_0`, satisfies the relators, since `uv_0 = 0` and `w_0 u = 0`. It is
  onto.
- `ψ` is well defined. The key identity `ψ_W(w)ψ_V(v') = ψ_T(μ(w,v'))` holds, by
  `e x^k f e = e x^k e θ(f(0))`.
- `ψφ = id` on generators, so `R_l ≅ R'`. ✓

**Torsion bookkeeping.**
- `N^(⊗s) = ⊕_K Z/l^(min m_(k_i))`, and `V`, `W` are free over `Z_(l)` on the `x^a v_0` and `w_0 x^b`.
- So `(e) = ⊕ G_K [a|K|b]` with the stated groups.
- The multiplication rules follow from `f x^a = x^a f(u - al)`. ✓

## 2. Residual finiteness (re-derived)

**The modules (r, N, g, E).**
- `u = lj` is well defined on `j ∈ Z/N`, because `l^(r-1) | N`.
- The only nontrivial relator is `xu = (u+l)x` at the wrap, where `lN ≡ 0 (mod l^r)`.
- `eu = 0` because `e` is supported on `V_0`, where `u = 0`. ✓

**Action of a path.** `x^N = g` on every `V_j`, with exactly one wrap per `N` steps.
- Starting from `V_0`, `x^a` wraps `⌈a/N⌉` times. This holds for negative `a` too, where the wraps apply
  `g^(-1)`.
- Starting from `V_(ρ')`, `x^b` wraps `⌊b/N⌋` times.
- So `[a|K|b]` acts as the block `g^(⌈a/N⌉) E g^(k_1/N) E ⋯ E g^(⌊b/N⌋)` from `V_(b mod N)` to `V_(-a mod N)`, when
  `N` divides every `k_i`. It acts as 0 otherwise. ✓

**Density.**
- The idempotents:
  - for odd `l`, `ε = (1+s)/2` in `F_l[C_2]`;
  - for `l = 2`, `ε = 1+s+s^2` in `F_2[C_3]`, where `ε^2 = 1 + s^2 + s^4 = ε`.
  - For `l = 2` a group of order 3 is forced: `F_2[C_2]` is local and has no nontrivial idempotent.
- The top word `z^α s z^(n_1) s ⋯ s z^β` is reduced and occurs only in the all-`s` expansion of `w_(τ*)`:
  - choosing `1` in some `ε` merges two `z`-powers and drops a letter;
  - choosing `s^2` changes a letter.
- So its coefficient is `λ_(τ*) c^(s+1) ≠ 0`.
- `Z * C_m` is virtually free, hence residually finite. A finite quotient `Q` injective on the finitely many
  group elements keeps this coefficient, and the regular representation of `F_l[Q]` is faithful. ✓

**Separation.** The two parts can mix, and both cases are handled.
- **Case δ ≠ 0.** Take `E = 0`, so the whole ideal `(e)` acts as 0 and only `δ` is seen. Choose an integer `t` with
  `f_k(lt) ≠ 0`; this is defined, since the denominators `1 + (t+j)l` are units. Choose `r` so that
  `f_k(lt) ∉ l^r Z_(l)`. Choose `N` larger than the `x`-spread. Distinct `k` land in distinct copies, so the
  coefficient `f_k(lt) mod l^r` survives. ✓
- **Case δ = 0.** Take `ν = min v(c_τ)`, `r = ν+1` and `N = l^ν`.
  - For `τ ∈ F_0` with `s >= 1`: `ν <= v(k_i)`, since `ν < m_K`. So `N | k_i`.
  - For `τ ∉ F_0`: either `l^(ν+1) | c_τ`, or some `N ∤ k_i`. In both cases `c_τ[τ]` acts as 0. This is consistent
    with the order of `[τ]` because the module is an `R_l`-module.
  - The `F_0`-part is `l^ν Y` with unit coefficients `c'_τ`. Distinct `τ` in one block pair give distinct density
    tuples `(⌈a/N⌉; k/N; ⌊b/N⌋)`.
  - So `Y ≢ 0 (mod l)`. Lift `g_0` and `E_0`, using idempotent lifting modulo the nilpotent ideal `(l)`. Then
    `l^ν Y ≠ 0` over `Z/l^(ν+1)`. ✓

## 3. Calibration

- **Why `Z_(l)` and not `Q`.** Separation of the ideal part rests entirely on the `l`-adic valuation `ν` and the
  quotients `Z/l^(ν+1)`. `Q` has no finite quotients, so no residually finite ring contains `Q` unitally in a
  corner. `Z_(l) ⊆ Z_l` is residually finite, and the proof uses exactly that.
- **Why the resolvent is needed.** Dropping `B` removes the inverses of `1 + kl`. Then the corner is `Z`, not
  `Z_(l)`, and residual finiteness is easier but pointless.
- **Consequences.** A residually finite, finitely presented ring has decidable word problem.
  `E_N(R_l) ≤ GL_N(R_l)` is residually finite, entrywise through finite quotient rings, and contains `Z_(l)`
  through `e_12(θ(q))`. ✓
- **Finite presentation of the Steinberg group.** `St_N(R_l)` is finitely presented for `N >= 5`
  (`gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md`). This agrees with the node's reduction of
  the bottleneck to the kernel of `St_N(R_l) -> E_N(R_l)`.
