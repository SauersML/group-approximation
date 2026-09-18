---
rg: 2
id: depth-distortion-power-conjugates-leavitt-hosts-proof
kind: route
title: Leavitt monomials shift cylinder depth and support measure by bounded amounts, so growth rates are conjugacy invariant and homogeneous; iterating b^m a b^-m = a^(2^m) through b = t a t^-1 gives the tower bound
target: depth-distortion-obstructs-power-conjugates-in-leavitt-hosts
requires: []
---

Notation is as in the target claim. For `f = 0` put `depth 0 = 0`; every supremum runs over `f ≠ 0`.

## Step 0: the hosts

**Leavitt units.** The algebra `L = L_K(1,2)` has generators `x_1, x_2, y_1, y_2` with `y_i x_j = δ_ij` and
`x_1 y_1 + x_2 y_2 = 1`. It acts on `C_1` by

- `(x_i f)(w) = [w_1 = i] f(σw)`,
- `(y_i f)(w) = f(iw)`,

where `σ` is the shift. The relations check directly:

- `(y_j x_i f)(w) = (x_i f)(jw) = [i=j] f(w)`;
- `Σ_i (x_i y_i f)(w) = f(w_1 σw) = f(w)`.

Every element of `L` is a finite `K`-combination of monomials `x_p y_q`, with `p, q` words in `{1,2}`. Here
`(x_p y_q f)(w) = [w begins with p] f(q·σ^{|p|}w)`. If `f ∈ V_k`, then `y_q f ∈ V_{max(k−|q|,0)}` and
`x_p y_q f ∈ V_{|p| + max(k−|q|,0)} ⊂ V_{k+|p|}`. Also

- `supp(x_p y_q f) = p·(q^{-1} supp f)`;
- `μ(q^{-1}E) ≤ 2^{|q|} μ(E)`;
- `μ(p·E') = 2^{-|p|} μ(E')`.

So `μ(supp x_p y_q f) ≤ 2^{|q|−|p|} μ(supp f)`.

Now take `d` coordinates. The locally constant functions on `X^d` form the algebraic tensor product
`C_1^{⊗d}`, since `V_k(X^d) = V_k(X)^{⊗d}`. `L^{⊗d}` acts coordinatewise. A monomial
`⊗_i x_{p_i} y_{q_i}` raises depth by at most `max_i |p_i|` and multiplies support measure by at most
`2^{Σ(|q_i|−|p_i|)}`.

For a sum of monomials, two facts give the bounds:

- depth of a sum is at most the maximum depth;
- the support of a sum lies in the union of the supports.

So for `u = Σ_j c_j M_j` we get `s(u) ≤ max_j s(M_j)` and `m(u) ≤ Σ_j m(M_j)`, both finite. Applying this to
`u^{-1}` puts every unit of `L^{⊗d}` in `BDep_d(K) ∩ BSD_d(K)`.

Faithfulness:

- `L_K(1,2)` is simple with center `K`.
- A central simple algebra tensored with a simple algebra is simple, so `L^{⊗d}` is simple.
- The representation is nonzero, so it is faithful.

**Brin--Thompson `dV`.** An element `v ∈ dV` maps finitely many dyadic boxes `B_j` onto boxes `C_j` by prefix
replacement in each coordinate. Then `f ↦ f∘v^{-1}` is `Σ_j ⊗_i x_{p^{(j)}_i} y_{q^{(j)}_i}`, where `p` are the
range prefixes and `q` the domain prefixes, so it is a unit of `L^{⊗d}`. It is also covered by the direct estimates:
depth rises by at most the longest range prefix, and the Radon--Nikodym derivative takes finitely many values.

`BDep` and `BSD` are groups, because `s(ST) ≤ s(S) + s(T)` and `m(ST) ≤ m(S) m(T)`.

## Step 1: rates exist and are invariants

**Depth.**

- **Nonnegativity.** Suppose `s(T) ≤ −1`. Then `T V_k ⊂ V_{k−1}` for every `k ≥ 1`. But `T` is injective and
  `dim V_k = |{1,2}^{dk}| > dim V_{k−1}`, a contradiction. So `s(T) ≥ 0`.
- **Limit.** `n ↦ s(T^n)` is subadditive and nonnegative, so by Fekete the limit `δ(T) = lim s(T^n)/n` exists.
  Hence `ε(T) = max(δ(T), δ(T^{-1})) = lim E_T(n)/n` exists.
- **Conjugation.** Let `g ∈ BDep`. For every `f`,
  `depth(g T^n g^{-1} f) ≤ s(g) + depth(T^n g^{-1} f) ≤ s(g) + s(T^n) + s(g^{-1}) + depth f`.
  So `E_{gTg^{-1}}(n) ≤ E_T(n) + s(g) + s(g^{-1})`, and symmetrically. Dividing by `n` gives
  `ε(gTg^{-1}) = ε(T)`.
- **Homogeneity.** `E_{T^k}(n) = E_T(|k|n)`, so `ε(T^k) = |k| ε(T)`.

**Support.** `n ↦ log₂ m(T^n)` is subadditive. It is bounded below by `−n log₂ m(T^{-1})`, because
`μ(supp f) ≤ m(T^{-n}) μ(supp T^n f)` gives `m(T^n) m(T^{-n}) ≥ 1`. So `λ(T) = lim log₂ m(T^n)/n` exists and is
finite, and `ℓ(T) = max(λ(T), λ(T^{-1})) ≥ 0`. The conjugation and homogeneity arguments are the same, with
products in place of sums.

## Step 2: power conjugates

Suppose `g T g^{-1} = T^k` with `|k| ≥ 2`. By Step 1, `ε(T) = ε(T^k) = |k| ε(T)` with `ε(T)` finite, so
`ε(T) = 0`.

Quantitatively, `T^{k^m} = g^m T g^{-m}`. So `E_T(|k|^m) ≤ E_T(1) + s(g^m) + s(g^{-m})`. By subadditivity
`s(g^{±m}) ≤ m·max(s(g), s(g^{-1}))`, which gives the stated bound. `ℓ` works the same way.

## Step 3: the Baumslag--Gersten tower bound

Let `A = ρ(a)`, `B = ρ(b) = T A T^{-1}` with `T = ρ(t)`, and `σ_T = s(T) + s(T^{-1})`. The relation
`b a b^{-1} = a^2` gives `A^{2^m} = B^m A B^{-m}` and `A^{-2^m} = B^m A^{-1} B^{-m}`. Hence

- `s(A^{±2^m}) ≤ s(B^m) + s(A^{±1}) + s(B^{-m})`;
- `s(B^{±m}) = s(T A^{±m} T^{-1}) ≤ s(A^{±m}) + σ_T`.

So `E_A(2^m) ≤ 2E_A(m) + c` with `c = E_A(1) + 2σ_T`.

Put `x_i = E_A(N_i)` with `N_{i+1} = 2^{N_i}`. Then `x_{i+1} + c ≤ 2(x_i + c)`, so
`x_i ≤ 2^i (E_A(1) + c)`.

The support version is the same computation for `log₂ m(A^{±n})`, with `c' = log₂ max(m(A), m(A^{-1})) +
2 log₂(m(T) m(T^{-1}))`. It uses `m(gSg^{-1}) ≤ m(g) m(S) m(g^{-1})`.

**Killed class.** Suppose `E_A(n) ≥ α log^{(j)} n` for all large `n`. At `n = N_i` this gives
`α N_{i−j} ≤ C 2^i`. But `N_{i−j}` is a tower of height `i−j`, which exceeds `C 2^i / α` once `i` is large. This
is a contradiction.

## Step 4: bounded depth over a finite field

Let `c = sup_n E_T(n) < ∞`. Then `U_k = span{T^n V_k : n ∈ Z} ⊂ V_{k+c}` is finite-dimensional and `T`-invariant.
When `K` is finite, `GL(U_k)` is a finite group, so `T|U_k` has finite order. Every `f` lies in some `V_k`, so `T`
is locally periodic.

### Step 4b: a locally periodic Baumslag--Gersten generator is trivial

This is the argument of `baumslag-gersten-equicontinuity-smallest-prime-proof`, run for the permutation action of
`BG` on the set `W`. Let `A = ρ(a)`, `B = ρ(b)`, `T = ρ(t)`, and suppose every `A`-orbit in `W` is finite.

**(i) `B` is locally periodic.** `B^k(Tf) = T A^k f`, so `B` has finite orbits.

**(ii) All `A`-periods are odd.** Write `per(f)` for the `A`-orbit length of `f`.

- From `A^2 B = B A` we get `per_{A^2}(Bf) = per(f)`, and `per_{A^2}(g) = per(g)/gcd(2, per(g))`.
- If `per(f)` is even, then `per(Bf)` cannot be odd, because then it would equal `per(f)`. So
  `per(Bf) = 2 per(f)`.
- Iterating, `v_2(per(B^m f)) = v_2(per f) + m` for all `m ≥ 0`.
- But `B^r f = f` for some `r ≥ 1` by (i), a contradiction. So every period is odd.

**(iii) The closures.** Give `Sym(W)` the pointwise topology, which makes it a topological group.

- `Â`, the closure of `<A>`, lies in the product of the finite cyclic groups acting on the `A`-orbits. So `Â` is a
  procyclic profinite group.
- By (ii), every finite quotient of `Â` has odd order. Let `P` be its set of primes, so `2 ∉ P`.
- `B̂ = T Â T^{-1}` has the same prime set.

**(iv) Squaring action.** For `x ∈ Â`, `B^n x B^{-n} = x^{2^n}` by continuity from `x = A`.

- If `y = lim B^{n_i} ∈ B̂`, then `y x y^{-1} = lim x^{2^{n_i}} ∈ Â`. Squaring is invertible on `Â` because
  `2 ∉ P`, so this gives a continuous action `ψ : B̂ → Aut(Â)` with `ψ(B) = squaring`.
- Suppose `A ≠ 1` and let `p` be the least prime in `P`. The finite quotient `Â/Â^p ≅ Z/p` is preserved by `ψ`, so
  `ψ` induces a homomorphism `B̂ → (Z/p)^×` with finite image.
- That image is a quotient of `B̂`, so its order has all prime factors in `P`. It also divides `p − 1`, whose prime
  factors are all `< p`. So the image is trivial.
- Hence `2 ≡ 1 mod p`, which is impossible. So `P = ∅` and `A = 1`.

**Finite-field consequence.** If `K` is finite and `sup E_A < ∞`, then `A` is locally periodic by Step 4, so it
has finite orbits, and `A = 1`.

### Step 4c: counting over a finite field

Let `K = F_q`, `T ∈ BDep_d(K)`, and let `f ∈ V_k` have an infinite `T`-orbit. Fix `D ≥ 0` and put
`X_D = {n ∈ Z : s(T^n) ≤ D}`. For `n ∈ X_D`, the restriction `T^n|V_k` is a linear map `V_k → V_{k+D}`.

- If `n ≠ n'` in `X_D` give the same restriction, then `T^{n−n'}` fixes `V_k` pointwise, because `T` is
  injective. Then the orbit of `f` has at most `|n − n'|` elements, a contradiction.
- So `n ↦ T^n|V_k` is injective on `X_D`. Its target has `q^(dim V_k · dim V_{k+D}) = q^(2^{dk}·2^{d(k+D)})`
  elements, which bounds `|X_D|`.
- Every `X_D` is finite, so `s(T^n) → ∞` as `|n| → ∞`.
- **Running maximum.** Put `F = max_{0≤m≤n} s(T^m)`. The `n+1` maps `T^m|V_k`, `0 ≤ m ≤ n`, are pairwise distinct
  by the same argument and lie in `Hom(V_k, V_{k+F})`. So `n + 1 ≤ q^(2^{d(2k+F)})`, which gives
  `F ≥ log₂(log_q(n+1))/d − 2k`.

### Step 4d: the profile window for BG

Let `ρ : BG → BDep_d(F_q)` be faithful. Then `A = ρ(a) ≠ 1`, so by Step 4b `A` is not locally periodic, and some
`f ∈ V_k` has an infinite orbit. Step 4c gives divergence, the counting bound and the `log log` lower bound.

**Upper bound `C₁ log n`.** Only `B A B^{-1} = A^2` is used. Let `0 < n < 2^M` with binary digits at positions
`m_1 < ... < m_r`, so `r ≤ M` and `m_r < M`. Then
`a^n = Π_j b^{m_j} a b^{−m_j} = b^{m_1} a b^{m_2−m_1} a ⋯ a b^{m_r−m_{r−1}} a b^{−m_r}`.
By subadditivity, `s(A^n) ≤ m_r s(B) + r s(A) + m_r s(B^{-1}) ≤ M (s(B) + s(B^{-1}) + s(A))`. Inverting the word
gives the same bound for `s(A^{-n})`. With `M = ⌈log₂(n+1)⌉`, this yields `E_A(n) ≤ C₁ log n` for `n ≥ 2`.

**Why counting cannot close DG.** A word of length `ℓ` in `a^{±1}, t^{±1}` that equals `a^n` gives
`E_A(n) ≤ ℓ·max(E_A(1), s(T), s(T^{-1}))`. Such words number at most `4^ℓ`, which is far below the doubly
exponential bound of Step 4c. So Step 4c is consistent with every placement, and DG needs structure beyond the
dimension count.

**Conditional reduction.** Let `ρ` be faithful, so `A ≠ 1`, over a finite field. Then `E_A` is unbounded. If DG
also held, some `α, j` would give `E_A(n) ≥ α log^{(j)} n` for large `n`, contradicting Step 3.

## Step 5: calibration on V

- **Torsion.** If `v^r = 1`, then `E_v` is bounded by `max_{0≤j<r} E_v(j)`, so `ε(v) = 0`.
- **Attracting cycle.** Suppose `v` has an attracting cycle of cones: a word `α`, a nonempty word `γ` and `p ≥ 1`
  with `v^p(αw) = αγw` for all `w`. Let `u f = f∘v^{-1}`. Then `u^{pj} 1_{[α]} = 1_{[αγ^j]}`, which has depth
  `|α| + j|γ|`. So `ε(v) ≥ |γ|/p > 0`.
- **Infinite order.** Every infinite-order element of `V` has such a cycle. This is Brin's revealing-pair analysis
  (M. Brin, *The chameleon groups of Richard J. Thompson*, Publ. IHES 84, 1996), recast by Salazar-Díaz
  (*Thompson's group V from a dynamical viewpoint*, IJAC 20, 2010): an element is torsion iff a revealing pair has
  no attractors. A power of an attractor component acts as the prefix replacement above.

Steps 1–2 hold in any group of `BDep_1(K)` containing `V`, for example `L_K(1,2)^×`. So no infinite-order `v ∈ V` is
conjugate there to `v^k`, `|k| ≥ 2`.

Numerical check (`experiments/leavitt-depth-rate-2026-09-17/results.txt`): Thompson's `x_0` has
`s(u^n) = n` for `n ≤ 12`, and the order-2 swap has `s(u^n) = 0`.

## Step 6: sharpness

**Over `Q`.** `M_2(Q)` embeds in `L_Q(1,2)` by `[[p,q],[r,s]] ↦ x_1 p y_1 + x_1 q y_2 + x_2 r y_1 + x_2 s y_2`.
Every power of `a = [[1,1],[0,1]]` has scalar entries, so it has depth shift at most 1. With `t = diag(2,1)` this
embeds `BS(1,2)` with `ε(a) = ℓ(a) = 0`. The theorem therefore does not exclude `BS(1,2)`, which is consistent with
`BS(1,2)` being linear.

**Over `F_2`.** Take `u = [[x_1,1],[1,0]]`. Its inverse is `[[0,1],[1,x_1]]`, since `char 2` makes `det = 1`. The
entries of `u^n` are polynomials in `x_1` of degree `n`, with leading term `x_1^n`, so `s(u^n) ≥ n`. The script
reports `s(u^n) = n` for `n ≤ 12`.

The support ratio stays bounded:

- `p(x_1) g` is supported in `∪_j 1^j·supp g`, whose measure is at most `2 μ(supp g)`;
- each of the four matrix-unit terms contributes at most a factor `4`.

So `m(u^n) ≤ 16` for all `n`, which gives `ℓ(u) = 0` and `ε(u) = 1`.

**Caveat on the script.** `results.txt` records support ratios only over cylinders of length at most 3. They are
lower bounds for `m(u^n)`, not the full supremum. The depth column is exact for those cylinders, and it gives a lower
bound for `s(u^n)`.
