# The unstable Steinberg kernel of a Z^2 crossed product is nonzero

Lane `swarm-rigid-sft-elementary-group-mod`, 2026-09-16. Target of the lane:
`rigid-sft-elementary-group-mod-centre-is-fp`. This artifact proves the claim
`z2-crossed-product-steinberg-kernel-is-nonzero`. The only import is
`steinberg-group-homology-gives-k2-and-k3` (ii): for every associative unital ring `S` and
`n >= 5`, every central extension of `St_n(S)` splits (Weibel, *The K-book*, III Proposition 5.5.1,
quoted verbatim in `steinberg-group-homology-gives-k2-and-k3-citation`). Everything else is
proved here. The identities of Steps 1–4 are also checked exactly on random data by
`experiments/z2-crossed-product-steinberg-kernel-2026-09-16/verify_cocycle.py`.

## 0. Statement

Let `A` be a nonzero commutative unital ring and `alpha: Z^2 -> Aut(A)` an action, written
`t -> alpha_t`. Let `R = A ⋊ Z^2`: the free left `A`-module on symbols `u_g` (`g ∈ Z^2`), with
`(a u_g)(b u_h) = a alpha_g(b) u_(g+h)`. Put `u_1 = u_(e_1)` and `u_2 = u_(e_2)`. They are
commuting units.

For `n >= 3` let `pi: St_n(R) -> E_n(R) ⊆ GL_n(R)` be the canonical map `x_ij(r) -> e_ij(r)`, and
`K_2(n,R) = ker pi`. Put `w_ij(u) = x_ij(u) x_ji(-u^(-1)) x_ij(u)` and
`h_ij(u) = w_ij(u) w_ij(-1)` for a unit `u`, and

    c_n = [h_12(u_1), h_13(u_2)] = h_12(u_1) h_13(u_2) h_12(u_1)^(-1) h_13(u_2)^(-1)  ∈ St_n(R).

**Theorem.**
1. For every `n >= 5` there is a map `sigma: St_n(R) -> A` whose restriction to `K_2(n,R)` is a
   group homomorphism and is invariant under conjugation by `St_n(R)`, with `sigma(c_n) = -1`.
   More generally `sigma([x,y]) = -1` for all `x, y ∈ St_n(R)` with `pi(x) = D_1` and `pi(y) = D_2`,
   where `D_1 = diag(u_1, u_1^(-1), 1, ..., 1)` and `D_2 = diag(u_2, 1, u_2^(-1), 1, ..., 1)`.
2. For every `n >= 3`, `c_n ∈ K_2(n,R)`, and the order of `c_n` is infinite or a multiple of the
   additive order of `1 ∈ A`. In particular `c_n ≠ 1`, `K_2(n,R) ≠ 0`, and
   `St_n(R) -> E_n(R)` is not injective.
3. The image of `c_3` in the stable Steinberg group `St(R)` lies in `K_2(R)` and is nontrivial,
   with the same order statement.

For `R = LC(Ω, F_q) ⋊ Z^2`, with `Ω` any Cantor `Z^2`-system (free, minimal, SFT or not),
`K_2(n,R)` is nonzero for every `n >= 3`, and `c_n` has order divisible by `p = char F_q`, or
infinite.

No freeness, minimality or finite presentation is used. Commutativity of `A` is used once, in
Step 2.

## 1. Conventions

- **Group chains.** For a group `G`, `C_k(G) = Z[G^k]` with basis `[g_1|...|g_k]` and
  `d[g_1|...|g_k] = [g_2|...|g_k] + sum_(i=1)^(k-1) (-1)^i [...|g_i g_(i+1)|...] + (-1)^k [g_1|...|g_(k-1)]`.
  A function `f: G^2 -> M` into an abelian group, extended linearly, satisfies `f∘d = 0` on
  `C_3(G)` iff `f(h,k) - f(gh,k) + f(g,hk) - f(g,h) = 0` for all `g,h,k`. That is the usual
  2-cocycle condition with trivial coefficients.
- **Hochschild chains.** For a ring `S`, `C_k(S) = S^(⊗(k+1))` over `Z`, with
  `b(s_0⊗...⊗s_k) = sum_(i=0)^(k-1) (-1)^i s_0⊗...⊗s_i s_(i+1)⊗...⊗s_k + (-1)^k s_k s_0⊗s_1⊗...⊗s_(k-1)`.
- **Group ring.** `Z[Z^2] = Z[t_1^(±1), t_2^(±1)]`, with `t^g = t_1^(g_1) t_2^(g_2)`. It acts on `A`
  by `t^g -> alpha_g`, a ring homomorphism `Z[Z^2] -> End_Z(A)`. Write `Ñ(m)` for the action of `N`
  on `m ∈ A`. Since `Z^2` is abelian, `Ñ(alpha_k(m)) = (t^k N)~(m)`. Write `eps: Z[Z^2] -> Z` for
  the augmentation.

## 2. Step 1: from group chains to Hochschild chains of `R`

**(1a) Units.** Let `S` be a ring and `G ⊆ S^x` a subgroup. Define
`Phi[g_1|...|g_k] = (g_1...g_k)^(-1) ⊗ g_1 ⊗ ... ⊗ g_k`. Then `b∘Phi = Phi∘d`.

*Proof.* Put `a_0 = (g_1...g_k)^(-1)`.
- The face `i = 0` gives `a_0 g_1 = (g_2...g_k)^(-1)`, so it is `Phi[g_2|...|g_k]`.
- The faces `1 <= i <= k-1` merge `g_i g_(i+1)` and keep `a_0`, so they give
  `(-1)^i Phi[...|g_i g_(i+1)|...]`.
- The last face gives `g_k a_0 = g_k g_k^(-1) (g_1...g_(k-1))^(-1) = (g_1...g_(k-1))^(-1)`, so it is
  `(-1)^k Phi[g_1|...|g_(k-1)]`. ∎

**(1b) Trace.** Define `T: C_k(M_n(R)) -> C_k(R)` by
`T(m_0⊗...⊗m_k) = sum_(i_0,...,i_k) m_0(i_0,i_1) ⊗ m_1(i_1,i_2) ⊗ ... ⊗ m_k(i_k,i_0)`. This is
multi-additive, and `b∘T = T∘b`.

*Proof.*
- For `i < k`, summing over the repeated index `i_(i+1)` turns
  `m_i(i_i,i_(i+1)) m_(i+1)(i_(i+1),i_(i+2))` into `(m_i m_(i+1))(i_i,i_(i+2))`.
- For the last face, summing over `i_0` turns `m_k(i_k,i_0) m_0(i_0,i_1)` into `(m_k m_0)(i_k,i_1)`.
  The resulting sum is `T((m_k m_0)⊗m_1⊗...⊗m_(k-1))` after renaming `i_k` as the first index. ∎

So `T∘Phi: C_*(GL_n(R)) -> C_*(R)` is a chain map.

## 3. Step 2: the degree-zero part of `C_*(R)` maps to group chains with coefficients in `A`

As an abelian group, `R^(⊗(k+1))` is the direct sum over `(g_0,...,g_k) ∈ (Z^2)^(k+1)` of
`A u_(g_0) ⊗ ... ⊗ A u_(g_k)`, because tensor products commute with direct sums. Call
`g_0 + ... + g_k` the degree of a summand. Every face of `b` multiplies two cyclically adjacent
factors, so `b` preserves degree.

Let `B_k = A ⊗ Z[(Z^2)^k]`, the finitely supported functions `(Z^2)^k -> A`. Write its elements as
sums of `m[g_1|...|g_k]` with `m ∈ A`, and define

    ∂(m[g_1|...|g_k]) = m[g_2|...|g_k] + sum_(i=1)^(k-1) (-1)^i m[...|g_i + g_(i+1)|...]
                        + (-1)^k alpha_(g_k)(m)[g_1|...|g_(k-1)].

Define `psi: C_k(R) -> B_k` on the summand `(g_0,...,g_k)` as follows. It is `0` if the degree is
nonzero. If the degree is `0`, it sends `x_0⊗...⊗x_k` with `x_i ∈ A u_(g_i)` to
`(x_0 x_1 ... x_k)[g_1|...|g_k]`. Here the product lies in `A u_0 = A`, and it is multi-additive.

**(2a)** `psi∘b = ∂∘psi`.

*Proof.* On a summand of nonzero degree both sides vanish, since `b` preserves degree. Take degree
`0` and `m = x_0...x_k`.
- The face `i = 0` has factors `x_0 x_1, x_2, ..., x_k`. The product is still `m`, and the degrees
  of the last `k-1` factors are `g_2, ..., g_k`. So it gives `m[g_2|...|g_k]`.
- The faces `1 <= i <= k-1` give `(-1)^i m[...|g_i + g_(i+1)|...]`.
- The last face has factors `x_k x_0, x_1, ..., x_(k-1)`, with product `x_k x_0 ... x_(k-1)`.
  - Write `x_0 ... x_(k-1) = y u_(-g_k)` with `y ∈ A`, and `x_k = a u_(g_k)`.
  - Then `m = y u_(-g_k) a u_(g_k) = y alpha_(-g_k)(a)`.
  - Also `x_k x_0...x_(k-1) = a u_(g_k) y u_(-g_k) = a alpha_(g_k)(y) = alpha_(g_k)(alpha_(-g_k)(a) y)`.
  - Because `A` is commutative, this is `alpha_(g_k)(m)`.
  - So the last face gives `(-1)^k alpha_(g_k)(m)[g_1|...|g_(k-1)]`. ∎

We never need `∂∘∂ = 0`, although it follows from `(2a)` because `psi` is onto: take `x_0 = m u_(g_0)`
and `x_i = u_(g_i)`. We only need that a map `taubar: B_2 -> A` with `taubar∘∂ = 0` on `B_3` gives
`tau = taubar∘psi` with `tau∘b = taubar∘∂∘psi = 0` on `C_3(R)`.

## 4. Step 3: a `Z[Z^2]`-valued cocycle and the functional `tau`

**(3a) Quantum integers.** In `Z[t^(±1)]` put `P(a) = 1 + t + ... + t^(a-1)` for `a >= 0` (so
`P(0) = 0`), and `P(a) = -(t^a + ... + t^(-1))` for `a < 0`. Then `(t-1)P(a) = t^a - 1` for all
`a ∈ Z`. Hence `P(a+b) = P(a) + t^a P(b)`, because both sides times `t-1` equal `t^(a+b) - 1` and
`Z[t^(±1)]` is a domain. Also `eps(P(a)) = a`. Write `P_1` and `P_2` for `P` in `t_1` and `t_2`.

**(3b) A 2-cocycle.** For `a, b ∈ Z^2` put `c(a,b) = P_1(a_1) t_2^(a_2) P_2(b_2) ∈ Z[Z^2]`. Then

    (δc)(a,b,d) := t^a c(b,d) - c(a+b,d) + c(a,b+d) - c(a,b) = 0.

*Proof.* Expand with `(3a)`:
- `t^a c(b,d) = t_1^(a_1) P_1(b_1) · t_2^(a_2+b_2) P_2(d_2)`;
- `c(a+b,d) = [P_1(a_1) + t_1^(a_1) P_1(b_1)] · t_2^(a_2+b_2) P_2(d_2)`;
- `c(a,b+d) = P_1(a_1) t_2^(a_2) [P_2(b_2) + t_2^(b_2) P_2(d_2)]`;
- `c(a,b) = P_1(a_1) t_2^(a_2) P_2(b_2)`.

The alternating sum cancels term by term. This is the cup product of the 1-cocycles
`a -> P_1(a_1)` and `a -> P_2(a_2)`. ∎

**(3c)** Put `N(g,h) = c(h,g) = P_1(h_1) t_2^(h_2) P_2(g_2)`. Then for all `g,h,k ∈ Z^2`,

    N(h,k) - N(g+h,k) + N(g,h+k) - t^k N(g,h) = -(δc)(k,h,g) = 0,

and `eps(N(g,h)) = h_1 g_2`.

**(3d) The functional.** Define `taubar: B_2 -> A` by `taubar(m[g|h]) = Ñ(g,h)(m)`, and
`tau = taubar∘psi: C_2(R) -> A`. Explicitly, on `x_i = a_i u_(g_i)`,

    tau(x_0⊗x_1⊗x_2) = [g_0+g_1+g_2 = 0] · Ñ(g_1,g_2)( a_0 alpha_(g_0)(a_1) alpha_(g_0+g_1)(a_2) ).

Then `tau∘b = 0` on `C_3(R)`.

*Proof.* By `(2a)` it suffices that `taubar∘∂ = 0` on `B_3`. Since
`∂(m[g|h|k]) = m[h|k] - m[g+h|k] + m[g|h+k] - alpha_k(m)[g|h]`,

    taubar(∂(m[g|h|k])) = ( N(h,k) - N(g+h,k) + N(g,h+k) - t^k N(g,h) )~(m) = 0

by `(3c)` and `Ñ(alpha_k(m)) = (t^k N)~(m)`. ∎

*Remark.* The naive choice `taubar(m[g|h]) = g_1 h_2 λ(m)` needs `λ∘alpha_t = λ` with `λ(1) ≠ 0`.
Such a `λ` can fail to exist over `F_p`, for instance when `[1]` is divisible by `p` in the
coinvariants. The factor `N(g,h) ∈ Z[Z^2]` removes any invariance requirement: `tau` takes values in
`A` itself. The negative control `negative_control.py` confirms that the naive choice with the
non-invariant `λ = id_A` violates `tau∘b = 0` for a translation action.

## 5. Step 4: the group cocycle `f` and its value on the torus pair

**(4a)** Define `f: GL_n(R) × GL_n(R) -> A` by `f(g,h) = tau(T((gh)^(-1) ⊗ g ⊗ h)) = tau(T(Phi[g|h]))`.
Then `f` is a normalized 2-cocycle with trivial coefficients.

*Proof.*
- **Cocycle.** Extend `f` linearly to `C_2(GL_n(R))`. By Step 1, `f∘d = tau∘T∘Phi∘d = tau∘b∘T∘Phi`,
  which is `0` on `C_3` by `(3d)`.
- **Normalization.**
  - The cocycle identity at `(1,1,k)` gives `f(1,k) = f(1,1)`, and at `(g,1,1)` gives
    `f(g,1) = f(1,1)`.
  - `f(1,1) = tau(T(1⊗1⊗1)) = n · tau(u_0⊗u_0⊗u_0) = n · Ñ(0,0)(1) = 0`, because `P_2(0) = 0`.
  - So `f(1,·) = f(·,1) = 0`. ∎

**(4b) Values on monomials.** If `g_0+g_1+g_2 = 0`, then
`tau(u_(g_0)⊗u_(g_1)⊗u_(g_2)) = Ñ(g_1,g_2)(1) = eps(N(g_1,g_2)) · 1 = (g_2)_1 (g_1)_2 · 1`, since
`alpha_t(1) = 1`.

**(4c) The torus pair.** `f(D_1,D_2) - f(D_2,D_1) = -1`.

*Proof.* For diagonal `m_0, m_1, m_2` only `i_0 = i_1 = i_2` survives in `T`. We have
`D_1 D_2 = D_2 D_1 = diag(u_(e_1+e_2), u_(-e_1), u_(-e_2), 1, ...)`, so its inverse is
`diag(u_(-e_1-e_2), u_(e_1), u_(e_2), 1, ...)`.

- **`f(D_1,D_2)`** is the sum of
  `tau(u_(-e_1-e_2)⊗u_(e_1)⊗u_(e_2)) + tau(u_(e_1)⊗u_(-e_1)⊗u_0) + tau(u_(e_2)⊗u_0⊗u_(-e_2))`
  and `(n-3) tau(u_0⊗u_0⊗u_0)`. By `(4b)` the terms are:
  - `(e_2)_1 (e_1)_2 = 0`,
  - `0 · (-e_1)_2 = 0`,
  - `(-e_2)_1 · 0 = 0`,
  - `0`.

  So `f(D_1,D_2) = 0`.
- **`f(D_2,D_1)`** is the sum of
  `tau(u_(-e_1-e_2)⊗u_(e_2)⊗u_(e_1)) + tau(u_(e_1)⊗u_0⊗u_(-e_1)) + tau(u_(e_2)⊗u_(-e_2)⊗u_0)`
  and `(n-3) · 0`. The terms are:
  - `(e_1)_1 (e_2)_2 = 1`,
  - `(-e_1)_1 · 0 = 0`,
  - `0 · (-e_2)_2 = 0`.

  So `f(D_2,D_1) = 1`. ∎

## 6. Step 5: splitting over `St_n(R)` and the conclusion

**(5a) The extension.** Let `Ŝ` be the set `A × St_n(R)` with
`(a,x)(b,y) = (a + b + f(pi x, pi y), xy)`.
- It is a group: associativity is the cocycle identity, the identity element is `(0,1)` by
  normalization, and `(a,x)^(-1) = (-a - f(pi x, pi x^(-1)), x^(-1))`.
- `(a,x) -> x` is a surjective homomorphism with kernel `A × {1}`.
- The kernel is central: `(m,1)(b,y) = (m+b+f(1,pi y), y) = (m+b, y) = (b,y)(m,1)`.

So `Ŝ -> St_n(R)` is a central extension.

**(5b) Splitting.** Let `n >= 5`. By `steinberg-group-homology-gives-k2-and-k3` (ii) the extension
splits. So there is a homomorphism `s: St_n(R) -> Ŝ` of the form `s(x) = (sigma(x), x)`, and being a
homomorphism means exactly

    sigma(xy) = sigma(x) + sigma(y) + f(pi x, pi y)   for all x, y ∈ St_n(R).       (*)

**Consequences of `(*)`.**
- `sigma(1) = 0`, since `s(1) = (0,1)`.
- **Additive on the kernel.** For `k, k' ∈ K_2(n,R)`,
  `sigma(k k') = sigma(k) + sigma(k') + f(1,1) = sigma(k) + sigma(k')`.
- **Conjugation invariant.** For `k ∈ K_2(n,R)` and `y ∈ St_n(R)`, `(*)` gives
  `sigma(y k y^(-1)) = sigma(y) + sigma(k y^(-1)) + f(pi y, pi y^(-1))`, and
  `sigma(k y^(-1)) = sigma(k) + sigma(y^(-1))` since `pi k = 1`. Also
  `0 = sigma(y y^(-1)) = sigma(y) + sigma(y^(-1)) + f(pi y, pi y^(-1))`. Hence
  `sigma(y k y^(-1)) = sigma(k)`.
- **Uniqueness.** The splitting `s` is unique: two splittings differ by a homomorphism
  `St_n(R) -> A`, which is trivial because `St_n(R)` is perfect for `n >= 3`.

**(5c) The commutator.** Let `x, y ∈ St_n(R)` with `pi x = D_1` and `pi y = D_2`, and put
`c = xyx^(-1)y^(-1)`.
- `pi c = [D_1, D_2] = 1`, so `c ∈ K_2(n,R)`, and `xy = c·yx`.
- By `(*)`, `sigma(xy) = sigma(x) + sigma(y) + f(D_1,D_2)`.
- Also `sigma(c·yx) = sigma(c) + sigma(yx) + f(1, D_2 D_1) = sigma(c) + sigma(x) + sigma(y) + f(D_2,D_1)`.
- Comparing, `sigma(c) = f(D_1,D_2) - f(D_2,D_1) = -1` by `(4c)`.

**Checking the images of `h_ij`.** In the `(i,j)` block,
`pi(w_ij(u)) = [[1,u],[0,1]]·[[1,0],[-u^(-1),1]]·[[1,u],[0,1]] = [[0,u],[-u^(-1),0]]`. Hence
`pi(h_ij(u)) = [[0,u],[-u^(-1),0]]·[[0,-1],[1,0]] = diag(u, u^(-1))` in that block. So
`pi(h_12(u_1)) = D_1` and `pi(h_13(u_2)) = D_2`, and `sigma(c_n) = -1`. This proves part 1.

**(5d) Order.** If `c_n^k = 1` with `n >= 5`, then `0 = sigma(c_n^k) = k·sigma(c_n) = -k·1_A`. So `k`
is a multiple of the additive order of `1_A`.

**(5e) Small rank and stable rank.**
- For `3 <= n < m`, the map `x_ij(r) -> x_ij(r)` is a homomorphism `St_n(R) -> St_m(R)`: the
  Steinberg relations of `St_n` are among those of `St_m`. It sends `h_ij(u)` to `h_ij(u)` and
  `c_n` to `c_m`.
- With `m = max(n,5)`, `c_n^k = 1` forces `c_m^k = 1`, so `k` is a multiple of the order of `1_A`.
  This proves part 2.
- `St(R)` is the colimit of the `St_m(R)`. An element of `St_m(R)` that dies in `St(R)` dies in some
  `St_(m')(R)`, so the same conclusion holds for the image of `c_n` in `K_2(R) ⊆ St(R)`. This proves
  part 3.

For `A = LC(Ω, F_q)`, `1_A` has additive order `p`. ∎

## 7. Consequences for gate (b), and what this invariant cannot do

**What gate (b) is.** Let `R = LC(Ω, F_q) ⋊ Z^2` be finitely presented and `n >= 4`.
- `projective-elementary-fp-kernel-criterion` says `EL_n(R)/Z` is finitely presented iff
  `K_2(n,R)` is finitely normally generated in `St_n(R)` and `Z(EL_n(R))` is finitely generated.
- The centre is finite (`free-minimal-subshift-elementary-groups-are-simple-kazhdan`).
- So gate (b) is exactly finite normal generation of `K_2(n,R)` for some `n >= 4`.

**What this artifact adds.**
- **Vanishing is false in every rank.** `K_2(n,R) ≠ 0` for all `n >= 3`. So gate (b) cannot be closed
  by showing `St_n(R) = E_n(R)`, the way polynomial rings over `F_q` are handled (there `K_2` vanishes
  by homotopy invariance). A proof must produce finitely many normal generators of a nonzero kernel.
- **The obvious generator.** `c_n` is a natural first generator. The heuristic
  `K_2(R) ≈ Z{u_1,u_2} ⊕ (extension and Nil terms)` from the lane notes predicts it is the main one
  over `F_2`.
- **Contrast with `d = 1`.** For `LC(X, F_2) ⋊ Z` the stable `K_2` vanishes
  (`binary-cantor-ring-stable-steinberg-group-centrally-closed`, unreviewed). The argument above
  needs two commuting translations, since `H_2(Z; ·)` has no torus class, so there is no conflict.
- **Sanity check.** Take `A = F_q` with the trivial action, so `R = F_q[u_1^(±1), u_2^(±1)]`. The
  theorem then detects the reduction mod `p` of the symbol `{u_1,u_2}`, which is nonzero in
  `K_2(F_q[x^(±1), y^(±1)]) ≅ Z ⊕ C_(q-1)^2` (`rank-five-laurent-k2-stability-is-dimension-free`).

**What `sigma` cannot do.** `sigma` is additive and conjugation invariant on `K_2(n,R)` (`(5b)`).
- If `K_2(n,R)` is normally generated by `k_1, ..., k_r`, then `sigma(K_2(n,R))` is the subgroup of
  `A` generated by the `sigma(k_i)`, which is finite because `A` has exponent `p`.
- So `sigma` would obstruct gate (b) only if `sigma(K_2(n,R))` were infinite.
- Heuristically (not proved here) `sigma` factors through `HH_2(R) -> H_2(Z^2; A) ≅ A^(Z^2)`, which
  is `F_q` for a minimal action. Then its image is finite, and `sigma` gives no obstruction. The same
  heuristic applies to every functional built the same way.

## 8. Machine check and weakest points

**Script.** `experiments/z2-crossed-product-steinberg-kernel-2026-09-16/verify_cocycle.py` uses
exact arithmetic over `F_5`, with `A = F_5^((Z/3)^2)` and `Z^2` acting by translation. It checks:
- `(3c)` for 2000 random triples in `[-3,3]^2`;
- `tau∘b = 0` on 3000 random homogeneous 3-chains of degree `0`;
- the 2-cocycle identity for `f` on 25 random triples of products of elementary and monomial
  diagonal matrices in `GL_3(R)`;
- `f(D_1,D_2) - f(D_2,D_1) = -1`.

All pass (`output.txt`). `negative_control.py` shows that check (2) is not vacuous.

**Weakest points.**
1. **The import.** Part 1 relies on Weibel III Proposition 5.5.1 (every central extension of
   `St_n(S)` splits for `n >= 5`, for every associative unital ring `S`). It is quoted verbatim in the
   graph. Part 2 in ranks 3 and 4 is reduced to rank 5, so it uses the same import.
2. **Conventions.** Signs and conventions in Steps 2–4 are the main risk of a slip. Each identity is
   proved by hand above and checked exactly on random data, but a check on a finite periodic model
   is not a proof.
3. **Commutativity.** Commutativity of `A` is used in `(2a)`, and nowhere else.
