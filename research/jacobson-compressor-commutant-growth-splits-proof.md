---
rg: 2
id: jacobson-compressor-commutant-growth-splits-proof
kind: route
title: Noetherian symbol commutants are compressor-stable, so the lifting long exact sequence splits commutant growth into finite-rank invariants and restriction-killed H^1 classes
target: jacobson-compressor-commutant-growth-splits
requires:
  - jacobson-compressors-commensurate-every-moved-module
---

Notation as in the target. `F` is any field. `V = F[x]^N`, `S` acts by multiplication by `x`, and
`T f = P_+(x^-1 f)`.

## Step 0. Finite-rank elements of `M_N(J)` are exactly `M_N(I)`

- By Step 0 of `jacobson-compressors-commensurate-every-moved-module-proof`, every `a in M_N(J)` satisfies
  `a = T_(rho(a)) + (finite rank)`.
- `I` is spanned by the matrix units `S^i Q T^j`, and these have rank one. So `M_N(I)` consists of finite-rank
  operators.
- Conversely, suppose `a` has finite rank. Then `T_(rho(a))` has finite rank. A Toeplitz operator with a nonzero
  Laurent-matrix symbol has infinite rank, because on `x^k e_i` with `k` large it multiplies by the symbol without
  truncation. So `rho(a) = 0` and `a in M_N(I)`.
- Since `rho` is a ring homomorphism with kernel `M_N(I)`, for `X, Y in M_N(J)` we get: `[X, Y] in M_N(I)` if and only
  if `rho(X)` and `rho(Y)` commute.

## Step 1. Symbol rigidity (Theorem part 1)

Put `h = rho(g)` and `C = C_R(Gamma)`.
- `Gamma' <= Gamma` gives `C <= C_R(Gamma')`.
- `C_R(Gamma') = C_R(h rho(Gamma) h^-1) = h C h^-1`. So `C <= h C h^-1`.
- Conjugation by `h` is an `R`-linear bijection of `M_N(R)`, because `R` is commutative. So
  `C <= h C h^-1 <= h^2 C h^-2 <= ...` is an ascending chain of `R`-submodules of `M_N(R)`.
- `M_N(R)` is a finitely generated module over the noetherian ring `R`, so the chain stabilizes:
  `h^k C h^-k = h^(k+1) C h^-(k+1)` for some `k`.
- Conjugating by `h^-k` gives `C = h C h^-1 = C_R(Gamma')`.

No finite generation of `Gamma` and no hypothesis on `F` is used. This is the instance of
`noetherian-invariant-compression-rigidity` for the antitone invariant `Delta |-> C_R(Delta)`.

## Step 2. The lifting sequence (Theorem part 2)

- Put `A~ = rho^-1(C) <= M_N(J)`. By Step 1, the same `A~` serves for `Gamma` and for `Gamma'`.
- For `delta` in `Gamma` and `X` in `A~`, `rho(delta X delta^-1) = rho(X)`. So `Gamma` acts on `A~` by
  conjugation, and that action is trivial on the quotient `A~ / M_N(I) = C`.
- This gives a short exact sequence of `Delta`-modules for `Delta` in `{Gamma, Gamma'}`:
  `0 -> M_N(I) -> A~ -> C -> 0`.
- Its long exact cohomology sequence begins
  `0 -> M_N(I)^Delta -> (A~)^Delta -> C -> H^1(Delta, M_N(I))`.
- `(A~)^Delta = A(Delta)`. An element commuting with `Delta` has symbol commuting with `rho(Delta)`, so it lies in
  `rho^-1(C_R(Delta)) = A~`.
- The connecting map sends `xi` to the class of `gamma |-> gamma X gamma^-1 - X`, where `rho(X) = xi`. That is
  `delta_Delta`.
- Both sequences come from the same short exact sequence, restricted from `Gamma` to `Gamma'`. By naturality,
  `delta_(Gamma') = res o delta_Gamma`.

## Step 3. Splitting (Theorem part 3)

- `A(Gamma) <= A(Gamma')`, because `Gamma' <= Gamma`.
- `A(Gamma') = A(g Gamma g^-1) = g A(Gamma) g^-1`.
- By Step 2, `rho(A(Gamma)) = ker delta_Gamma` and `rho(A(Gamma')) = ker(res o delta_Gamma)`.
- Consider the surjection `A(Gamma') -> ker(res o delta_Gamma) / ker(delta_Gamma)`. Take `X` in its kernel. Then
  `rho(X) = rho(Y)` for some `Y` in `A(Gamma)`, so `X - Y` lies in `A(Gamma') cap M_N(I) = M_N(I)^(Gamma')`.
- So the kernel is `(A(Gamma) + M_N(I)^(Gamma')) / A(Gamma)`. This is isomorphic to
  `M_N(I)^(Gamma') / (M_N(I)^(Gamma') cap A(Gamma)) = M_N(I)^(Gamma') / M_N(I)^Gamma`.
- Finally, `delta_Gamma` induces `ker(res o delta)/ker(delta) ~= delta(ker(res o delta)) = im(delta) cap ker(res)`.

## Step 4. Corollary 1 (finite growth is killed by (T))

For a subspace `A` of `M_N(J)` and `h` in `GL_N(J)`, write `hA = h A h^-1`. Say `A` and `B` are *commensurable* when
each has finite codimension in `A + B`.

- The commensurator `Comm(A) = {h : hA ~ A}` is a group.
- The relative index `ind(h) = dim A/(A cap hA) - dim hA/(A cap hA)` is a homomorphism `Comm(A) -> Z`. This is the
  standard additivity of relative dimension: `ind(h_1 h_2) = [A : h_1 A] + [h_1 A : h_1 h_2 A]`, and conjugation by
  `h_1` carries the pair `(A, h_2 A)` to `(h_1 A, h_1 h_2 A)`.
- Take `A = A(Gamma)`. Each compressor `g` has `A <= gA`, with codimension `d(g)` finite by hypothesis. So
  `g in Comm(A)` and `ind(g) = -d(g)`.
- Hence `D_G <= Comm(A)`, and `ind` restricts to a homomorphism `D_G -> Z`. It vanishes by hypothesis. (A Kazhdan
  group has finite abelianization, and `D_G = G` when `Gamma` is infranormal in `G`.)
- So `d(g) = 0` for every compressor, and `g A g^-1 = A`. Therefore every element of `D_G = G` normalizes `A(Gamma)`.
- For `h in G` and `z in C_H(Gamma) <= A(Gamma)^x`, we get `h z h^-1 in A(Gamma)`. So `h z h^-1` commutes with every
  `gamma in Gamma`, which is triviality of the rigid defect.
- Contrapositive: a nontrivial defect needs some compressor with `d(g) = infinity`. By Step 3, `d(g)` is the sum of
  the type (a) and type (b) dimensions, so one of them is infinite.

## Step 5. Corollary 2 (scalar centralizers)

- **The algebra.** Let `N >= 2` and `p in {S, T}`. The `F`-span of `E_N(F[p])` contains
  `a E_ij = e_ij(a) - 1` for `i != j` and `a in F[p]`, and it contains `a E_ii = (a E_ij)(E_ji)`. So it is the
  whole algebra `M_N(F[p])`.
- **Reduction to the scalar case.** An element of `M_N(J)` that commutes with every constant matrix unit is `y 1_N`
  with `y in J`. It commutes with `p 1_N` exactly when `y in C_J(p)`.
- **`C_J(S) = F[S]`.** Take `y` commuting with `S`. On `F[x]`, `S` is multiplication by `x`, so `y` is
  `F[x]`-linear. Hence `y` is multiplication by `f = y(1)`, which is also the action of `f(S)`. Since `J` acts
  faithfully, `y = f(S)`.
- **`C_J(T) = F[T]`.**
  - Take `y` commuting with `T`, and put `a_m` = the coefficient of `x^0` in `y(x^m)`.
  - The coefficient of `x^j` in `y(x^n)` is the `x^0`-coefficient of `T^j y(x^n) = y(T^j x^n)`. That is `a_(n-j)`
    for `j <= n`, and `0` for `j > n`.
  - So `y(x^n) = sum_(k=0)^n a_k x^(n-k)`, the action of the formal series `sum_k a_k T^k`.
  - By Step 0, for `n` large, `y(x^n) = rho(y) x^n` with `rho(y)` a Laurent polynomial. So only finitely many `a_k`
    are nonzero, and `y = sum a_k T^k in F[T]`.
- **Units.** If `f(p)` is a unit of `J`, its inverse also commutes with `p`, so it equals `h(p)` for some `h`.
  `F[p]` is a polynomial ring: `S` is injective and not algebraic, and `T^k != 0` for every `k`. So
  `f(p) h(p) = 1` forces `f` to be constant.
- **Conclusion.** The commutant of `x E_N(F[p]) x^-1` in `M_N(J)` is `x F[p] x^-1`, and its unit group is `F^x`.
  Hence `F^x <= C_(GL_N(J))(Gamma) <= F^x`.
- **Defect.** Each `z` in the centralizer is central in `GL_N(J)`. So `g z g^-1 = z` commutes with `Gamma` for
  every `g`.
- **Finite-dimensional stable spaces.** `e_ij(a T^k)` adds `a T^k` of one coordinate to another. `T` lowers degree
  by one, so this preserves each `V_(<= d)`.

## Step 6. The corner calibration

Take `n = m >= 3`, `Gamma = E_m(J) + 1` on `V_1 + V_2`, and `u = [[S, Q], [0, T]]` with block scalars.

- **The conjugate.** `QS = TQ = 0` and `Q^2 = Q` give `u (A + 1) u^-1 = phi(A) + 1`, where
  `phi(A) = S A T + Q`.
- **The commutant of `Gamma`.**
  - `E_m(J)` contains `SL_fin(V_1)`, which acts irreducibly with commutant `F`.
  - An off-diagonal intertwiner has image in `Fix(E_m(J)) = 0`, or kills `Mov = V_1`.
  - So `A(Gamma) = F + M_m(J)`, `rho(A(Gamma)) = F + M_m(R)`, and `M_N(I)^Gamma = 0 + M_m(I)`.
- **Type (b) vanishes.** `rho(u) = diag(x, x^-1)` is block scalar, so
  `rho(A(Gamma')) = rho(u) rho(A(Gamma)) rho(u)^-1 = F + M_m(R)`. Hence `ker(res o delta) = ker(delta)` and
  `B(u) = 0`.
  - `C_R(Gamma) = R 1_m + M_m(R)` is strictly larger. The classes `delta(r 1_m)` with `r notin F` are nonzero in
    `H^1(Gamma, M_N(I))` and stay nonzero on `Gamma'`.
- **Type (a) is infinite.** `Gamma'` has `Mov = S V_1` and `Fix = Q V_1 + V_2`. Every finite-rank map `V -> Fix` that
  kills `S V_1` commutes with `Gamma'`. In particular every finitely supported map `V_2 -> Q V_1`, and every one
  `Q V_1 -> V_2`, lies in `M_N(I)^(Gamma')` but not in `M_N(I)^Gamma`. These form an infinite-dimensional family.

So all the growth of `u` is finitary, and it is produced by the growth `Fix(Gamma) < Fix(Gamma')` that FI measures.
The naive lemma, "finite codimension of `A(Gamma)` in `A(g Gamma g^-1)` for every compressor", is therefore false.
Corollary 1 applies only where both growth types are finite-dimensional.
