---
rg: 2
id: abelianized-cover-isolated-fixed-spectral-point-proof
kind: route
title: Cut the kernel algebra at a clopen fixed point, untwist by a character of the free group, and let the full radical kill the corner
target: abelianized-cover-isolated-fixed-spectral-point-is-scalar
requires:
  - universal-mf-quotient
---

Notation is that of the target claim.  `Rad_MF(Gamma)` is the intersection
of the kernels of all models `Gamma -> U(Q)` over all norm matrix coronas
`Q`.  So `Rad_MF(G) = G` means every model of `G` is trivial.

## Step 0: corners of a corona are coronas

Let `p != 0` be a projection in `Q = prod_k M_(d_k) / (+)_k M_(d_k)`.
- Take a self-adjoint lift `(a_k)` of `p`.  Then
  `||a_k^2 - a_k|| -> 0`, so for large `k` the spectrum of `a_k` avoids
  `1/2`.  Let `p_k = 1_[1/2, infinity)(a_k)`, a projection with
  `||p_k - a_k|| -> 0`, so `(p_k)` also lifts `p`.
- Put `r_k = rank p_k` and `J = {k : r_k >= 1}`.  Since
  `||p|| = limsup ||p_k|| = 1`, the set `J` is infinite.
- Then `pQp = prod_(k in J) p_k M_(d_k) p_k / (+)` is isomorphic to
  `prod_(k in J) M_(r_k) / (+)_(k in J) M_(r_k)`.  The factors with
  `k notin J` are zero.

So `pQp` is a norm matrix corona, and every unital homomorphism
`G -> U(pQp)` is trivial when `Rad_MF(G) = G`.

## Step 1: the kernel algebra and the action

- `M` is abelian, so `A = C*(W(M))` is a unital commutative C*-algebra.
  By Gelfand duality, `A = C(X)`, where `X` is the joint spectrum: the set
  of characters `chi` of `M` such that `m -> chi(m)` extends to a
  character of `A`.  So `X` is a closed subset of `hat M`.
- For `e in E` with image `g in G`, `Ad W(e)` maps `W(m)` to
  `W(e m e^-1) = W(g.m)`.  So `Ad W(e)` restricts to an automorphism of
  `A`, which is `f -> f o (g^-1 .)` for the dual action on `X`.  This
  depends only on `g`, because `M` is abelian.

## Step 2: the cut

Let `chi in X` be isolated and fixed.
- `{chi}` is clopen, so its indicator `p` is continuous and lies in `A`.
  It is nonzero, since `chi in X`.
- By Step 1, `W(e) p W(e)^* = 1_{g.chi} = 1_{chi} = p`.  So `p` commutes
  with `W(E)`.
- Since `W(m) = hat m` in `C(X)`, we have `W(m) p = chi(m) p`.
- Hence `V(e) = W(e) p` is a unital homomorphism `E -> U(pQp)` with
  `V(m) = chi(m) p` for `m in M`.

## Step 3: untwisting by a character of the free group

Assume `chi` is liftable: `chi = psi o eps` on `M`, for some character
`psi` of the subgroup `eps(M_G) <= Z^n`.  (A fixed character of `M` kills
`[F,R]/[R,R]`, so it is a character of `M_G`.)
- `T` is divisible, so `psi` extends to a character of `Z^n`, still
  written `psi`.
- Let `lambda = psi o ab : F -> T`.  It kills `[F,F]`, which contains
  `[R,R]`, so it descends to a character of `E` that factors through
  `E^ab = F^ab = Z^n`.
- For `r in R` with class `m in M`, `lambda(r) = psi(eps(m)) = chi(m)`.

Define `U(e) = conj(lambda(e)) V(e)`.  Then:
- `U` is a unital homomorphism `E -> U(pQp)`, since `lambda` is a scalar
  character;
- `U(m) = conj(chi(m)) chi(m) p = p` for `m in M`.

So `U` factors through `E/M = G`.  By Step 0 it is trivial, which gives
`W(e) p = V(e) = lambda(e) p` for every `e`.  This is item 1 of the
claim.  Since `lambda` factors through `E^ab`, `W(w) p = p` for
`w in E'`.

## Step 4: stripping (item 2)

- The indicators `p_chi` of distinct isolated points are orthogonal
  projections in `A`, each commuting with `W(E)` by Step 2.  So `p_Y` is a
  projection commuting with `W(E)`.
- `W = W(1 - p_Y) + sum_(chi in Y) W p_chi`, and each summand is a
  homomorphism into a corner.
- The kernel spectrum of `W_0 = W(1 - p_Y)` is the support of `1 - p_Y` in
  `X`, which is `X \ Y`.
- For `w in E'`, `W(w) = W_0(w) + p_Y` by Step 3.  So `W(w) = 1` iff
  `W_0(w) = 1 - p_Y`.

## Step 5: finite orbits, superperfect bases, connectedness (items 3-5)

- **Item 3.**  The stabilizer of a point of a finite orbit has finite
  index in `G`.  So it is `G` when `G` has no proper finite-index
  subgroup.  A finite clopen subset of `X` consists of isolated points.
- **Item 4.**  Put `K = R cap [F,F]`.
  - `eps(M_G)` is the image of `R` in `Z^n = F^ab`.  Its cokernel is
    `G^ab = 0`, so `eps` is onto.
  - Its kernel is `K/[F,R]`, which is `H_2(G)` by Hopf's formula.  If
    `H_2(G) = 0`, then `eps` is an isomorphism.
  - So every character of `M_G`, that is, every fixed point, has the form
    `psi o eps`.
- **Item 5.**
  - `R` is free (Nielsen-Schreier), so `M = R^ab` is free abelian.  It is
    nonzero, since `G` is infinite and `F` is not.
  - The Pontryagin dual of a torsion-free discrete abelian group is
    connected (Hewitt-Ross, Abstract Harmonic Analysis I, Theorem 24.25).
    So `hat M` is a connected compact group, and its only clopen subsets
    are the empty set and `hat M`.
  - In a regular model `X = hat M`.  So there is no isolated point, and no
    projection of `A` other than `0` and `1`.  Items 1-2 are vacuous
    there.

## Where the method stops

Step 2 needs `{chi}` clopen in `X`.
- At a non-isolated fixed point, the spectral projection of `{chi}` exists
  in `A''`, not in `A`.  In the norm corona it has no meaning: the
  corona is not a von Neumann algebra.
- Projections `1_U(W(m))` for open `U` exist only after functional calculus
  in a larger algebra.  They are `G`-invariant only if `U` is.
- Making a near-invariant neighborhood projection exactly invariant in
  norm is the spectral-gap step recorded in
  `commutant-projection-extraction`.

Step 3 needs `chi` liftable.  For a non-liftable fixed point, `U` is a
projective model of `G` with cocycle `chi o c`, whose class in
`H^2(G;T) = Hom(H_2 G, T)` is `chi|H_2(G) != 1`.  The full radical of `G`
says nothing directly about projective models.
