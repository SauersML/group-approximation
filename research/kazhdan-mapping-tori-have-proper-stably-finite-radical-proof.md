---
rg: 2
id: kazhdan-mapping-tori-have-proper-stably-finite-radical-proof
kind: route
title: Kill the invariant corner of a nontrivial tracial representation, then spread it along the automorphism orbit with a Folner wrap of trace 1/N
target: kazhdan-mapping-tori-have-proper-stably-finite-radical
requires:
  - kazhdan-mf-hyperlinear-fragment
artifacts:
  - GroupApproximation/Sofic/KazhdanCorner.lean
---

Notation: `Q`, `(S,kappa)`, `psi`, `G = Q semidirectProduct_psi Z` as in the
claim.  Write `t` for the generator `(1,1)` of `Z`, so every element of `G`
is uniquely `q t^m`, with `t q t^-1 = psi(q)`.  For a finite von Neumann
algebra `M` with faithful normal tracial state `tr`, put
`||x||_2 = tr(x^* x)^(1/2)`.  For a unitary `u`, `||u - 1||_2^2 = 2 - 2 Re tr(u)`.

**Imported definition (Kazhdan pair).**  `(S,kappa)` is a Kazhdan pair when
every unitary representation `(pi,H)` of `Q` having a unit vector `xi` with
`max_{s in S} ||pi(s) xi - xi|| < kappa` has a nonzero `Q`-invariant vector
(Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Definition 1.1.3).
Property (T) for a countable discrete group gives a finite Kazhdan set
(ibid., Theorem 1.3.1 and Proposition 1.3.2).  Contrapositive form used below:

```text
(KP)  if pi has no nonzero invariant vector, then
      max_{s in S} ||pi(s) xi - xi|| >= kappa ||xi||   for all xi in H.
```

## Step 0. The corona algebra is stably finite (SF1)

Let `B = prod_n M_n / (+)_n M_n`.  Then
`M_k(B) = prod_n M_{kn} / (+)_n M_{kn}`, which has the same form.  Suppose
`v in M_k(B)` has `v^* v = 1`.

1. Choose any lift `(v_n)`.  Norm in the quotient is `limsup_n` of the
   coordinate norms, so `||v_n^* v_n - 1|| -> 0`.
2. All singular values of the square matrix `v_n` therefore tend to `1`
   uniformly.
3. So `||v_n v_n^* - 1|| -> 0`, and `v v^* = 1`.

Hence `B` is stably finite.  So `Rad_sf(G) <= Rad_MF(G)`.  The map
`G -> Z -> U(1)`, `q t^m -> exp(i m)`, lands in a stably finite algebra and is
injective on `Z`.  So `Rad_sf(G) <= Rad_MF(G) <= Q x {0}`.

A finite von Neumann algebra `P` with faithful normal tracial state is stably
finite.  `M_k(P)` again has a faithful trace, and `v^* v = 1` gives
`tr(1 - v v^*) = 0`, hence `v v^* = 1`.

## Step 1. A nontrivial tracial representation with no invariant vectors

By `kazhdan-mf-hyperlinear-fragment` (Lean: `hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF`),
`Q` has a nontrivial hyperlinear quotient.  So there is a homomorphism
`tau_0 : Q -> U(M_0)` with `tau_0 != 1`, where `M_0` is a finite von Neumann
algebra with faithful normal tracial state, for instance `R^omega`.

Let `Q` act on `L^2(M_0)` by left multiplication through `tau_0`, and let `H_inv`
be the closed subspace of invariant vectors.

- **The projection lies in `M_0`.**  Right multiplication by elements of
  `M_0` commutes with left multiplication, so it preserves `H_inv`.  Hence the
  orthogonal projection onto `H_inv` commutes with the right action
  `J M_0 J = M_0'`, and so lies in `M_0'' = M_0`.  Call it `f`, a projection
  in `M_0`.
- **`f` absorbs and is central for the image.**  Every vector `f xi` is
  invariant, so `tau_0(q) f = f`.  Taking adjoints of
  `tau_0(q^-1) f = f` gives `f tau_0(q) = f`.  So `f` commutes with every
  `tau_0(q)`.
- **`f != 1`.**  Otherwise `tau_0(q) = tau_0(q) f = f = 1` for all `q`, which
  is false.

Put `e = 1 - f != 0` and `M = e M_0 e`, with the normalized trace
`tr_M(x) = tr(x)/tr(e)`.  Here `tr(e) > 0` by faithfulness, and `tr_M` is a
faithful normal tracial state.  Put `tau(q) = tau_0(q) e`.  Since `e` commutes
with the image, `tau : Q -> U(M)` is a homomorphism.

**No invariant vectors.**  `L^2(M)` is the closure of `e M_0 e` inside
`e L^2(M_0)`, with a rescaled inner product.  If `xi in L^2(M)` is
`tau(Q)`-invariant, then `xi = e xi` and `tau_0(q) xi = xi`, so `xi in H_inv`
and `xi = f xi`.  So `xi = e f xi = 0`.

## Step 2. The Kazhdan bound is psi-invariant

Fix `j in Z`.  The representation `q -> tau(psi^-j(q))` on `L^2(M)` has the
same image group `tau(Q)` as `tau`, so it has no nonzero invariant vector.
Apply (KP) to it with `xi = 1_M`.  Note that
`||tau(psi^-j(s)) 1_M - 1_M||_{L^2(M)} = ||tau(psi^-j(s)) - 1||_2`.  So

```text
(B)  sum_{s in S} || tau(psi^-j(s)) - 1 ||_2^2  >=  kappa^2     for every j in Z.
```

The constant is independent of `j`.  Precomposition by an automorphism does
not change which subspaces are invariant, and (KP) is applied to one fixed
finite set `S`.

## Step 3. Folner spreading along the automorphism orbit (SF3, SF2)

Fix `N >= 1`.  Let `M_N(M)` carry the faithful normal tracial state
`tr_N (x) tr_M`.  Index the diagonal blocks by `j in Z/N` with
representatives `0,...,N-1`.  Define

```text
sigma_N(q) = diag( tau(psi^-j(q)) )_{j = 0..N-1}     (a homomorphism Q -> U(M_N(M)))
U_N e_j    = e_{j+1 mod N}                            (cyclic shift, a unitary)
sigma_N(q t^m) = sigma_N(q) U_N^m.
```

**The relation fails on one block.**  For a diagonal `D = diag(a_j)`,
`U_N D U_N^* = diag(a_{j-1 mod N})`.  With `a_j = tau(psi^-j(q))`, the block
`j` of `sigma_N(psi(q))` is `tau(psi^-(j-1)(q)) = a_{j-1}`.  So the two agree
at every `j != 0`.  The only exception is the wrap block `j = 0`, which has
normalized trace `1/N`.  This is (SF3).

**Almost multiplicativity.**  In `G`, `(q t^m)(q' t^m') = q psi^m(q') t^(m+m')`.
Iterating the previous paragraph, `U_N^m sigma_N(q') U_N^-m` and
`sigma_N(psi^m(q'))` differ on at most `min(|m|,N)` blocks.  On each block both
entries are unitary, so the difference has norm at most `2`.  Hence

```text
|| U_N^m sigma_N(q') U_N^-m - sigma_N(psi^m(q')) ||_2  <=  2 (|m|/N)^(1/2).
```

Left and right multiplication by unitaries preserve `||.||_2`.  So

```text
|| sigma_N(g) sigma_N(g') - sigma_N(g g') ||_2 <= 2 (|m|/N)^(1/2),  g' = q' t^m.
```

**Ultraproduct.**  Fix a free ultrafilter `omega` on `N`.  Let
`P = prod_omega (M_N(M), tr_N (x) tr_M)` be the tracial ultraproduct: bounded
sequences modulo those with `lim_omega ||x_N||_2 = 0`.  This is a finite von
Neumann algebra with faithful normal tracial state
`tr_P(x) = lim_omega tr(x_N)` (imported: Brown--Ozawa, *C*-algebras and
Finite-Dimensional Approximations*, Appendix A, tracial ultraproducts).
Unitary sequences give unitaries of `P`.  By the estimate above, for fixed
`g,g'` the defect tends to `0` in `||.||_2`.  So
`sigma(g) = [(sigma_N(g))_N]` is a homomorphism `G -> U(P)`.

**Nontriviality with the uniform constant.**  For `s in S`,

```text
|| sigma_N(s) - 1 ||_2^2 = (1/N) sum_{j=0}^{N-1} || tau(psi^-j(s)) - 1 ||_2^2 .
```

Sum over `s in S` and exchange the finite sums.  By (B) every inner sum is at
least `kappa^2`, so `sum_s ||sigma_N(s) - 1||_2^2 >= kappa^2` for every `N`.
Since `||sigma(s) - 1||_2 = lim_omega ||sigma_N(s) - 1||_2` and `S` is
finite, `sum_s ||sigma(s) - 1||_2^2 >= kappa^2 > 0`.  So `sigma(s) != 1` for
some `s in S`, with `s in Q x {0}`.  By Step 0, `P` is stably finite.  Hence
`s` is not in `Rad_sf(G)`, which is (SF2).

## Step 4. Consequences stated in the claim

- **Finite targets.**  `sigma` extends to a unital `*`-homomorphism
  `C*_max(G) -> P`.
  - Any identity of projections forced in every stably finite quotient of
    `C*_max(G)` holds in `P`.  One example is `t p_L t^* = p_L` for a Kazhdan
    `L <= Q` with `t L t^-1 <= L`.
  - This uses that a unital finite C*-algebra has only finite projections: if
    `w^* w = p` and `w w^* = p' < p`, then `v = w + (1 - p)` is an isometry and
    not a unitary.
  - An argument that deduces `q in Rad_MF(G)` using only such consequences
    gives `q in Rad_sf(G)`.  By (SF2) it cannot do this for all `q in Q`.
- **Invariant and death step.**  The only place where `sigma_N` fails to
  represent `G` is the wrap block of trace `1/N`, while (B) holds on every
  block.  So a certificate that is true in every tracial ultraproduct of
  approximate representations whose defects vanish in `||.||_2` cannot put
  `S` into the radical.  Any valid certificate must use a defect that is small
  in operator norm but carried by a block of vanishing trace.
