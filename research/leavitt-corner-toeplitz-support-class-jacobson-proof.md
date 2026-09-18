---
rg: 2
id: leavitt-corner-toeplitz-support-class-jacobson-proof
kind: route
title: Identify Toeplitz coefficients with the Jacobson ring, use the simple self-centralizing finitary monolith, and push the Haar fixed-point character through the corner
target: leavitt-corner-toeplitz-support-class-is-jacobson-hyperlinearity
requires:
  - leavitt-corner-bcs-support-coefficient-gate
  - steinberg-finite-presentation-and-kazhdan-theorem
  - cohn-elementary-group-is-not-lef
---

The notation is that of the target claim.

## Step 1. (A) Coefficients

`J` acts on `F_2^(N)` by `S e_k = e_(k+1)`, `T e_k = e_(k-1)` and `T e_0 = 0`.
This is Jacobson's faithful representation. The normal forms `S^a T^b` act
linearly independently. The matrix units `e_ab = S^a Q T^b` act as
`e_a (x) e_b^*`, and `M_inf := span{e_ab}` consists exactly of the elements of
`J` that act with finite rank.

Why `M_inf` is exactly the finite-rank part. Mod `M_inf` an element is a
nonzero Laurent polynomial `f` of degree `d`, and then `x e_k = sum_j f_j e_(k+j)`
for all large `k`. The leading terms `e_(k+d)` are independent, so `x` has
infinite rank.

**Every nonzero ideal `I` of `J` contains `Q`.** Take `0 != x in I`. Choose
`b` with `x e_b != 0`, and `a` with coefficient `c_a != 0` of `e_a` in `x e_b`.
Then `Q T^a x S^b Q = c_a Q`: both sides are rank-one operators sending `e_0`
to `c_a e_0` and killing `e_k` for `k > 0`. So `Q in I`.

Now `S |-> s_2`, `T |-> t_2` defines a homomorphism `J -> R`, because
`t_2 s_2 = 1`. It sends `Q` to `1 - s_2t_2 = s_1t_1 = q != 0` (`R` is simple and
nonzero). So its kernel is an ideal not containing `Q`, hence zero. Its image is
`T_2`, so `J` is isomorphic to `T_2` and `x_13(Q)` corresponds to `z`.

## Step 2. (B) Monolith

**`L` is contained in `EL_n(J)`.** An element `g in L` is `1 + finite rank`. Its
entries lie in `M_inf`, and so do those of `g^(-1)`. So `g` lies in
`GL_(nm)(F_2)`, embedded through the corner `e_m = sum_(a<m) e_aa`, for some `m`.

Over the field `F_2` we have `GL_(nm)(F_2) = SL_(nm)(F_2) = E_(nm)(F_2)`.
- A cross-block transvection is `1 + e_((i,a),(j,b)) = x_ij(e_ab)` with `i != j`.
- A within-block transvection with `a != b` is the commutator
  `[1 + e_((i,a),(k,c)), 1 + e_((k,c),(i,b))]` for any `k != i`.

So `L <= EL_n(J) <= GL_n(J)`. Also `L` is normal in `GL(V)`.

**`L` is simple.** It is the increasing union of the simple groups
`SL_k(F_2)` with `k >= 3`.

**`C_GL(V)(L) = 1`.** If `g` commutes with every transvection `1 + v (x) phi`
(`phi(v) = 0`), then `g v (x) phi o g^(-1) = v (x) phi`. Hence `g v in F_2 v` for
all `v`, so `g` is a scalar, that is `g = 1`.

**The monolith argument.** Let `L <= H <= GL(V)` and `phi(w) != 1`.
- `ker(phi) cap L` is normal in `L` and misses `w`, so it is trivial.
- `ker(phi)` normalizes `L`, so `[ker phi, L] <= ker(phi) cap L = 1`.
- Hence `ker(phi) <= C(L) = 1`.

## Step 3. (C) and (TJ1)

(C) follows from Steps 1 and 2:
- a homomorphism of `EL_20(J)` into a hyperlinear group, or into `U(R^omega)`,
  that retains `w` is injective, so `EL_20(J)` is hyperlinear;
- the converse is the identity map.

For (TJ1), the Whitehead lemma gives `diag(g, g^(-1)) in EL_40(J)` for every
`g in GL_20(J)`. The map `g |-> diag(g, g^(-1))` is an injective homomorphism.

## Step 4. (D) Class reduction

Suppose `S_X <= T_2`. Every `pi(g)^(+-1)` with `g in X`, and `pi(z)`, has
entries in `T_2`. So `pi` restricts to a homomorphism `h : Gamma_X -> GL_20(T_2)`,
which is `GL_20(J)` by Step 1, with `h(z) = w != 1`.

If `GL_20(J)` is hyperlinear, then `h` is a homomorphism into a hyperlinear
group with `h(z) != 1`. This contradicts the hyperlinear shadow gate of
`leavitt-corner-bcs-support-coefficient-gate`. By (TJ1), `GL_20(J)` is
hyperlinear whenever `EL_40(J)` is. The second bullet of (D) is the
contrapositive.

## Step 5. (E) The Haar character

`GL_20(J)` acts on the compact abelian group `V^* = prod F_2` by
`chi |-> chi o g^(-1)`, and this action preserves Haar measure `mu`.

**Fixed sets.** `Fix(g)` is the annihilator of `(g^(-1) - 1)V = g^(-1)(1-g)V`,
which has the same dimension as `(g-1)V`.
- If `(g-1)V` is finite, the annihilator is a closed subgroup of index
  `|(g-1)V|`.
- If `(g-1)V` is infinite, the annihilator is a closed subgroup of infinite
  index, hence Haar-null.

By Step 1, `g-1` has finite rank iff `g in L`. This gives `(TJ2)`.

**`tau` is a character.** For any measure-preserving action,
`g |-> mu(Fix g)` is positive definite and conjugation invariant: it is the
restriction to the group of the canonical trace on the von Neumann algebra of
the action groupoid.

**Faithfulness.** `tau(g) = 1` forces `g in L` and `(g-1)V = 0`, so `g = 1`.

**The head.** `w - 1 = e_13 (x) Q` has rank one, so `tau(w) = 1/2`.

**Pushing through the corner.** Suppose `LNC3` has `S_X <= T_2` and `tau` is
Connes-embeddable.
- The character `tau o h` of `Gamma_X` is Connes-embeddable. Its GNS algebra
  embeds in that of `tau` by restriction and pullback.
- By Step 1 of the gate proof, `Phi` takes values in `C[Gamma_X]`.
- Composing `Phi` with the GNS representation of `tau o h` gives a unital
  *-representation of `A(B_loop)` on the corner `P_z`, where
  `tau(P_z) = (1 - tau(w))/2 = 1/4 > 0`.
- The normalized corner trace is a Connes-embeddable tracial state on
  `A(B_loop)`. This contradicts Step 0 of the gate proof: `A(B_loop)` has no
  Connes-embeddable tracial state.

Finally, a faithful Connes-embeddable character gives an injective
homomorphism into `U(R^omega)`. So `tau` Connes-embeddable implies `GL_20(J)`
is hyperlinear.

## Step 6. (F) Affine models die

Let `sigma_k : F_Sigma -> Aff(X_k)` be maps on the free group with each `X_k`
a finite `F_2`-space. Assume `d_Hamm(sigma_k(r), id) -> 0` for every relator
`r` of `St_20(J)`, with the generators mapped through a fixed word map.

**The gap.** A non-identity affine map fixes either nothing or a coset of a
proper subspace. Either way it moves at least half of all points.

**Exactness.** By `steinberg-finite-presentation-and-kazhdan-theorem`
(`J` is a finitely presented unital ring and `20 >= 4`), `St_20(J)` is
finitely presented. So for all large `k`, `sigma_k` kills a finite set of
defining relators exactly. It therefore induces a homomorphism
`St_20(J) -> Aff(X_k)` into a finite group.

**The head dies.** By item 1 of `cohn-elementary-group-is-not-lef` (finite
images of groups satisfying the Steinberg relations over `J` kill `x_13(Q)`),
`sigma_k(w) = id` for all large `k`. The limiting fixed-point density of `w`
is therefore `1 != tau(w)`.

The same argument applies to any model into finite permutation groups whose
non-identity elements move a uniformly positive fraction of points.
