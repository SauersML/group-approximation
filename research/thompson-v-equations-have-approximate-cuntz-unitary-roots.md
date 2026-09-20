---
rg: 2
id: thompson-v-equations-have-approximate-cuntz-unitary-roots
kind: claim
title: Every nonsingular equation over the canonical copy of Thompson's V in U(O_2) has operator-norm approximate roots in U(O_2)
distinct_from:
  kl-holds-over-thompson-v: that asks for an abstract overgroup of V solving the equation; this asks for norm-approximate roots in one fixed ambient, U(O_2) with V's canonical copy, which implies that through kl-holds-over-thompson-v-via-approximate-cuntz-roots and may fail while it holds.
  tracial-algebras-solve-nonsingular-equations-in-extensions: that is the tracial root theorem, which needs a trace and allows any tracial extension; O_2 has no trace, and this fixes the ambient and the operator norm.
  thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes: that is MF-ness of V, which asks for finite-dimensional operator-norm models; this asks for no finite-dimensional model, and every proof of it by finite-dimensional perturbation of the coefficients inside O_2 proves V is MF.
  thompson-v-census-word-has-an-exact-cuntz-unitary-root: that is the finite-coefficient case, with exact roots, including the census word w0; this is every nonsingular equation, including the frontier census words whose coefficients generate V.
  overgroup-room-does-not-supply-a-root: that shows the room in an overgroup does not produce a root; this names one overgroup, U(O_2^omega), and asks whether it has the root, which is a statement about equations and not about room.
---

**OPEN.**

**Setting.** Let `U : V -> U(O_2)` be the canonical copy of Thompson's `V`: the element that maps the cone `u_i` onto the
cone `v_i` goes to `U_g = sum_i s_(v_i) s_(u_i)^*`.

**Statement.** For every `w in V * <t>` with nonzero `t`-exponent sum and every `epsilon > 0`, there is `T in U(O_2)` with

```text
|| w(U, T) - 1 || < epsilon      (operator norm in O_2).
```

**Equivalent form.** Taking a sequence of such `T` with `epsilon -> 0` gives an element of the norm ultrapower. So the
statement holds for `w` iff `w(U, T) = 1` has an exact root `T in U(O_2^omega)`, where `O_2 -> O_2^omega` is the diagonal
embedding.

By `kl-holds-over-thompson-v-via-approximate-cuntz-roots`, this claim implies `kl-holds-over-thompson-v`, and so it
refutes `kl-violating-equation-over-thompson-v`.

## What is proved

1. **Finite coefficient subgroups.** Suppose the coefficients of `w` generate a finite subgroup. Then there is an exact
   root in `U(O_2)` (`thompson-v-census-word-has-an-exact-cuntz-unitary-root`, item 2). This covers `w0 = ctataT`, whose
   explicit root is a lifted reflection.
2. **Finite-dimensionally approximable coefficients.** Call a tuple `u in U(O_2)^k` *FD-approximable in `O_2`* if for
   every `delta > 0` there is `u' in U(O_2)^k` such that
   - `||u_i - u'_i|| < delta` for each `i`, and
   - `C*(u')` is finite-dimensional.

   If the coefficient tuple of `w` is FD-approximable, the claim holds for `w`.

   *Proof.* `C*(u')` is `⊕ M_(d_j)`. Solve blockwise with the Gerstenhaber--Rothaus surjectivity of
   `nonsingular-equations-preserve-matrix-certificates`. This gives `T' in U(C*(u'))` with `w(u', T') = 1`. A unitary
   word is `1`-Lipschitz in each letter, so `||w(u, T') - 1|| <= L delta`, where `L` is the number of coefficient
   letters of `w`.
3. **That route is MF, not new.** Suppose a finite generating tuple `g` of `V` has `U(g)` FD-approximable in `O_2`. Then
   `V` is MF.

   *Proof.* Take `u'^(n)` with `delta_n -> 0` and `C*(u'^(n)) = ⊕_j M_(d_j) <= M_(D_n)`, block-diagonally and unitally.
   - For each relator `r`, `||r(u'^(n)) - 1|| <= |r| delta_n -> 0`.
   - For each `1 != x in V`, `||x(u'^(n)) - 1|| -> ||U_x - 1||`. This is `> 0` because the canonical copy is faithful
     (`kl-holds-over-thompson-v-via-approximate-cuntz-roots`, Step 1).

   So `x ↦ [x(u'^(n))]` is an injective homomorphism `V -> U(prod M_(D_n) / ⊕ M_(D_n))`.

   So every proof of this claim by finite-dimensional perturbation of the coefficients inside `O_2` passes through MF-ness
   of `V`, which is open (`thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes`). MF-ness already gives
   `kl-holds-over-thompson-v` through `kervaire-laudenbach-holds-for-mf`.

## Why it can fail on its own

The claim implies `kl-holds-over-thompson-v`, and no converse is known. A root could exist in some overgroup of `V` without
any exact C\*-algebra carrying one over the canonical norm. The claim fixes both:
- the norm on `C[V]`, namely `A_can = C*(U(V)) <= O_2`, which is exact as a subalgebra of `O_2`;
- the ambient.

A failure here gives no violation.

## Attempts

1. **Topology of `U(O_2)`.** Dead as a method.
   - The Gerstenhaber--Rothaus proof is a degree argument: `t ↦ w(u, t)` on the compact manifold `U(d)` has degree `m^d`.
   - `U(O_2)` is path-connected, because `K_1(O_2) = 0` and `stw58-simple-pure-k1-bijective` identifies
     `U(A)/U_0(A)` with `K_1(A)` for purely infinite simple `A`. So a path from each coefficient to `1` gives a homotopy
     from `t ↦ w(u, t)` to the power map `t ↦ t^m`.
   - It is recalled, but not imported verbatim here, that `pi_k(U(A)) = K_(k+1)(A)` for purely infinite simple `A`
     (S. Zhang). With that, `U(O_2)` is weakly contractible. The power map is then homotopic to a constant map, which is
     not surjective.
   - So no argument that reads approximate surjectivity off the homotopy class of the word map can prove the claim. There
     is no fundamental class to carry a degree.
2. **Change of embedding.** Vacuous, modulo a recalled citation.
   - It is recalled, not imported verbatim, that Kirchberg--Phillips (J. reine angew. Math. 525 (2000)) proved two
     things: every separable unital exact C\*-algebra embeds unitally in `O_2`, and any two unital injective
     `*`-homomorphisms from a separable unital exact algebra into `O_2` are approximately unitarily equivalent.
   - Approximate unitary equivalence moves approximate roots: conjugate `T` by the implementing unitaries, and the
     finitely many coefficient letters move by less than `delta`. So the claim for `w` depends only on the abstract
     algebra `A_can` with its generators.
   - It holds as soon as some separable exact unital C\*-algebra containing `A_can` unitally contains a root or
     approximate roots.
   - The move that the orbit-type obstruction forces in spatial ambients, re-embedding the coefficients, therefore has
     no content here.
3. **Finite-dimensional perturbation.** Reduces to MF-ness of `V` (item 3 above). Dead as a new route.
4. **Spatial and cutoff models inside `O_2`.** Dead for the known reasons.
   - Roots of the form `Phi_l(P)` with `P` a permutation matrix are internal roots in `V`. The orbit type of `F = S_3`
     forbids them for `w0` (`higman-thompson-roots-miss-a-kl-word-over-thompson-v`).
   - Truncations of Cantor orbits are ratio models. They die at the `l^p` isoperimetric inequality of
     `thompson-v-cantor-orbits-have-no-folner-sets`.
