---
rg: 2
id: partial-burnside-low-degree-plancherel-proof
kind: route
title: Each small irreducible satisfies the law on the degree radius and so kills a fixed finite-index subgroup; count Plancherel mass through the quotient
target: partial-burnside-finite-quotients-low-degree-plancherel-bound
requires:
  - bounded-degree-partial-burnside-reps-factor-through-burnside
---

**Proof.** Notation as in the claim.

**Step 0: `K_c` has finite index.** This is Step 0 of
`approximate-burnside-models-low-degree-mass-proof`, repeated so this route
stands alone. For a representation `rho : F -> GL_d(C)`, `d <= c`, with
`rho(g)^N = 1` for all `g`, clause 2 of
`bounded-degree-partial-burnside-reps-factor-through-burnside` gives
`|rho(F)| <= M_c := max_(d <= c) f(d) N^d`. So `ker rho` has index `<= M_c`. `F` has
finitely many subgroups of index `<= M_c`, so `K_c`, the intersection of all such
kernels, has finite index `C(m,N,c)`. Moreover `F/K_c` embeds in a finite product
of the images `rho(F)`, each of exponent dividing `N`, so `F/K_c` has exponent
dividing `N`. (Unitarizing, the same `K_c` arises from unitary representations,
as in that route.)

**Step 1: small irreducibles kill `K_c`.** Let `pi` be an irreducible
representation of `Q` of dimension `d <= c`, and `rho = pi o p : F -> GL_d(C)`. By
hypothesis `rho(h)^N = 1` for `1 <= |h| <= R_c`. Since `R_c >= R_0(m,N,d)` and
`X_R(d)` shrinks as `R` grows, `rho in X_(R_c)(d) ⊂ X_(R_0(m,N,d))(d) =
Hom(B(m,N), GL_d(C))` by clause 1 of the bounded-degree claim. So
`rho(K_c) = 1`, that is `pi` is trivial on `p(K_c)`.

**Step 2: count.** `M = p(K_c)` is normal in `Q`, and by Step 1 every irreducible
of `Q` of dimension `<= c` is inflated from an irreducible of `Q/M`. Distinct
irreducibles of `Q` inflate from distinct irreducibles of `Q/M`, so

```text
sum_(dim pi <= c) (dim pi)^2 <= sum over irreducibles of Q/M of (dim)^2 = |Q/M|.
```

`Q/M` is a quotient of `F/K_c`, so `|Q/M| <= C(m,N,c)`. Dividing by `|Q|` gives
clause 1. ∎

**Clause 2.** If every irreducible of `Q` has dimension `<= c`, Step 1 shows `M`
lies in the kernel of the regular representation, which is faithful, so `M = 1`.
Then `Q` is a quotient of `F/K_c`: `|Q| <= C(m,N,c)` and `Q` has exponent dividing
`N` by Step 0. If `Q` has an abelian subgroup `A` of index `<= c`, let `pi` be an
irreducible of `Q`. `pi|_A` contains a character `chi` of `A`, so by Frobenius
reciprocity `Hom_Q(Ind_A^Q chi, pi) = Hom_A(chi, pi|_A) != 0`. As `pi` is
irreducible it is a quotient of `Ind_A^Q chi`, so `dim pi <= [Q : A] <= c`. ∎

**Clause 3.** Let `A <= Q` be abelian of index `<= c`, and `T` its normal core in
`Q`, which is abelian of finite index. `T` is finitely generated, being of finite
index in a finitely generated group, so `T ≅ Z^r + (finite)` and the
characteristic subgroups `T^n = {t^n : t in T}` satisfy `∩_n T^n = 1` (take `n`
over multiples of the exponent of the torsion part). Each `T^n` is normal in `Q`,
and `Q/T^n` is finite: it is an extension of the finite group `T/T^n` by the
finite group `Q/T`. The quotient `Q/T^n` is `m`-generated, satisfies `h^N = 1` on
the ball of radius `R_c`, and has the abelian subgroup `A/T^n` of index `<= c`. By
clause 2, `|Q/T^n| <= C(m,N,c)` and `Q/T^n` has exponent dividing `N`. Any finite
set of elements of `Q` injects into some `Q/T^n` (as `∩_n T^n = 1` and the `T^n`
decrease along multiples), so `|Q| <= C(m,N,c)` and `Q` has exponent dividing `N`. ∎
