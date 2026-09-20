---
rg: 2
id: separated-ring-linear-seeds-char-p-or-deep-radical-proof
kind: route
title: Filter by m-adic depth, then let commuting normal subgroups collapse the congruence kernel
target: separated-ring-linear-seeds-reduce-to-char-p-or-deep-radical
requires:
  - mf-radical-functoriality
  - lef-implies-operator-mf
---

Notation is as in the target.  Put `S = M_n(R)`.  Then
`intersection_j m^j S = M_n(intersection_j m^j R) = 0`.  An element of
`Gamma(q)` has the form `1 + qX` with `X in S`.  Its inverse is again in
`Gamma(q)`, because reduction mod `q` is a homomorphism.

## Step 1: the filtration

Let `a, b >= 1`, `x = 1 + m^a X in Gamma(m^a)` and `y = 1 + m^b Y in Gamma(m^b)`.

- **Commutators.**  `xy - yx = m^(a+b)(XY - YX)`, and
  `[x,y] - 1 = (xy - yx) x^(-1) y^(-1)`.  So
  `[Gamma(m^a), Gamma(m^b)] <= Gamma(m^(a+b))`.
- **Powers.**  `x^m = 1 + sum_(k>=1) C(m,k) m^(ka) X^k`.  Only powers of the
  single element `X` occur, so the binomial expansion is valid.  The `k = 1`
  term is `m^(a+1) X`.  For `k >= 2`, `ka >= 2a >= a+1`.  So
  `x^m in Gamma(m^(a+1))`.
- **Separation.**  `intersection_j Gamma(m^j) = 1`.

Hence `Gamma(m)/Gamma(m^j)` has the central series
`Gamma(m^a)/Gamma(m^j)`, for `1 <= a <= j`.  Its factors are abelian of
exponent dividing `m`.  So `Gamma(m)/Gamma(m^j)` is nilpotent of class
`< j`, and its exponent divides `m^(j-1)`.

## Step 2: part (0)

Let `H <= Gamma(m)` be finitely generated.  Then `H/(H cap Gamma(m^j))` is
finitely generated and nilpotent, and it has finite exponent.

- A finitely generated nilpotent torsion group is finite.
- Its order involves only primes dividing `m`, by the exponent bound.
- The kernels `H cap Gamma(m^j)` intersect in `1`.

So `H` is residually finite.  A residually finite group is LEF, and so it
is MF by `lef-implies-operator-mf`.

If `G` is finitely generated and `H = G cap Gamma(m)` has finite index, then
`H` is finitely generated, hence residually finite.  A group with a
residually finite subgroup of finite index is residually finite: intersect
the conjugates of a finite-index normal subgroup of `H` to get one of `G`.
So `G` is MF and `Rad_MF(G) = 1`.

## Step 3: part (1)

`Rad_MF(G)` is carried into `Rad_MF(pi(G))` by the surjection `pi = pi_(m^j)`
(`mf-radical-functoriality`).  Given `d != 1`, separation gives some `j_0`
with `d` not in `Gamma(m^(j_0))`.  Since the kernels decrease,
`pi_(m^j)(d) != 1` for all `j >= j_0`.

## Step 4: two facts about (NC) groups

- **(NC1)** If `A` and `B` are normal in `E` with `A cap B = 1`, then
  `[A,B] <= A cap B = 1`.  So `B <= C_E(A)`, and `A = 1` or `B = 1`.  Hence
  a finite intersection of nontrivial normal subgroups is nontrivial.
- **(NC2)** A nilpotent normal subgroup `V` of `E` is trivial.  Otherwise
  its center `Z(V)` is nontrivial.  It is characteristic in `V`, so it is
  normal in `E`, and `Z(V) <= C_E(Z(V)) = 1`, which is a contradiction.

**Torsion-free AH groups are (NC).**  Let `E` be acylindrically hyperbolic,
acting acylindrically and non-elementarily on a hyperbolic space `X`, and
let `1 != N` be normal.

- If `E` is torsion-free, `N` is infinite.  By Osin, *Acylindrically
  hyperbolic groups* (Trans. AMS 2016), Corollary 1.5 and its proof, `N`
  acts non-elementarily on `X`.  So `N` contains two independent
  loxodromic elements `g` and `h`, with disjoint fixed-point pairs in
  `boundary X`.
- By Dahmani, Guirardel and Osin (Mem. AMS 2017), Lemma 6.5 and
  Corollary 6.6, `C_E(g)` lies in the virtually cyclic group `E(g)`.  Every
  infinite-order element of `E(g)` is loxodromic with fixed points
  `{g^+, g^-}`, and likewise for `h`.
- An element `1 != c in C_E(N)` lies in `C_E(g) cap C_E(h) <= E(g) cap E(h)`.
  It has infinite order because `E` is torsion-free, so its fixed-point pair
  would equal both `{g^+, g^-}` and `{h^+, h^-}`.  This is a contradiction.
  So `C_E(N) = 1`.

## Step 5: part (2)

Let `D = Rad_MF(E)`, a nontrivial normal subgroup (normal by
`mf-radical-functoriality` for inner automorphisms), and `N_j = E cap Gamma(m^j)`.

**Dichotomy.**  (A) and (B) are exclusive: `N_j = 1` forces `D cap N_j = 1`.
They are exhaustive: if `D cap N_j = 1` for some `j`, then (NC1) with
`A = D != 1` gives `N_j = 1`.  In (B), `D_j = D cap Gamma(m^j)` are nontrivial
normal subgroups of `E`, decreasing, with trivial intersection.  Their
finitely generated subgroups lie in `Gamma(m)`, so they are residually
finite by Step 2.  Also `1 != D_j <= Gamma(m^j) <= Gamma(p)` for each `p | m`,
so `E cap Gamma(p) != 1`.

**From level `m^j` to a prime in branch (A).**  Suppose `N_j = 1`.  Then
`pi_(m^j)` embeds `E` in `GL_n(R')`, where `R' = R/m^j R`.

- Choose `J` with `m^j | r^J`, so `r^J R' = 0`.
- The kernel `W` of `GL_n(R') -> GL_n(R'/rR')` is `1 + r M_n(R')`.  Step 1,
  run with `r` in place of `m`, gives the central series `1 + r^a M_n(R')`,
  `1 <= a <= J`, with `1 + r^J M_n(R') = 1`.  So `W` is nilpotent.
- `E cap Gamma(r)` embeds in `W`, so it is a nilpotent normal subgroup of
  `E`, and it is trivial by (NC2).
- `R'/rR' = R/rR`.  By the Chinese remainder theorem for the pairwise
  coprime central integers `p | r`, this is `prod_(p|r) R/pR`.  Here
  `aR + bR = R` and `aR cap bR = abR` for coprime integers `a` and `b`.
- So `E` embeds in `prod_p GL_n(R/pR)`.  The kernels `K_p = E cap Gamma(p)`
  are normal with intersection `E cap Gamma(r) = 1`.  By (NC1), some `K_p = 1`.

## Step 6: part (3)

A finitely generated linear group over a commutative ring `A` lies in
`GL_n(A_0)`.  Here `A_0` is the finitely generated subring generated by
the entries and the inverse determinants.  `A_0` is residually finite, as
every finitely generated commutative ring is: it is noetherian and
Jacobson, with finite residue fields, and Krull intersection applies at
each maximal ideal.  So the group is residually finite (Mal'cev), hence MF
with trivial radical.

- In branch (A), apply this with `A = R/pR`.
- If `R` is commutative, apply it to `E <= GL_n(R)` directly.
