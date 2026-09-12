# Torus fusion is forced on every finite image of a half-corner comparison

Date: 2026-09-11 (fork `kaplansky-df`). Exact representation theory; no
computation. No Kaplansky counterexample and no proof of direct finiteness
is claimed.

Section 1 proves a general balance theorem for split comparisons between
finite-subgroup projectives: every finite image of the actor group, injective
on the finite subgroup, must identify the two induced projectives, so their
induced Brauer characters agree. Section 2 computes the Brauer-character
difference of the two half-corner projectives. It sits on exactly three
order-three torus classes of `GL_2(F_4)` with weights `+2/3, -1/3, -1/3`.
Section 3 draws the consequence: an actor group supporting a comparison must
fuse those three classes in every finite image that is injective on the
chart. Section 4 records that the Leavitt unit group itself does fuse them,
so every additive invariant is blind to the comparison, and which recorded
exclusions this subsumes.

## 1. Split comparisons balance induced Brauer characters

**Theorem 1.** Let `p` be prime, `G` a group, `K <= G` a finite subgroup, and
`e,f in F_p[K]` idempotents. Suppose

```text
Z in e F_p[G] f,       L in f F_p[G] e,       L Z = f.              (C)
```

Let `H <= G` be any subgroup containing `K` and the support of `Z`, and let
`pi : H -> F` be a homomorphism to a finite group which is injective on `K`.
Write `P_e = e F_p[K]` and `P_f = f F_p[K]` for the right projective modules.

1. `Ind_{pi K}^F P_f` is isomorphic to a direct summand of `Ind_{pi K}^F P_e`.
2. If `dim P_e = dim P_f`, then `Ind P_f ~= Ind P_e`, and for every
   `p`-regular `x in F`

   ```text
   sum over K-classes c with pi(c) inside x^F of
       ( beta_e(c) - beta_f(c) ) / |C_K(c)|  =  0,                  (B)
   ```

   where `beta_e, beta_f` are the Brauer characters of `P_e, P_f`.

No hypothesis on `H`, on `F` or on the support of `L` is used beyond the ones
displayed.

*Proof.* Let `E_H : F_p[G] -> F_p[H]` keep the coefficients on `H` and discard
the rest. It is a bimodule map over `F_p[H]`. Since `Z` and `f` lie in
`F_p[H]`, `E_H(L) Z = E_H(L Z) = f`. Replace `L` by `f E_H(L) e`; it lies in
`f F_p[H] e`, and `(f E_H(L) e) Z = f E_H(L) Z = f`, because `e Z = Z`.

Apply the unital ring homomorphism `pi_* : F_p[H] -> F_p[F]` and write bars for
images. Then `Lbar Zbar = fbar`, `Zbar = ebar Zbar fbar` and
`Lbar = fbar Lbar ebar`. Put `q = Zbar Lbar`. Then
`q^2 = Zbar (Lbar Zbar) Lbar = Zbar fbar Lbar = q`, and
`ebar q = q = q ebar`. Left multiplication by `Zbar` maps `fbar F_p[F]` onto
`q F_p[F]`, with inverse left multiplication by `Lbar`. So
`fbar F_p[F] ~= q F_p[F]`, a direct summand of `ebar F_p[F]`.

Because `pi` is injective on `K`, `F_p[F]` is a free left module over
`F_p[pi K] ~= F_p[K]`. Hence `ebar F_p[F] ~= P_e (x)_{F_p[K]} F_p[F] = Ind P_e`,
of dimension `[F : pi K] dim P_e`, and likewise for `f`. This proves item 1.

If the dimensions agree, `q F_p[F]` is contained in `ebar F_p[F]` and has the
same finite dimension, so the two right ideals are equal. Then `ebar` lies in
`q F_p[F]`, whence `q ebar = ebar`; and `q ebar = q`. So `q = ebar` and
`Ind P_f ~= Ind P_e`.

Isomorphic modules have equal Brauer characters, and the Brauer character of
an induced module is the induced class function on `p`-regular elements:

```text
Ind phi (x) = (1/|K|) sum_{y in F, y^-1 x y in pi K} phi(y^-1 x y)
            = |C_F(x)| sum_{c : pi(c) inside x^F} phi(c) / |C_K(c)|.
```

Dividing by `|C_F(x)|` gives (B). `square`

*Remarks.* The same argument applies to `M_n(F_p[K])`. Without equal
dimensions, item 1 still gives, for each simple `F`-module, the inequality
between projective-cover multiplicities in `Ind P_f` and in `Ind P_e`. Any
finite-dimensional representation of `H` over a finite field has finite image,
so Theorem 1 already covers every finite-dimensional module of `H`.

## 2. The half-corner projectors and their Brauer difference

Notation is that of
[the half-corner artifact](kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md),
Sections 6--8. `Q = L_(F_2)(1,2)^x` and `S = F_2[Q]`. The finite chart is
`K = <g, u g u^-1>`, acting on the four leaves `(000, 001, 010, 011)`. The
pairs `(000,001)` and `(010,011)` are the two `F_4`-coordinates, and
multiplication by `omega` is `G = [[0,1],[1,1]]`. Thus `K = GL_2(F_4) = A x <z>`,
with `A = SL_2(F_4) ~= A_5` and `z = omega I`, of order `180`.

The artifact supplies idempotents `f_+, P in F_2[K]` of regular rank `40` and
the reduced pair `f_0 = f_+(1+E)`, `P_0 = P(1+E)` of regular rank `32`, where `E`
is the center-trivial Steinberg block and `f_+ E ~= P E` inside `F_2[K]`
(Section 7, via the explicit `b in SL_2(F_4)`). Hence

```text
beta(f_+) - beta(P) = beta(f_0) - beta(P_0).                          (D0)
```

The reduced projectors lie in the nontrivial central block, which is
`F_4[A_5]` with `z` acting by `omega`. Section 8 of the artifact computes their
ranks on the four absolutely simple modules `1, V, V^(2), St` and concludes

```text
f_0 F_4[A_5] ~= P(1) + St,          P_0 F_4[A_5] ~= P(V) + P(V^(2)).   (D1)
```

**Brauer characters of `A_5` modulo two.** The 2-regular classes are `1`, the
twenty three-cycles, and two classes of five-cycles. The ordinary characters
`1, chi_3, chi_3', chi_4, chi_5` have values

```text
          1    (123)   5A        5B
chi_1     1     1      1         1
chi_3     3     0      a         b
chi_3'    3     0      b         a
chi_4     4     1     -1        -1
chi_5     5    -1      0         0          a=(1+sqrt5)/2, b=(1-sqrt5)/2.
```

The decomposition modulo two is `chi_1 -> 1`, `chi_3 -> 1+V`,
`chi_3' -> 1+V^(2)`, `chi_4 -> St`, `chi_5 -> 1+V+V^(2)`. By Brauer reciprocity
the projective indecomposable characters are the columns:

```text
Phi_1  = chi_1+chi_3+chi_3'+chi_5 :  (12,  0, 2, 2)
Phi_V  = chi_3+chi_5              :  ( 8, -1, a, b)
Phi_V2 = chi_3'+chi_5             :  ( 8, -1, b, a)
Phi_St = chi_4                    :  ( 4,  1,-1,-1)
```

As a check, `1*12 + 2*8 + 2*8 + 4*4 = 60 = |A_5|`. By (D1),

```text
beta_A(f_0) = Phi_1 + Phi_St = (16,  1, 1, 1),
beta_A(P_0) = Phi_V + Phi_V2 = (16, -2, 1, 1),
Delta_A     = beta_A(f_0) - beta_A(P_0) = (0, 3, 0, 0).                (D2)
```

**Passing to `F_2[K]`.** Regard an `F_4[A_5]`-module `M` on which `z` acts by
`omega` as an `F_2[K]`-module. Then `M (x)_{F_2} F_4 ~= M + M^sigma`, where `sigma`
is the Frobenius twist and `z` acts on `M^sigma` by `omega^2`. Both modules in
(D1) are Frobenius-stable, since `sigma` fixes `1` and `St` and exchanges `V`
and `V^(2)`. Their Brauer characters on the three-cycle class are rational. For
`a in A` of order three and `k in {0,1,2}`, writing `w` for a complex primitive
cube root of unity,

```text
Delta_F2(a z^k) = (w^k + w^(2k)) * Delta_A(a) = 6 if k = 0,  -3 if k = 1, 2,
```

and `Delta_F2` vanishes on every other 2-regular element of `K`: on `z^k` and
on elements of order five `Delta_A = 0`, and elements of order fifteen are
`a z^k` with `a` of order five.

The three supporting sets are single `K`-classes of size `20` with centralizers
of order `9`:

```text
T0 = { a : ord a = 3 }        eigenvalues {w, w^2},  e.g. diag(G, G^2)
T1 = { a z : ord a = 3 }      eigenvalues {w^2, 1},  e.g. diag(G^2, I_2)
T2 = { a z^2 : ord a = 3 }    eigenvalues {1, w},    e.g. diag(I_2, G)
```

The matrices are written on the leaf coordinates `(000,001 | 010,011)`. So the
weighted difference `Delta_F2(c)/|C_K(c)|` is

```text
T0 : +2/3,        T1 : -1/3,        T2 : -1/3,        all other classes : 0.    (D3)
```

As a control, the total mass at the identity is `0`, matching equal regular
ranks, and the lifted 2-adic traces `8/45` of `f_0, P_0` agree.

## 3. Consequence: the actor group must fuse the torus classes

**Corollary 2.** Let `Z in P_0 S f_0` and `L in f_0 S P_0` satisfy `L Z = f_0`.
The same holds for the unreduced pair `(f_+, P)`, and hence for the
comparison of the half-corner artifact's Section 5 after conjugating its source
by `U`. Let `H <= Q` contain `K` and the support of `Z`, and let
`pi : H -> F` be a homomorphism to a finite group which is injective on `K`.
Then `pi(T0)`, `pi(T1)` and `pi(T2)` lie in one conjugacy class of `F`.

*Proof.* Theorem 1 applies, since `dim f_0 F_2[K] = dim P_0 F_2[K] = 32` (or `40`
for the unreduced pair, by (D0)). Take `x in pi(T0)` in (B). By (D3) the sum is
`2/3 - (1/3)[T1 fuses with T0] - (1/3)[T2 fuses with T0]`. It vanishes only if
both `T1` and `T2` fuse with `T0` in `F`. `square`

**Corollary 3 (module form).** For every finite-dimensional `F_2`-module `M` of
such an `H`, writing `a_0(T)` for the dimension of the fixed space of an element
of `T` on `M`,

```text
rank_M(f_0) - rank_M(P_0) = a_0(T0) - ( a_0(T1) + a_0(T2) ) / 2  <=  0.
```

*Proof.* `dim e M = dim Hom_K(e F_2[K], M) = (1/|K|) sum_g Phi_e(g^-1) beta_M(g)`
over 2-regular `g`. For an element of order three on a module of dimension `d`,
`beta_M = a_0 - (d - a_0)/2`. Substituting (D3) gives the displayed identity.
The inequality holds because `Z` embeds `f_0 M` in `P_0 M` with left inverse
`L`. `square`

Corollary 3 is one-sided and strictly weaker than Corollary 2. The natural
module of a coordinate interpretation satisfies it with room to spare, yet
fails Corollary 2.

## 4. Scope, blindness of additive invariants, and what this subsumes

**The Leavitt unit group fuses the three classes.** All three classes are
conjugate in `Q`, by prefix permutations. An element acting by `G` on the two
children of a cone is conjugate to the one acting by `G^2`, by swapping the
children. Prefix permutations move any cone to any other. Swapping the
second and third letters under the cone `0` conjugates `diag(G, G)` on the
four leaves to `G` acting on the two children `00, 01`. Hence
`T0 ~ diag(G,G) ~ (G on the children of 0) ~ T1`, and likewise `T2`.

Consequently every 2-adic lifted Hattori--Stallings rank, at every conjugacy
class of `Q`, takes equal values on `f_0` and `P_0`: at the fused class the
weights sum to `2/3 - 1/3 - 1/3 = 0`. This agrees with `[f_0 S] = [P_0 S]` in
`K_0(S)`, which the half-corner construction forces anyway, since
`e = f + h = P + a v alpha` with `a v alpha ~ h`. Every additive invariant
factoring through `K_0(S)` is blind to the comparison. So is every rank decoder
which is approximately conjugation-invariant, because Corollary 3's
fixed-space densities of conjugate elements agree in such a decoder. Only
module-level or finite-image arguments can obstruct.

**What Corollary 2 excludes, uniformly and at every coefficient choice.** Any
actor family whose generated group has a finite coordinate interpretation in
which `K` acts through natural `F_4`-blocks plus trivial coordinates is dead. In
such an image `T0` moves two `F_4`-coordinates per natural block and `T1, T2`
move one. The fixed spaces differ, so they are not conjugate, and there is no
need to compute exterior powers. This covers the finite specializations of the
half-corner artifact: Section 10 (Jacobson one-pair specializations), Section 11
(packed Cuntz actors, image in `GL_3(F_4)`), Section 12 (literal two-pair
formula, image in `GL_5(F_4)`), and Section 14 (the creation-only
specializations `s -> 0`, whose images are constant finite matrix groups). In
Section 12 the recorded argument needed `Lambda^2` ranks; Corollary 2 needs
only fixed-space dimensions.

Theorem 1 is strictly more general than the Section 10 control. That control
needs one representation killing `f_0` but not `P_0`. Theorem 1 needs only
that the two induced projectives `f_0 F_2[F]` and `P_0 F_2[F]` are
non-isomorphic for some finite image `F`, and for this pair that is decided by
fusion alone.

**What it does not exclude.** The infinite boundary-module obstructions
(Sections 13, 15, 16 and the transporter notes) concern actor groups with no
finite image injective on `K`, and Corollary 2 is silent there. A finite image
in which `K` acts freely on points or on a regular module fuses all elements of
equal order and imposes nothing.

**Design constraint for a live comparison.** Every `K`-injective finite image
of the actor group must fuse `T0 ~ T1 ~ T2`. In `Q` that fusion is implemented by
depth-changing prefix permutations, which have no nontrivial finite images. A
successful comparison has to route the extra fixed mass of `T0` to `T1` and `T2`
through relations with no faithful finite shadow on the chart.
