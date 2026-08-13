# Square-level Eisenstein cohomology is a weight-three scattering graph

Date: 2026-08-12

## Outcome

Let

```text
Gamma=Gamma_0(p^2,3) < SL_3(Z)
```

for an odd prime `p`, and let `M` be its rational Borel--Serre quotient.  Put

```text
E^2(Gamma)=im(H^2(M;Q)->H^2(partial M;Q)).                 (SEG1)
```

Then

```text
dim_Q E^2(Gamma)
  = dim_C S_3(Gamma_1(p))
  = dim_C S_2(Gamma_0(p^2))-dim_C S_2(Gamma_0(p)).         (SEG2)
```

For `p>=5`, all three terms equal

```text
(p-1)(p-5)/12.                                            (SEG3)
```

For `p=3`, they are zero.

There is a stronger structural statement over `C`.  The whole degree-two
boundary cusp sector consists of the two middle maximal-parabolic faces,
one of each type:

```text
H^2(partial M;C)
  ~= S_3(Gamma_1(p)) (+) S_3(Gamma_1(p)).                  (SEG4)
```

Under this identification, the Eisenstein image is a scattering graph

```text
E^2(Gamma)_C
  = {phi (+) C_p^*(0) phi : phi in S_3(Gamma_1(p))}.       (SEG5)
```

Here `C_p^*(0)` is the constant-term intertwining operator between the two
associate maximal parabolics.  Thus the square-level boundary problem is
not an arbitrary growing-rank packet problem.  It is one modular-curve
lattice together with one intertwining operator.

This proves the square-level dimension formula previously recorded as a
four-level conjecture at `p=3,5,7,11`.

## 1. Lee--Schwermer's exact boundary module

Take the principal congruence subgroup `Gamma(p^2)` inside `Gamma`.  It is
torsion-free because `p^2>=3`.  Write

```text
G_p=SL_3(Z/p^2 Z),
P_1,P_2 < G_p
```

for the two standard maximal-parabolic subgroups.  Lee--Schwermer,
Theorem 2.4(3), give the following exact `G_p`-module decomposition:

```text
H^2(partial M(p^2);C)
 ~= (+)_(i=1,2) Ind_(P_i)^(G_p)
       H_cusp^1(Gamma(p^2,2);E_0)
    (+) (+)_(i=1,2)
       (Ind_(P_i)^(G_p) epsilon_i
        (+) Ind_(P_i)^(G_p) epsilon_i).                   (SEG6)
```

The coefficient `E_0` is the standard two-dimensional representation of
`SL_2`, and `epsilon_i` is the nontrivial component character of the
extended Levi.  Lee--Schwermer explicitly say immediately after the theorem
that boundary cohomology for a containing congruence subgroup is obtained
by taking finite-quotient invariants.

Let

```text
K=Gamma/Gamma(p^2) < G_p.
```

The rational boundary cohomology of `Gamma` is therefore the `K`-fixed part
of `(SEG6)`.  Mackey decomposition and Frobenius reciprocity turn the fixed
part of each induced module into a direct sum over `K\G_p/P_i`, equivalently
over the `Gamma`-orbits of maximal parabolics of type `i`.  Each summand is
the fixed part under the corresponding extended Levi stabilizer.

## 2. The six maximal faces at square level

Ash--Yasaki determine both the orbits and their Levi groups.  Maximal faces
of either type are indexed by divisors `d|N`.  If

```text
Delta=gcd(d,N/d),
Gamma_1(A,Delta)^*
  ={[a b; c D] in GL_2(Z):
      c=0 mod A, a=det mod Delta},                         (SEG7)
```

then the line-face Levi at `d` is
`Gamma_1(N/d,Delta)^*`, while the plane-face Levi is the transpose of
`Gamma_1(d,Delta)^*`.

At `N=p^2`, the determinant-one parts, in order `d=1,p,p^2`, are

```text
line type:   Gamma_0(p^2), Gamma_1(p), SL_2(Z),
plane type:  SL_2(Z), Gamma^1(p), Gamma_0(p^2),             (SEG8)
```

where `Gamma^1(p)` is conjugate to `Gamma_1(p)`.

Every extended group in `(SEG7)` contains `diag(-1,1)`.  The character
`epsilon_i` is the determinant/component character on that extended Levi,
so this element acts by `-1`.  Consequently every fixed space coming from
the four sign-induced terms in `(SEG6)` is zero.

For an extended Levi `Lambda^*`, let

```text
Lambda^+=Lambda^* intersect SL_2(Z).
```

Eichler--Shimura with the standard coefficient gives

```text
H_cusp^1(Lambda^+;E_0)
  ~= S_3(Lambda^+) (+) conjugate(S_3(Lambda^+)).            (SEG9)
```

Any determinant-negative element of `Lambda^*` interchanges the two Hodge
summands.  Hence the `Lambda^*/Lambda^+`-fixed space has dimension
`dim_C S_3(Lambda^+)` and is naturally a graph between the two summands.

Odd-weight forms for `Gamma_0(p^2)` and `SL_2(Z)` vanish because both groups
contain `-I`.  Therefore only the middle divisor `d=p` survives in each
parabolic type.  Equations `(SEG6)`--`(SEG9)` prove

```text
dim_C H^2(partial M;C)=2 dim_C S_3(Gamma_1(p)),             (SEG10)
```

as well as `(SEG4)`.

## 3. The Eisenstein image is exactly half

The boundary intersection theorem in
`TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md` proves that

```text
E^2(Gamma) subset H^2(partial M;Q)
```

is Lagrangian.  Thus `(SEG10)` immediately gives

```text
dim_Q E^2(Gamma)=dim_C S_3(Gamma_1(p)).                    (SEG11)
```

Lee--Schwermer give more.  In Section 6.1, equation (9), they identify the
degree-two maximal-parabolic restriction image as

```text
{phi (+) C^*(0)phi}.                                       (SEG12)
```

Taking `K`-invariants and using the vanishing of every face except the two
middle faces turns `(SEG12)` into `(SEG5)`.  In particular, projection of
the Eisenstein image to either middle face is an isomorphism.

## 4. The classical dimension identity

It remains to evaluate `dim S_3(Gamma_1(p))`.  For `p>=5`, the image of
`Gamma_1(p)` in `PSL_2(Z)` is torsion-free, has index

```text
mu_1=(p^2-1)/2,
```

has `p-1` cusps, and its compactified modular curve has genus

```text
g_1=(p-5)(p-7)/24.                                         (SEG13)
```

The standard Riemann--Roch dimension formula for weight three on a
torsion-free modular curve gives

```text
dim_C S_3(Gamma_1(p))
  =2(g_1-1)+(p-1)/2
  =(p-1)(p-5)/12.                                          (SEG14)
```

On the other hand, the genus formula for `X_0(n)` is

```text
g_0(n)=1+mu_0(n)/12-e_2(n)/4-e_3(n)/3-c_0(n)/2.            (SEG15)
```

At `n=p` and `p^2`,

```text
mu_0(p)=p+1,       mu_0(p^2)=p(p+1),
c_0(p)=2,          c_0(p^2)=p+1.                           (SEG16)
```

For `p>=5`, the elliptic-point counts at `p` and `p^2` agree: solutions of
the relevant quadratic congruences lift uniquely from `p` to `p^2`.
Subtracting `(SEG15)` therefore yields

```text
g_0(p^2)-g_0(p)
  =(p^2-1)/12-(p-1)/2
  =(p-1)(p-5)/12.                                          (SEG17)
```

Equations `(SEG14)` and `(SEG17)` prove `(SEG2)` for `p>=5`.  Directly,
`S_3(Gamma_1(3))=0` and `g_0(9)=g_0(3)=0`, proving the remaining case.

## 5. Consequence for the TRUE program

The square-level free boundary sector is now completely localized:

```text
one integral modular-symbol lattice for S_3(Gamma_1(p))
                 +
one scattering/intertwining graph C_p^*(0).                (SEG18)
```

The large absolute harmonic rank at square level is therefore not caused by
unstructured incidence among all maximal and minimal faces.  Four of the six
maximal faces contribute nothing in degree two, all generalized-Steinberg
sign pieces vanish, and the remaining two faces are paired by one graph.

The next family theorem should not ask for arbitrary Eisenstein packets.
It should do two explicit things:

1. build bounded integral packets for the weight-three modular-symbol lattice
   of `Gamma_1(p)`;
2. bound the denominator and metric distortion of the integral graph of
   `C_p^*(0)`.

Over `C`, the graph description already controls dimension and projection.
The unresolved difficulty is arithmetic: the rational/integral lattice of
the constant-term operator, exactly the sort of paired-discriminant gluing
that circle repair detects.

## Sources

- Ronnie Lee and Joachim Schwermer,
  [*Cohomology of arithmetic subgroups of SL3 at infinity*](https://doi.org/10.1515/crll.1982.330.100),
  Theorem 2.4(3), its following remark, and Section 6.1 equation (9).
- Avner Ash and Dan Yasaki,
  [*Cohomology of congruence subgroups of SL3(Z), Steinberg modules, and real quadratic fields*](https://arxiv.org/abs/2107.10918),
  Section 6, especially the line- and plane-stabilizer lemmas.

