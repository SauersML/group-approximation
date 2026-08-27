# Clifford hyperlinearity forces ambient flexible HS-instability

Date: 2026-08-13

## 1. Outcome

Let `Gamma<G` be the explicit residually finite Kazhdan infranormal pair
used in the Kun--Thom construction, let `X=G/Gamma`, and let
`E_Cl,0` be the perfect even Clifford cover from
`PERFECT_CORE_KUN_THOM_WREATH.md`. Its central involution is `z`.

There is a sharper stability implication than the one for the entire
Kun--Thom free-lamp group:

```text
E_Cl,0 hyperlinear
    ==> G is not flexibly normalized-Hilbert--Schmidt stable.       (CHI1)
```

Equivalently,

```text
G flexibly normalized-Hilbert--Schmidt stable
    ==> E_Cl,0 is an explicit finitely generated perfect
        nonhyperlinear group.                                      (CHI2)
```

Only the classical ambient group `G` is assumed stable in `(CHI2)`. No
stability of the Clifford cover, the free-lamp amalgam, or the nonsofic
wreath product is required.

This is a conditional nonhyperlinearity theorem, not a proof that `G` has
the required stability. Section 4 records a crucial normalization barrier:
known 2-Kazhdan results imply unnormalized Frobenius stability and therefore
do not discharge `(CHI2)` for arbitrary Connes-embedding microstates.

## 2. From group hyperlinearity to the canonical CAR trace

Assume that `E_Cl,0` is hyperlinear. Its canonical group trace is then a
Connes-embeddable character. Since `z` is a nonidentity group element of
order two, that character satisfies

```text
tau(z)=0,       tau((1-z)/2)=1/2.                     (CHI3)
```

Compressing to the central negative corner and normalizing gives a
Connes-embeddable character with `z=-1`. The character-rigidity theorem in
`PERFECT_CORE_KUN_THOM_WREATH.md`, Theorem 6, then identifies the resulting
lamp trace with the unique CAR trace. Tensoring with the regular character
of the residually finite retract `G` kills all nontrivial crossed-product
Fourier coefficients. Consequently the canonical trace on

```text
N_CAR=A_CAR crossed_product G                         (CHI4)
```

is Connes embeddable.

This step prevents a hypothetical hyperlinear embedding from escaping
through a noncanonical character or a vanishing negative central corner.
Proposition 4 of the same note identifies the full Clifford crossed product
as a crossed product of `(CHI4)` by the order-two automorphism implemented
by an odd Majorana. Its regular covariant representation embeds it into
`M_2(N_CAR)`. Hence Connes embeddability of `(CHI4)` also gives Connes
embeddability of

```text
M_Cl=Cl(X) crossed_product G.                          (CHI4a)
```

## 3. CAR microstates give the forbidden relative wall

Choose a strict compressor `t in G` and `gamma in Gamma` with

```text
t Gamma t^(-1)<=Gamma,
h=t^(-1) gamma t notin Gamma.                         (CHI5)
```

Let `o=Gamma in X`. In the full crossed product `(CHI4a)`, the root
Majorana `C_o`
obeys

```text
[C_o,u_s]=0                 (s in Gamma),
tau(C_o C_(h o))=0,
||C_o-u_h C_o u_h^*||_2=sqrt(2).                      (CHI6)
```

Take finite matrix lifts of a trace-preserving embedding of `(CHI4a)` into a
tracial matrix ultraproduct. After the standard polar and spectral
corrections, these give maps

```text
pi_n:G->U(d_n),       V_n in U(d_n),                  (CHI7)
```

such that

```text
||pi_n(gk)-pi_n(g)pi_n(k)||_(2,d_n)->0,
||[V_n,pi_n(s)]||_(2,d_n)->0       (s in Gamma),
lim_n ||[V_n,pi_n(h)]||_(2,d_n)=sqrt(2).              (CHI8)
```

The last equality follows from CAR covariance and orthogonality of distinct
Majoranas. Replacing the additive commutator by its group commutator does
not change its norm because all surrounding factors are unitary.

Equations `(CHI7)--(CHI8)` are exactly the relative-commutant wall in
`FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md`. Its Theorem 1
proves that such a wall is incompatible even with correction after adding
`o(d_n)` dimensions. Hence `G` is not flexibly normalized-HS stable. This
proves `(CHI1)` and `(CHI2)`.

The division of labor is exact:

1. central-corner character rigidity turns group hyperlinearity into the
   *canonical* CAR trace;
2. the CAR root supplies a positive-energy relative wall;
3. property `(T)` of `Gamma`, finite-dimensional commutant no-growth, and
   negligible-padding estimates forbid correcting that wall.

## 4. The 2-Kazhdan/Frobenius shortcut is invalid

It is tempting to combine `(CHI2)` with the cohomological criterion

```text
[T_2] ==> Frobenius stability                              (CHI9)
```

and then try to prove `[T_2]` for the ambient group. This does not prove the
hypothesis of `(CHI2)`.

The norms have different scales. For `A in M_d(C)`,

```text
||A||_F=sqrt(d) ||A||_(2,d).                           (CHI10)
```

Connes embeddability supplies only

```text
epsilon_n:=max_(g,k in F)
  ||pi_n(gk)-pi_n(g)pi_n(k)||_(2,d_n) -> 0.            (CHI11)
```

Frobenius stability applies only if the stronger profile

```text
sqrt(d_n) epsilon_n -> 0                               (CHI12)
```

holds. Nothing in a tracial matrix ultraproduct or in the central-corner
argument supplies `(CHI12)`. Passing to a subsequence does not solve this:
the dimensions may grow faster than the errors shrink. Repeating blocks
preserves normalized error and increases its unnormalized Frobenius size.

Therefore even a proof that

```text
H^2(N,W)^Q=0
```

for every unitary `G`-module in the Lyndon--Hochschild--Serre reduction from
`notes/NOTEPAD.md` would establish Frobenius stability, but would not by
itself contradict arbitrary CAR microstates. The earlier coefficientwise
`H^2` gate and `(CHI2)` are two different stability scales and must not be
silently identified.

Applying the adjoint representation does not repair the argument. Adjoint
multiplicativity is dimension-free in normalized Hilbert--Schmidt norm, but
the adjoint space has dimension `d_n^2`; its unnormalized Frobenius defect
still carries a growing dimension factor.

## 5. Exact remaining alternatives

The Clifford lane now has three honestly distinct possible completions.

1. Prove flexible **normalized**-HS stability of this explicit ambient `G`.
   Then `(CHI2)` gives an explicit nonhyperlinear group.
2. Prove the canonical CAR crossed-product trace Connes embeddable. Then
   the even Clifford cover is hyperlinear and nonsofic.
3. Produce only the finite relative wall `(CHI8)`. That already gives the
   radical-collision hyperlinear nonsofic quotient and simultaneously proves
   flexible normalized-HS instability of `G`.

The first and second outcomes point in opposite directions, and the third is
the finite-coordinate form of the second. What the present theorem adds is
a clean decision boundary on the *ambient* group and a proof that ordinary
2-Kazhdan/Frobenius stability lies on the wrong side of the normalization
firewall.

## 6. Formalization status

The algebraic Clifford phase extraction and radical-collision endpoint are
already kernel-checked in

```text
GroupApproximation/Sofic/CliffordPhaseExtraction.lean
GroupApproximation/Sofic/AntipodalRadicalCollision.lean
GroupApproximation/Sofic/RadicalSeparation.lean
```

The implication `(CHI1)` uses analytic notions not yet represented in the
Lean library: Connes-embeddable characters, normalized-HS matrix
ultraproducts, flexible stabilization, and the property-`(T)` correction
estimate. It should not be encoded as an axiom merely to claim a completed
formal proof. Once one of the three alternatives in Section 5 is actually
proved, these analytic interfaces must be formalized before declaring the
universal-hyperlinearity question Lean-closed.

## Primary references

* Alon Dogon, [*Flexible Hilbert--Schmidt stability versus hyperlinearity for
  property (T) groups*](https://arxiv.org/abs/2211.10492), arXiv:2211.10492.
* Uri Bader, Alexander Lubotzky, Roman Sauer, and Shmuel Weinberger,
  [*Stability and instability of lattices in semisimple
  groups*](https://arxiv.org/abs/2303.08943), arXiv:2303.08943.
