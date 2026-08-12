# Absolute projective H2 has an interior quotient and a boundary kernel

Date: 2026-08-12

## Outcome

The absolute projective `H_2` lattice is not, in general, the same object as
the cuspidal modular-symbol lattice. Rationally it has a canonical short
exact sequence

```text
0 -> B_Gamma -> H_2(Gamma;Q) -> H_cusp^3(Gamma;Q) -> 0,       (AHB1)
```

where, for the Borel--Serre compactification `Ybar_Gamma`,

```text
B_Gamma = coker(H^2(Ybar_Gamma;Q)
                 -> H^2(partial Ybar_Gamma;Q)).               (AHB2)
```

Thus unimodular modular symbols control the interior/cuspidal quotient in
`(AHB1)`, but they do not see the boundary kernel `B_Gamma`.

At projective level `121`, the two sides are now known exactly:

```text
dim_Q H_2(Gamma_0(121);Q)       = 7,
dim_Q H_cusp^3(Gamma_0(121);Q)  = 2,
dim_Q B_Gamma                   = 5.                           (AHB3)
```

Consequently, the seven-dimensional harmonic space found in the projective
cellular computation consists of five boundary-kernel directions and only
two interior/cuspidal directions. This is the first computed chart where the
boundary kernel is load-bearing. At the prime cuspidal levels `53,61,79,89`,
both the absolute `H_2` rank and the cuspidal dimension are two, so
`B_Gamma=0` rationally there.

The corrected family target therefore has three pieces:

1. bounded cuspidal closing for unimodular modular symbols;
2. bounded packets for the Borel--Serre boundary kernel;
3. bounded integral and metric gluing of those two filtrands.

The rational exact sequence alone supplies no uniform integral or metric
splitting.

The boundary kernel has since been identified more sharply: the middle
boundary intersection pairing canonically identifies it with the dual of
the degree-two Eisenstein restriction image. See
`TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md`.

## 1. The pair sequence

Work over `Q`, and include the orientation local system when required by the
chosen left/right quotient convention. The cohomology sequence of the pair
`(Ybar_Gamma,partial Ybar_Gamma)` contains

```text
H^2(Ybar_Gamma)
  --res--> H^2(partial Ybar_Gamma)
  --delta--> H^3(Ybar_Gamma,partial Ybar_Gamma)
  --j_!--> H^3(Ybar_Gamma)
  --res--> H^3(partial Ybar_Gamma).                            (AHB4)
```

Lee--Schwermer's boundary theorem, in the form quoted by Ash--Yasaki, says
that the last restriction map is surjective and that its kernel is the
interior cohomology, which in this degree equals cuspidal cohomology:

```text
ker(H^3(Ybar_Gamma)->H^3(partial Ybar_Gamma))
  = H_!^3(Gamma;Q)
  = H_cusp^3(Gamma;Q).                                       (AHB5)
```

Exactness of `(AHB4)` therefore gives

```text
0 -> coker(res:H^2(Ybar_Gamma)->H^2(partial Ybar_Gamma))
  -> H^3(Ybar_Gamma,partial Ybar_Gamma)
  -> H_cusp^3(Gamma;Q)
  -> 0.                                                       (AHB6)
```

The locally symmetric space has real dimension five. Lefschetz duality
identifies

```text
H^3(Ybar_Gamma,partial Ybar_Gamma;Q)
  ~= H_2(Ybar_Gamma;Q)
  ~= H_2(Gamma;Q),                                            (AHB7)
```

rationally (and with the same orientation convention). Substituting
`(AHB7)` into `(AHB6)` proves `(AHB1)`.

There is no assertion here that `(AHB1)` splits canonically, integrally, or
with bounded norm. Precisely those stronger properties matter for circle
repair.

## 2. What modular symbols see

The homology sequence of the same pair contains

```text
H_2(partial Ybar_Gamma)
  -> H_2(Ybar_Gamma)
  --j--> H_2(Ybar_Gamma,partial Ybar_Gamma)
  -> H_1(partial Ybar_Gamma).                                 (AHB8)
```

Hence

```text
ker(j)=im(H_2(partial Ybar_Gamma)->H_2(Ybar_Gamma)).           (AHB9)
```

For `SL_3`, the Steinberg/modular-symbol group identifies with the relative
target (equivalently, by duality, with top-degree cohomology):

```text
H_0(Gamma,St(Q^3)) ~= H^3(Gamma;Q)
                    ~= H_2(Ybar_Gamma,partial Ybar_Gamma;Q).  (AHB10)
```

Ash--Rudolph says that unimodular symbols generate this relative object.
Absolute classes enter it through `j`. They can therefore describe the
cuspidal image of `(AHB1)`, but the absolute classes in `(AHB9)` map to zero
and are invisible to every relative modular symbol.

This corrects the earlier shorthand “the absolute lattice is the closing
kernel inside modular symbols.” That description applies to the image of
absolute homology. It omits the boundary kernel of the absolute-to-relative
map.

## 3. The exact level-121 consequence

The exported projective cellular complex proves

```text
dim_Q H_2(Gamma_0(121);Q)=7.                                  (AHB11)
```

Ash--Yasaki compute

```text
dim_Q H_cusp^3(Gamma_0(121);Q)=2.                             (AHB12)
```

and independently decompose the full degree-three cohomology at level `121`
as dimensions `14+2+13=29` (maximal-boundary, cuspidal, and the remaining
boundary contribution in their notation). Taking dimensions in `(AHB1)`
now gives

```text
dim_Q B_Gamma = 7-2 = 5.                                     (AHB13)
```

This explains why level `121` acquired seven harmonic directions although
the cuspidal contribution remained two-dimensional. The five extra
directions are not additional cuspidal packets awaiting a modular-symbol
description; they are boundary-kernel classes.

## 4. Corrected theorem-shaped target

Let `K_cusp,X` denote the absolute quotient detected in relative modular
symbols and let `K_bdry,X` denote the boundary kernel in `(AHB1)`. A family
proof of the harmonic systole bound needs uniformly bounded real spanning
packets for both pieces:

```text
K_cusp,X tensor R is spanned by bounded unimodular-symbol closings,
K_bdry,X tensor R is spanned by bounded boundary-stratum packets. (AHB14)
```

The second line should be attacked in the Borel--Serre boundary complex,
through maximal-parabolic faces and their intersections. It is a different
finite-combinatorial problem from cuspidal closing.

Equivalently, by middle-dimensional boundary duality, this line asks for
bounded packets in degree-two Eisenstein cohomology. That reformulation is
canonical and is the preferred target.

For circle repair one additionally needs a bounded integral/metric gluing
theorem for the extension

```text
0 -> K_bdry,X -> H_2(X;Z)/torsion -> K_cusp,X -> 0,            (AHB15)
```

after replacing the right term by its actual integral image. Rational
bounded packets on the two associated graded pieces do not by themselves
bound the integral extension class or a section norm.

The immediate computational follow-up is also sharper: classify the seven
level-`121` primal packets by their images under the absolute-to-relative
map. Exactly two independent images and five kernel packets must occur.
Their supports should reveal separate cuspidal-closing and boundary-stratum
templates rather than one undifferentiated rank-seven pattern.

## Sources

- Avner Ash and Dan Yasaki,
  [*Cohomology of congruence subgroups of SL(3,Z)*](https://arxiv.org/abs/2107.10918),
  especially Theorem 2.9, Section 7, and the level-`121` computations in
  Sections 12.2 and 12.4.
- Lee--Schwermer's boundary restriction theorem, quoted and used in Section
  7 of Ash--Yasaki.
- Avner Ash and Lee Rudolph,
  *The modular symbol and continued fractions in higher dimensions*,
  Inventiones Mathematicae 55 (1979), 241--250.
