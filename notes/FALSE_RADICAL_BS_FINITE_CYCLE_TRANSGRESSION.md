# The fold-aligned paired class survives exactly on p-divisible cycles

Date: 2026-08-11

## 1. Outcome

The natural finite coefficient-ring quotients do retain the **fold-aligned**
paired class from `FALSE_RADICAL_BS_PAIRED_KUN_THOM_DOUBLE.md`, provided the
external substitution transvection has order divisible by `p`.

More precisely, on the finite coset set the marked translation `h` acts
trivially and the stable letter `c` acts in cycles of one common length
`M`.  For each orbit, the stabilizer map

`H_2(U semidirect MZ,F_p)->H_2(BS(1,p+1),F_p)`         `(FCT1)`

is multiplication by `M`.  Consequently the augmentation connecting map
on the explicit paired class is nonzero exactly when

`p divides M`.                                        `(FCT2)`

For the quotient `L->SL_d(Z/MZ)` and
`s=I+e_13`, the order of `s` is exactly `M`.  Thus moduli coprime to `p`
are provably sterile, while every `p`-divisible modulus preserves the
algebraic transgression.

This does not yet prove positive normalized Hilbert--Schmidt mass.  It
reduces that analytic problem to the metric of a disjoint union of explicit
length-`M` cyclic incidence complexes.

## 2. The finite coset action

Retain

`Gamma=E_r(R_+) semidirect Q`,
`G=E_r(R) semidirect (Q times L)`                      `(FCT3)`

and the fold-aligned subgroup

`B=<h,c> ~= BS(1,q)`, `q=p+1`,
`c=(c_0,s)`, `s=I+e_13 in L`.                         `(FCT4)`

In every finite coefficient-ring quotient, positive and Laurent ring
images coincide by `(FRQ4)`.  The image of `Gamma` is therefore normal and
the finite coset set is a quotient of the external `L` image.  The element
`h` belongs to the normal closure of `Gamma`, so it acts trivially.  The
element `c` acts through `s`.

Let `X` be one transitive `B`-orbit and suppose `s` has order `M` on it.
Then

`X ~= B/S_M`,
`S_M=nu^(-1)(MZ)=U semidirect MZ`,                    `(FCT5)`

where `U=ker(nu)=Z[1/q]`.  Equivalently,

`S_M ~= BS(1,q^M)`.                                   `(FCT6)`

## 3. The stabilizer map is multiplication by M

The Lyndon--Hochschild--Serre sequence for

`1->U->B->Z->1`                                       `(FCT7)`

identifies the mod-`p` degree-two class with

`H_2(B,F_p) ~= H_1(Z,H_1(U,F_p)) ~= F_p`.             `(FCT8)`

Indeed `H_1(U,F_p)=F_p`, and conjugation by `c` acts as multiplication by
`q=1 mod p`, hence trivially.  The same calculation for `(FCT5)` gives

`H_2(S_M,F_p) ~= H_1(MZ,F_p) ~= F_p`.                 `(FCT9)`

Under these identifications, inclusion `MZ<=Z` sends its degree-one
generator to `M` times the generator of `Z`.  Naturality of the spectral
sequence therefore gives

`H_2(S_M,F_p)->H_2(B,F_p): z |-> M z`.                `(FCT10)`

This also follows from the degree-`M` cyclic cover of the aspherical
Baumslag--Solitar presentation complex.

Now use Shapiro in the augmentation sequence

`0->I_X->F_p[X]->F_p->0`.                             `(FCT11)`

The relevant exact segment is

`H_2(S_M,F_p)->H_2(B,F_p)->H_1(B,I_X)`.               `(FCT12)`

Equations `(FCT10)--(FCT12)` prove:

**Theorem 1 (finite-cycle transgression dichotomy).**  The connecting map
in `(FCT12)` is zero if `p` does not divide `M` and injective if `p`
divides `M`.  In the latter case it retains the explicit generator
`[Z_p]` from `(RB18)`.

For a disjoint union of `M`-cycles, the first map in the global Shapiro
sum is a sum of copies of multiplication by `M`.  The same dichotomy holds
for the full finite coset set.

## 4. An exact chain representative

The dichotomy has a sparse chain-level form useful for computation.  Use
right-module conventions

`partial(m[g|k])=m g[k]-m[gk]+m[g]`.                  `(FCT13)`

Let `e_x` be one basis point of an `M`-cycle.  Since `h` acts trivially and
`q=1 mod p`, taking the boundary of `e_x Z_p` gives the `I_X`-valued
one-cycle

`(e_x-e_(xc))([h]+[c^(-1)])`
` +(e_(xc^(-1))-e_x)[c]`.                             `(FCT14)`

Thus every coefficient is one edge of the cyclic incidence operator

`D_M=1-S_M`.                                          `(FCT15)`

Formula `(FCT14)` verifies directly that the finite model has bounded
local support.  The global obstruction when `p|M` is not a high-degree
relator: it is the failure to integrate this cyclic derivative compatibly
around a cycle whose length is zero in `F_p`.

## 5. The natural quotient family

In `SL_d(Z/MZ)`, the transvection `s=I+e_13` satisfies

`s^k=I+k e_13`.                                       `(FCT16)`

Hence its order is exactly `M`, and right multiplication by `s` on the
finite group is a disjoint union of cycles of length `M`.  Theorem 1 now
gives an exact parameter rule:

* if `gcd(M,p)=1`, the paired class is absorbed by every orbit stabilizer;
* if `p|M`, every orbit stabilizer map in degree two is zero and the global
  augmentation transgression is nonzero.

There is therefore no reason to sweep primes or arbitrary exponent moduli.
Fix the odd prime `p` from the construction and use a tower

`M=p, p^2, p^3, ...`                                  `(FCT17)`

or any growing `p`-divisible sequence.

## 6. Remaining quantitative calculation

Nonzero finite-dimensional homology is qualitative.  A FALSE proof still
requires a sequence of phase representatives for `(FCT14)` such that

1. normalized relator carry tends to zero; and
2. the fold word `w=i_2(h)i_1(h)^(-1)` retains positive normalized chordal
   energy.

All orbit blocks are now identical cycles.  The next computation should
form the exact carry and marked-word matrices on one length-`M` block,
diagonalize them by the discrete Fourier transform, and determine the best
joint low-carry/high-word ratio as `M=p^k` grows.  No ambient elementary
matrix, character-table, or generic unitary optimization is needed for
this first analytic audit.
