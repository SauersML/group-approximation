# TRUE: exact projective cellular screening at prime-power level

## Purpose

The compact projective cellular calculations previously used the finite-field
projective plane at prime level.  The next cuspidal level in the
Ash--Yasaki list is `121=11^2`, so a finite-field substitution is no longer
valid: the coefficient set must be the projective plane over

```text
R = Z / p^k Z.
```

The exporter

```text
experiments/sl3_projective_cellular_prime_power_export.g
```

constructs that coefficient action directly over the local ring.  This note
records the exact model, its validation, and what the level-121 calculation
is meant to decide.

## 1. Canonical projective lines over a local ring

Let `R=Z/p^k Z`.  A row `v in R^d` represents a projective line precisely
when it is unimodular, equivalently when at least one coordinate is a unit.
Two such rows represent the same line when they differ by multiplication by
an element of `R^x`.

There is a canonical representative: scan the coordinates from left to
right, take the first unit coordinate, and rescale it to `1`.  This is
well-defined on projective classes because multiplying by a unit neither
changes the first unit position nor the normalized row.

The unit action on unimodular rows is free.  Hence

```text
|P^2(Z/p^k Z)|
  = (p^(3k)-p^(3(k-1))) / (p^k-p^(k-1))
  = p^(2(k-1)) (p^2+p+1).                         (PP1)
```

This count is enforced by the exporter rather than merely reported after the
fact.

## 2. The symmetric-square projective orbit

The HAP complex uses the six-dimensional symmetric-square representation of
`SL_3(Z)`.  Starting from the line of `e_1^2`, the exporter performs an exact
BFS orbit calculation modulo `p^k`, canonically normalizing after every
matrix action.

For odd `p`, the Veronese map from `P^2(R)` to this orbit is injective.  Indeed,
after normalizing a first unit coordinate of `v` to `1`, its diagonal square
coordinate is a unit and the associated mixed coordinates recover every
other coordinate of `v`; the possible factor `2` is a unit because `p` is
odd.  Transitivity of `SL_3(R)` on unimodular rows gives surjectivity.  Thus
the orbit has exactly the cardinality in (PP1).

For every coefficient element appearing in a stabilizer or cellular
boundary, the script computes its permutation of this exact orbit.  A missing
image, repeated image, nonunimodular row, or incorrect orbit cardinality is a
hard error.

## 3. Exact validations

### Prime-level byte comparison

At level `3`, the new local-ring exporter and the previous finite-field
exporter produce byte-for-byte identical boundary files.  Their common
SHA-256 digest is

```text
c29d49368cf799a685f8032d156cdce092fac72f6b87792606c40ccb773dc9e8.
```

This checks action orientation, inverse conventions, stabilizer signs,
boundary ordering, and serialization simultaneously.

### First genuinely nonfield level

At level `9`, formula (PP1) gives

```text
|P^2(Z/9Z)| = 3^2(3^2+3+1) = 117.
```

The exported rational complex has

```text
Q^11 <- Q^16 <- Q^9 <- Q^4,
rank(d1)=10, rank(d2)=6, rank(d3)=3,
d1 d2 = 0, d2 d3 = 0.
```

Consequently

```text
H_0 = Q,  H_1 = 0,  H_2 = 0,  H_3 = Q.           (PP2)
```

The exact summary certificate is

```text
experiments/projective-cellular-n9-summary.json
SHA-256 1a81d7c70b6477ab4c0cfeba0ebd0f4e1f3cf08c8f94aca0e42b3871cdb74ae2.
```

Thus the new path has been checked both against the old implementation where
the latter applies and on a true prime-power ring where it does not.

### Square-level Eisenstein calibration

The boundary/cuspidal split in
`TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md` motivated two further exact
small square-level runs.

At level `25`, the rational complex has dimensions and ranks

```text
Q^45 <- Q^100 <- Q^80 <- Q^28,
rank(d1)=44, rank(d2)=56, rank(d3)=24,
```

so its homology is `(1,0,0,4)`. At level `49`,

```text
Q^139 <- Q^356 <- Q^320 <- Q^110,
rank(d1)=138, rank(d2)=218, rank(d3)=101,
```

so its homology is `(1,0,1,9)`. All consecutive boundary products vanish
exactly. The rank-one level-`49` harmonic lattice is the first nonzero
noncuspidal square-level `H_2` in this calibration. Its shortest nonintegral
`Q^#` class has norm `0.335966093411573...>1/sqrt(28)`, so it is above the
spherical threshold.

Together with level `9` and level `121`, the exact Eisenstein dimensions at
square levels `p^2`, `p=3,5,7,11`, are `0,0,1,5`. They match

```text
dim S_2(Gamma_0(p^2))-dim S_2(Gamma_0(p)),
```

and this is now proved for every odd prime. In fact,

```text
dim H_Eis^2(Gamma_0(p^2,3))
 = dim S_3(Gamma_1(p))
 = dim S_2(Gamma_0(p^2))-dim S_2(Gamma_0(p)).
```

The two middle maximal faces supply the two copies of
`S_3(Gamma_1(p))` in boundary degree two; the Eisenstein image is the graph
of their constant-term intertwiner. See
`TRUE_SQUARE_LEVEL_EISENSTEIN_GRAPH.md`. The computational certificates are

```text
experiments/projective-cellular-n25-summary.json
SHA-256 597a70d2aafb8f2175988612a029d3c973c7b11ee1b68f3fa8d1869a62bfb1b3,

experiments/projective-cellular-n49-summary.json
SHA-256 3c3727e4df6d0ce2018ece91670e782879b2b5568942d57223b900598a3ffadc.
```

### Exact lower-level control for `121`

The reduction target of the level-`121` chart is level `11`.  Exact analysis
at that level gives

```text
Q^11 <- Q^18 <- Q^10 <- Q^4,
rank(d1)=10, rank(d2)=8, rank(d3)=2,
H_2=0.                                                    (PP2a)
```

Both consecutive boundary products vanish exactly.  Therefore any nonzero
harmonic plane at level `121` is genuinely new; it cannot be the ordinary
pullback of a lower-level harmonic class.  The exact control certificate is

```text
experiments/projective-cellular-n11-summary.json
SHA-256 f41d32c4f086c0a8bb59fefc170e4ba41213998aad27b4c594f7f640ebae2590.
```

This run also exposed and fixed an analyzer edge case: when `H_2=0`, a
requested lift output must remain null instead of entering the binary
harmonic Gram reducer.

## 4. The level-121 screen

The batch driver

```text
experiments/msi_sl3_projective_prime_power_screen.sbatch
```

first exports the exact local-ring complex and then invokes the same rational
homology, integral harmonic lattice, and paired-discriminant analyzer used at
prime level.

For `121=11^2`, the export has already certified

```text
|P^2(Z/121Z)| = 11^2(11^2+11+1) = 16093.         (PP3)
```

The exact signed-coinvariant dimensions are

```text
Q^721 <- Q^2028 <- Q^1940 <- Q^654,                       (PP3a)
```

whose Euler characteristic is `-21`.  Reduction of these same integral
boundary matrices over each of `F_101`, `F_1009`, and `F_10007` gives ranks

```text
(rank(d1),rank(d2),rank(d3))=(720,1308,625),              (PP3b)
```

so the modular homology dimensions are `(1,0,7,29)` in all three fields.
This already gives the rational upper bounds `dim H_1=0`, `dim H_2<=7`, and
`dim H_3<=29`.  Ash--Yasaki independently compute
`dim H^3(Gamma_0(121),Q)=29` in their detailed level-121 example
([Section 12.4](https://arxiv.org/html/2107.10918#S12.SS4)).  Thus the upper bound in
degree three is sharp.  Euler characteristic then forces

```text
dim_Q H_2(Gamma_0(121);Q)=7.                             (PP3c)
```

The two-dimensional cuspidal packet is therefore not the entire dangerous
space: five additional rational directions occur at this composite level.
The exact modular certificate is

```text
experiments/projective-cellular-n121-modular-screen.json
SHA-256 58b7e3fae6ec5fc1c4c7b7d4095f35331919f4622a794c4a5f8a2482f0384fa8.
```

This is precisely why the rank-independent systole screen must precede an
ambient section computation.

The rank-independent implementation is

```text
experiments/sl3_projective_cellular_systole.py.
```

It reconstructs `Q^#` from exact cycle pairings, clears denominators, and
uses exact integer shortest-vector reduction.  As a regression test, its
level-`79` output reproduces the previously certified discriminant group,
the exact shortest squared norm

```text
10728712947256347312769663474250046223588321991244287411579243217706716447682408124247043381061430739101610963804926581168798385712509031664221661233926942927648326947018265651270215509953939044890
/
85972262746423736417259155028330220464981880775136938484153009367340055879270507706557239067951479601089455324716561313521323488223939657898054379190757733582342373522062836858431172996132966638507
```

and `delta_79=0.3532601379363844...`.  In particular it again certifies
`28 delta_79^2>1`.  The standalone regression certificate is

```text
experiments/projective-cellular-p79-systole-generic.json
SHA-256 18683a12a3010c354ab4e5e16ca5ad2ebbdf4c01af5bc04c19244cdcc3c20be9.
```

This validates the arbitrary-rank path before applying it to the new
rank-seven level-`121` harmonic lattice.

The harmonic exporter now uses an arbitrary integral basis spanning the
rational harmonic space; `TRUE_QSHARP_SPAN_BASIS_REDUCTION.md` proves that
primitivity is unnecessary for reconstructing the physical `Q^#`, detecting
integral classes, or computing their orders.  At level `79`, the combined
span export and exact systole screen completed in `36` seconds and reproduced
every decisive field of the primitive-basis certificate exactly.  This
removes the full ambient HNF before the rank-seven level-`121` screen.

The decisive output is not merely the size of a selected modular lift.  If
the harmonic lattice is nonzero, compute its compact dual systole `delta_121`
and the spherical template bound `B_121`.  The harmonic plane is relevant to
the localized TRUE gate only when

```text
B_121 delta_121 < 1.                              (PP4)
```

If (PP4) fails, every localized harmonic maximum in the HIL22 reduction is
trivial, just as at prime levels `61`, `79`, and `89`.  If (PP4) holds, level
`121` becomes the next dangerous chart and warrants an exact compact CVP
calculation of its paired-discriminant repair constant.

## 5. Exact level-121 outcome

The rank-seven span export and exact `Q^#` systole computation completed on
one MSI core in `5m16s`.  The harmonic system has dimensions

```text
2682 x 1940,
```

the exported basis has rank seven, and its exact harmonic residual is zero.
The span-basis reconstruction gives

```text
rank(K)=632,
delta_121 = lambda_1(Q^#) = 0.45320230767323166... .   (PP5)
```

The shortest vector is nonintegral.  Its discriminant-class order is the
same explicit common denominator recorded in the certificate, but its norm
is already too large to participate in the localized obstruction.  The
chartwise spherical template bound is `B_121^2=12`, and exact rational
comparison gives

```text
12 delta_121^2 > 1.                                  (PP6)
```

Consequently

```text
every nonzero vector of Q^# lies above the spherical threshold. (PP7)
```

Thus the first composite projective chart is **safe**.  Its seven new
rational harmonic directions do not require a paired CVP/decoder
calculation.  This is materially stronger than merely lifting selected
mod-`2^k` classes: it eliminates the entire rational harmonic space at once.

The exact certificates are

```text
experiments/projective-cellular-n121-harmonic-span.json
SHA-256 90fccdd4c83c3812cecae3dadf8076aadc6cfaa23159dede4853593ac8b0e3eb,

experiments/projective-cellular-n121-systole-span.json
SHA-256 f9b5733277ba8c942710d6f24cf5407895478e13aa71d5014cbd28475a0c51b3.
```

The conclusion is chart-specific, not yet a uniform theorem over all prime
powers.  Together with the prime-level screen it leaves level `53` as the
only presently known subthreshold projective chart below `100`.

Independently of the chart-specific value, the fixed cellular attaching word
gives the uniform bound `B_level^2<=52` at every level; see
`TRUE_UNIFORM_PROJECTIVE_SPHERICAL_BOUND.md`.  Thus
`delta_level>=1/sqrt(52)` is already a chart-independent sufficient safety
certificate.

## 6. Scope

This closes a computational-model gap: composite projective levels can now be
screened without pretending that `Z/p^k Z` is a field.  It does not prove the
uniform family theorem.  The remaining TRUE statement is still a uniform
bound for the paired integral repair of every subthreshold harmonic class,
together with the already-separated nonsmall spherical decoder and the final
character-transfer argument.
