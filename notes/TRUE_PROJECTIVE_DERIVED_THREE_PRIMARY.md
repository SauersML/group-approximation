# The positive derived three-primary sector is uniformly local

Date: 2026-08-11

## Outcome

For every odd projective chart `X=P^2(F_p)`, the positive
stabilizer-homology terms in total degree two have dimension at most one in
characteristic three.  More precisely,

`E^1_(1,1)=0`,

`dim E^1_(0,2)=1` if `p=1 mod 3`, and `0` otherwise.          `(D3P1)`

The possible one-dimensional term is a single transitive coefficient orbit
with point stabilizer `C_3`; it is a fixed local template of bounded support.
All three-primary stabilizer homology is killed by `3`, so no higher-power
or growing-rank correction is hidden behind `(D3P1)`.

Consequently the positive derived three-primary sector cannot create a
chart-dependent normalized decoder cost.  The only growing derived-primary
problem is characteristic two.  The compact free harmonic lattice remains
a separate issue and may have its own discriminant at the prime three.

## 1. The edge term vanishes

The degree-one cell stabilizer is `D_8`.  Since `3` does not divide `8`,
averaging over `D_8` is defined over `F_3`; hence the invariants/coinvariants
functor is exact and

`H_s(D_8;F_3[X])=0` for every `s>0`.                          `(D3P2)`

The cellular orientation sign does not alter this conclusion.  Equation
`(D3P2)` proves `E^1_(1,1)=0` for every finite coefficient action, not just
the projective family.

## 2. The vertex term has one possible orbit

The vertex stabilizer is `S_4` in its fixed three-dimensional projective
representation.  Decompose `X` into transitive `S_4`-orbits.  Shapiro gives

`H_2(S_4;F_3[X]) ~= directSum_[x in S_4\X] H_2((S_4)_x;F_3)`. `(D3P3)`

The projective point stabilizers which occur are among

`1,C_2,C_3,C_4,V_4,S_3,D_8`.

All types except `C_3,S_3` have order prime to three and contribute zero to
`(D3P3)`.  For `S_3=C_3 semidirect C_2`, the
Lyndon--Hochschild--Serre sequence reduces positive homology to the
`C_2`-invariants in `H_*(C_3;F_3)`.  The nontrivial element acts by
inversion, hence by `-1` on `H_2(C_3;F_3)`, so

`H_2(S_3;F_3)=0`, while `H_2(C_3;F_3)=F_3`.                  `(D3P4)`

It remains only to count the `C_3` orbit.  A three-cycle has characteristic
polynomial

`(T-1)(T^2+T+1)`

in the projective representation.  Its two nontrivial eigenlines are
defined over `F_p` exactly when `p=1 mod 3`.  The normalizing involution
interchanges them, so together they form one `S_4`-orbit with stabilizer
exactly `C_3`.  The rational `1`-eigenline has stabilizer `S_3` and
contributes zero by `(D3P4)`.  This proves `(D3P1)`.

## 3. Metric consequence

The vertical splitting theorem in
`TRUE_VERTICAL_STABILIZER_DECODER_SPLITTING.md` supplies a fixed integral
boundary section on each transitive subgroup template.  The only surviving
three-primary template in `(D3P1)` is one `C_3` orbit, of size eight inside
the fixed `S_4` action.  Its chain representatives and every horizontal Wall
map involving it therefore have support and operator norm bounded by an
absolute constant.

Moreover positive homology of a finite stabilizer is killed by its order.
Since the three-part of every stabilizer order here is exactly `3`, the
integral three-primary correction has exponent three.  Thus `(D3P1)` is not
merely a bound on a mod-three shadow: it exhausts the possible positive
three-primary rank and gives a finite local decoder problem independent of
`p`.

## 4. Exact audit

The field-generic filtered analyzer
`experiments/sl3_projective_derived_e1.py` verifies the complete
characteristic-three filtration on the first five charts:

| `p` | `E^1_(0,2)` | `E^1_(1,1)` | `E^1_(2,0)` | `E^infinity_(0,2)` | full `H_2` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 0 | 0 | 0 | 0 | 0 |
| 5 | 0 | 0 | 0 | 0 | 0 |
| 7 | 1 | 0 | 4 | 1 | 1 |
| 11 | 0 | 0 | 10 | 0 | 0 |
| 13 | 1 | 0 | 16 | 1 | 1 |

The zero-row column `E^1_(2,0)` is shown only to distinguish it from the
positive terms; it is not claimed to vanish.  In the two cases with a
positive `C_3` class, all filtered differentials into that class have rank
zero, and the full mod-three `H_2` is precisely the one local class.  The
compact machine-readable table is
`experiments/projective-derived-mod3.tsv`, with SHA-256
`fe11d3790ff94240cc188187e8ebad1f6bc6794f93f6503350db1737ead2c31e`.
