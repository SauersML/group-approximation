# Locally finite commutants recover, but at shifted scales

Date: 2026-08-14

## 1. Outcome

The increasing finite unitriangular envelopes do permit coordinate recovery
of individual commutant elements. No Kazhdan centralizer theorem is needed
for that statement. If

```text
K_1 <= K_2 <= ...,
K=union_m K_m                                             (LFC1)
```

is a countable locally finite group represented in a tracial matrix
ultraproduct, then every finite family in `pi(K)'` can, after a sufficiently
slow diagonal choice `m=m(n)->infinity`, be lifted within vanishing
Hilbert--Schmidt distance of the exact coordinate commutants

```text
rho_n(K_(m(n)))'.                                        (LFC2)
```

The proof is only finite-group exactification followed by Reynolds
averaging. This gives the locally finite analogue of the elementwise part of
Alekseev--Thom Open Problem 6.2.

It still does not close the compressor argument. If `alpha(K)<K` is a
proper endomorphism, a finite exhaustion generally satisfies only

```text
alpha(K_m) <= K_(r(m)),       r(m)>m.                   (LFC3)
```

The coordinate relations then have the form

```text
C_(r(m)) <= D_m,
D_m=U C_m U*,                                           (LFC4)
```

not `C_m<=D_m=UC_mU*`. Dimension counting does not compare an algebra with
a conjugate of itself. For the unilateral binary shift, the missing scale
has an exact factor-two commutant-dimension defect. Thus the remaining gate
is a genuine **scale-synchronization/index theorem**, not separate
commutant recovery.

## 2. Finite Reynolds recovery

Let `F` be finite, let

```text
rho:F -> U(M_d)                                          (LFC5)
```

be an exact representation, and put

```text
E_F(X)=(1/|F|) sum_(g in F) rho(g)Xrho(g)*.             (LFC6)
```

This is the Hilbert--Schmidt orthogonal projection onto `rho(F)'`. The exact
mean-displacement identity is

```text
||X-E_F(X)||_2^2
 =(1/(2|F|))sum_(g in F)||rho(g)Xrho(g)*-X||_2^2.       (LFC7)
```

The real-Hilbert-space form is already formalized in
`GroupApproximation/PropertyT/FiniteGroupAverage.lean` as
`mean_norm_rho_sub_sq`, together with the Pythagorean identity
`norm_sub_orbitAverage_sq`.

In particular, if a bounded matrix `X` almost commutes on average with the
whole finite group, `(LFC7)` recovers an exact coordinate commutant element
with the sharp factor `1/2`. There is no dependence on `|F|` after the error
has been expressed as the normalized group average.

## 3. Slow diagonal recovery for a locally finite union

Let

```text
pi:K -> U(prod_omega M_(d_n))                            (LFC8)
```

be a homomorphism. On each fixed `K_m`, finite-group Hilbert--Schmidt
stability permits the coordinate lifts of `pi|K_m` to be replaced, after a
vanishing relative dimension adjustment if necessary, by exact
representations. Choose the diagonal `m=m(n)` sufficiently slowly that

1. `m(n)->_omega infinity`;
2. the repaired representation agrees with the chosen lifts on `K_(m(n))`
   up to `o(1)`; and
3. for every selected bounded lift `X_n` of an element
   `x in pi(K)'`,

```text
(1/|K_(m(n))|)sum_(g in K_(m(n)))
 ||rho_n(g)X_nrho_n(g)*-X_n||_2^2 ->_omega 0.           (LFC9)
```

The diagonal choice is legitimate because for each fixed `m`, the sum in
`(LFC9)` is finite and every summand tends to zero. For a finite family of
commutant elements, take the maximum of their finitely many averaged
defects before choosing the diagonal.

Now set

```text
Y_n=E_(K_(m(n)))(X_n).                                 (LFC10)
```

Then

```text
Y_n in rho_n(K_(m(n)))',
||X_n-Y_n||_2 ->_omega 0                               (LFC11)
```

by `(LFC7)`. Hence `x=[Y_n]_omega`. This proves the claimed elementwise
coordinate recovery.

This statement is intentionally weaker than equality of the complete
ultraproduct commutant with one ultraproduct of coordinate algebras. The
whole commutant may be nonseparable, while the slow diagonal above may
depend on the chosen finite family. The hyperlinear obstruction needs only
a fixed finite family, so nonseparability is not the immediate issue.

## 4. Why endomorphism compatibility shifts the scale

Let `alpha:K->K` be injective with proper image. For every `m`, choose
`r(m)` so that `(LFC3)` holds. In one exact coordinate representation of a
large enough finite envelope define

```text
C_m=rho(K_m)',
D_m=rho(alpha(K_m))'.                                  (LFC12)
```

Subgroup reversal gives

```text
C_(r(m)) <= D_m.                                       (LFC13)
```

If a coordinate unitary `U` exactly implements `alpha` on `K_m`, then

```text
U C_m U*=D_m.                                          (LFC14)
```

Combining these statements gives `(LFC4)`. Finite-dimensionality yields
only

```text
dim C_(r(m)) <= dim C_m,                               (LFC15)
```

which is already true because commutants shrink as the finite subgroup
grows. The equality-of-dimensions argument would require `r(m)=m`, meaning
a cofinal family of finite subgroups satisfying

```text
alpha(K_m)<=K_m.                                       (LFC16)
```

A proper unilateral compression has no such exhaustion.

## 5. Exact binary-shift model of the defect

Take

```text
K=direct_sum_(j>=0) C_2,
K_m=span(e_0,...,e_(m-1)),
alpha(e_j)=e_(j+1).                                    (LFC17)
```

Then

```text
alpha(K_m)<=K_(m+1),
[K_(m+1):alpha(K_m)]=2.                                (LFC18)
```

Use the left regular representation of `K_(m+1)`. Its commutant as a
`K_(m+1)`-representation has complex dimension

```text
dim C_(m+1)=|K_(m+1)|=2^(m+1).                        (LFC19)
```

Restricted to the subgroup `alpha(K_m)`, the same Hilbert space is two
copies of its regular representation. Therefore

```text
dim D_m=|K_m|*2^2=2^(m+2).                            (LFC20)
```

Thus

```text
dim D_m / dim C_(m+1)=2.                              (LFC21)
```

The inclusion in `(LFC13)` is genuinely proper at every finite level. The
extra commutant dimension is the finite boundary/index carried by the new
binary coordinate. Passing to a slow diagonal does not turn `(LFC21)` into
equality.

This model is the commutant version of the unilateral-shift warning: the
normalized trace of a boundary projection can vanish while its integer
index remains one. In Clifford amplification, a microscopic boundary can
also produce a macroscopic central sign. Therefore discarding the shifted
scale as `o(d)` is not justified.

## 6. Consequence for the Leavitt and spin programs

For the positive unitriangular root group over the binary Leavitt algebra,
every finitely generated subgroup lies in one finite envelope `U(V)`. The
recovery theorem `(LFC11)` therefore solves **separate** finite-coordinate
recovery of every fixed root-commutant element.

What it does not solve is the simultaneous diagram

```text
C_n subset D_n,
D_n=U_n C_n U_n*.                                      (LFC22)
```

The endomorphism moves the finite envelope, producing `(LFC4)` instead.
This is the same compatibility issue isolated in the eight-lamp spin
reduction, but now with the source of the failure made explicit: it is an
exhaustion-scale index, not failure of Reynolds averaging.

A theorem sufficient to continue would take one of two forms.

1. **Normalized/integer index:** recover either a direct nonzero integer
   index on a square finite-dimensional compression, or an index normalized
   by a canonical positive-density spin multiplicity.
2. **Scale synchronization:** use the two Leavitt branches and their
   cross-zero multiplication relation to couple the `m` and `r(m)`
   commutants inside one finite multiplicity corner, producing the three
   contractions already ruled out below `2-sqrt(3)`.

The unnormalized parity-to-phase version of the first route is ruled out by
direct-sum amplification; see
`FALSE_ADDITIVE_INDEX_TO_FINITE_PHASE_IS_NOT_AMPLIFICATION_STABLE.md`. The
second is the paired finite-envelope route. Separate commutant lifting,
including the locally finite theorem proved here, is no longer the missing
statement.

## Primary sources and formal support

- Gowers--Hatami, *Inverse and stability theorems for approximate
  representations of finite groups*,
  [arXiv:1510.04085](https://arxiv.org/abs/1510.04085), supplies the flexible
  finite-group exactification used before `(LFC9)`.
- Alekseev--Thom, *Centralizers of sofic approximations of Kazhdan groups*,
  [arXiv:2608.05362](https://arxiv.org/abs/2608.05362), Open Problem 6.2,
  formulates the corresponding full tracial-matrix commutant-recovery
  problem for Kazhdan groups.
- `GroupApproximation/PropertyT/FiniteGroupAverage.lean` already formalizes
  the exact Reynolds identities used in `(LFC7)`. No local build or compute
  was run for this note.
