# A finite central-relator certificate for a hyperlinear nonsofic group

Date: 2026-08-11

## 1. Outcome

**Closure update for the explicit symmetric double.** The criterion in this
note remains valid, but its hypotheses cannot occur for that presentation.
Its full finite residual \(R\) satisfies \(R=[D,R]\), so every radical word
has one fixed relator coefficient vector in all finite central-relator
models. See `FALSE_FINITE_RESIDUAL_COMMUTATOR_NO_GO.md`.

The remaining frozen-clock search can be formulated without optimizing
unitary matrices.  It is enough to find finite groups with a cyclic central
subgroup and generator labels for which every defining relator has
sublinear central exponent, while one fixed sofic-radical word has a
macroscopic central exponent.

The central-character summand of the finite regular representation then
turns the labels into normalized-Hilbert--Schmidt microstates.  Thus the
output of the computation may be a finite multiplication table together
with integer exponents; no numerical unitary search is required.

## 2. Central-character blocks

Let `E` be a finite group and let

`Z=<z> <= Z(E)`, `|z|=m`.                              `(CRS1)`

Put `omega=exp(2 pi i/m)`.  In the left regular representation of `E`, the
central idempotent

`e_omega=(1/m) sum_(j=0)^(m-1) omega^(-j) lambda(z)^j` `(CRS2)`

is nonzero.  Its range `H_omega` is invariant under `lambda(E)`, and the
restricted representation

`rho_omega:E->U(H_omega)`                              `(CRS3)`

satisfies

`rho_omega(z)=omega 1`.                                `(CRS4)`

Indeed `(CRS2)` is the Fourier projection for the character
`z |-> omega`; nonzeroness follows already by applying it to the delta
function at the identity.  Consequently

`||rho_omega(z^a)-1||_2`
` =|exp(2 pi i a/m)-1|`,                               `(CRS5)`

where the norm is normalized Hilbert--Schmidt norm on `H_omega`.

## 3. The finite certificate

Let

`P=<s_1,...,s_d | r_1,...,r_l>`                       `(CRS6)`

be a finitely presented group, and let `w` be a fixed word in the
generators whose image is a nonidentity element of `Rad_sof(P)`.

For every `n`, suppose there are:

1. a finite group `E_n` with a central element `z_n` of order `m_n`;
2. labels `u_(n,1),...,u_(n,d) in E_n`; and
3. integers `b_(n,j)` and `a_n`, read modulo `m_n`, such that

`r_j(u_(n,1),...,u_(n,d))=z_n^(b_(n,j))`              `(CRS7)`

for every defining relator, and

`w(u_(n,1),...,u_(n,d))=z_n^(a_n)`.                   `(CRS8)`

Write

`|b|_(m)=min_(k in Z)|b-km|`.                         `(CRS9)`

The two quantitative requirements are

`max_j |b_(n,j)|_(m_n)/m_n ->0`,                      `(CRS10)`

and

`liminf_n |exp(2 pi i a_n/m_n)-1|>0`.                 `(CRS11)`

**Theorem 1 (central-relator separation criterion).**  Data
`(CRS6)--(CRS11)` produce a hyperlinear nonsofic group.  More precisely,
the image of `P` in the resulting tracial matrix ultraproduct is
hyperlinear, retains `w`, and is therefore not sofic.

**Proof.**  Apply Section 2 to `(E_n,z_n)` and write `rho_n` for the
central-character representation with

`rho_n(z_n)=exp(2 pi i/m_n)1`.                         `(CRS12)`

Assign

`s_i |-> U_(n,i):=rho_n(u_(n,i))`.                    `(CRS13)`

By `(CRS7)` and `(CRS12)`, the defect of the `j`-th defining relator is
exactly

`||r_j(U_(n,1),...,U_(n,d))-1||_2`
` =|exp(2 pi i b_(n,j)/m_n)-1|`
` <=2 pi |b_(n,j)|_(m_n)/m_n`.                        `(CRS14)`

It tends to zero by `(CRS10)`.

Choose once and for all a word representative `v_g` for every `g in P` and
evaluate it at the matrices `(CRS13)`.  If two words represent the same
element of `P`, their quotient is a finite product of conjugates of the
finitely many relators and their inverses.  The normalized
Hilbert--Schmidt norm is unitarily invariant, and the telescoping inequality
therefore shows that the two evaluations have distance tending to zero by
`(CRS14)`.  The same argument applied to
`v_g v_h v_(gh)^(-1)` proves asymptotic multiplicativity.  Hence the word
evaluations induce a homomorphism

`Phi:P->product_omega U(H_(omega,n))`.                `(CRS15)`

Equation `(CRS8)` gives

`||Phi_n(w)-1||_2`
` =|exp(2 pi i a_n/m_n)-1|`.                          `(CRS16)`

Thus `(CRS11)` says that `Phi(w)!=1`.  Let `L=Phi(P)`.  It is hyperlinear
because it is a subgroup of a tracial matrix ultraproduct.  If `L` were
sofic, the quotient homomorphism `P->L` would kill every element of
`Rad_sof(P)`, in particular `w`, contradicting `(CRS16)`.  Therefore `L`
is nonsofic.  QED

## 4. Why nonzero relator curvature is essential

If every exponent in `(CRS7)` is zero, the generator labels define an
honest homomorphism `P->E_n`.  Since `E_n` is finite and `w` lies in the
sofic radical, `(CRS8)` must then have `a_n=0 mod m_n`.

More generally, let

`B_n=<z_n^(b_(n,1)),...,z_n^(b_(n,l))> <= <z_n>`.    `(CRS17)`

After quotienting `E_n` by `B_n`, all defining relators vanish, so the
labels induce a homomorphism from `P` to the finite group `E_n/B_n`.
The radical word dies in this quotient.  Hence

`z_n^(a_n) in B_n`.                                   `(CRS18)`

Thus the phenomenon required by Theorem 1 is a precise finite collision:
the individual defining curvatures are tiny on the circle, but the finite
quotient forces the radical word to accumulate a macroscopic element of
the subgroup they generate.  Exact finite models cannot do this; an
unbounded collision coefficient is necessary.

## 5. Frozen-clock computational target

For the fold-aligned Baumslag--Solitar construction, take

`P=D=G *_Gamma G`                                     `(CRS19)`

and

`w=i_2(h)i_1(h)^(-1) in Rad_sof(D) minus {1}`.        `(CRS20)`

The exact `p^k` clock gives the intended central-character block and the
macroscopic value of `(CRS11)`.  The remaining extension problem can now
be attacked as a finite algebra problem:

1. freeze the clock/shift labels;
2. add labels only for the square-zero elementary generators, coefficient
   `Q`, the remaining external substitution generators, and the second
   vertex;
3. require every presentation relator to evaluate to a power of the same
   central clock element;
4. record the integer exponent of each relator and of `w`; and
5. test `(CRS10)--(CRS11)` exactly.

This is stronger than observing a small numerical matrix defect.  A
successful stage comes with an exact finite certificate: multiplication in
`E_n`, the central order `m_n`, and the exponent table.  Conversely, the
relations which fail to land in the center identify the representation-
theoretic obstruction before any high-dimensional optimization is run.

The theorem does not assert that such certificates exist.  It isolates the
smallest exact output which would finish FALSE and explains how the local
clock amplifier must couple to the global `SL_d(Z)` relations.

## 6. The multi-central criterion

The cyclic center is convenient but unnecessary.  The form relevant to a
higher-incidence wall code is the following.

For every `n`, let `E_n` be finite, let

`Z_n <= Z(E_n)`                                       `(CRS21)`

be any finite central subgroup, and let

`chi_n:Z_n->T`                                        `(CRS22)`

be a character.  Suppose generator labels `u_(n,i) in E_n` satisfy

`r_j(u_(n,1),...,u_(n,d)) in Z_n`,                    `(CRS23)`

`w(u_(n,1),...,u_(n,d)) in Z_n`,                      `(CRS24)`

and

`max_j |chi_n(r_j(u_n))-1| ->0`,                      `(CRS25)`

`liminf_n |chi_n(w(u_n))-1|>0`.                       `(CRS26)`

**Theorem 2 (multi-central relator separation).**  Data
`(CRS21)--(CRS26)` produce a hyperlinear nonsofic group.

**Proof.**  In the left regular representation of `E_n`, use the central
Fourier projection

`e_(chi_n)=|Z_n|^(-1) sum_(z in Z_n)`
`                     conjugate(chi_n(z)) lambda(z)`. `(CRS27)`

Its range is nonzero and invariant, and every `z in Z_n` acts on it as the
scalar `chi_n(z)`.  Restricting the generator labels to this range makes
the `j`-th relator defect exactly the left side of `(CRS25)`, while the
marked displacement is the left side of `(CRS26)`.  The word-evaluation
and sofic-radical argument in the proof of Theorem 1 applies verbatim.
QED

Theorem 1 is recovered by taking `Z_n=<z_n>` and
`chi_n(z_n)=exp(2 pi i/m_n)`.

Let

`B_n=<r_1(u_n),...,r_l(u_n)> <= Z_n`.                 `(CRS28)`

Quotienting by `B_n` again produces a finite image of `P`; hence radicality
forces

`w(u_n) in B_n`.                                      `(CRS29)`

Thus a successful multi-central family consists of characters which are
asymptotically trivial on a fixed number of central carry generators but
remain nontrivial on a word in the subgroup they generate.  Equivalently,
if

`w(u_n)=product_j r_j(u_n)^(c_(n,j))`,                `(CRS30)`

then the coefficient vector `c_n` must amplify the vanishing individual
phases into the nonvanishing phase `(CRS26)`.  At least one such coefficient
is unbounded along every successful subsequence.

This is the correct endpoint after the cyclic-wall no-go in
`FALSE_LONG_CHAIN_BUNDLE_MONODROMY_NO_GO.md`.  A bounded-degree scalar
coboundary cannot have low carry and a dense witness, but a growing central
incidence code may.  Computationally one may therefore search for:

1. a finite central carry group `Z_n`;
2. the relator incidence vectors in `Z_n`;
3. the marked-word vector in their span; and
4. a character `chi_n` satisfying `(CRS25)--(CRS26)`.

Once these four finite objects exist, the unitary matrices and the
hyperlinear nonsofic image are automatic from `(CRS27)`.
