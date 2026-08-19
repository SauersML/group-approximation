# The Clifford compressor index is infinite at every strict positive compressor

Date: 2026-08-14

## 1. Outcome

This note settles item 3 of Section 7 of
`TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md`, and settles it in the strong
form: not only is the site difference `s X^Gamma minus X^Gamma` infinite for
the positive elementary transvections, the Pimsner--Popa growth index of the
relative commutant is *infinite for every strict positive compressor*, in the
Clifford crossed product itself.

Keep the monomial-cone framing of `FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`
and `(CG20)`:

```text
Lambda=M_(3x2)(Z),   Lambda_+=M_(3x2)(N),   L=SL_3(Z),
L_+=SL_3(Z) intersect M_3(N),
R_+=A[Lambda_+] subset R=A[Lambda],
Gamma=E_r(R_+),      G=E_r(R) semidirect L,
X=G/Gamma,           M_Cl=Cl(X) crossed_product G,
N=M_Cl intersect pi(Gamma)'.                          (CSG1)
```

`L` acts on `Lambda` by left multiplication, and that note proves

```text
P_Gamma intersect L=L_+,       L_+ subset P_Gamma.    (CSG2)
```

**Theorem A.**  For every `s in L_+`,

```text
lambda(s)=[Ad pi(s)(N):N]
 = 1        if s is a permutation matrix,
 = infinity otherwise.                                (CSG3)
```

In particular `lambda(x_(ij)(1))=infinity` for all six positive elementary
transvections `x_(ij)(1)=I+e_(ij)`.  Corollary 7 of the wall note only forces
the disjunction `lambda(x_(12)(1))=infinity` **or**
`lambda(x_(23)(1))=infinity`; inside `M_Cl` both alternatives in fact hold,
and no positive compressor other than a permutation matrix has finite index.

The mechanism has a clean arithmetic reading, recorded here because it will
survive any change of model:

```text
the Clifford modes created by a compressor s are indexed by
L_+ minus L_+ s,
the elements of the compression monoid that are not right
divisible by s.                                        (CSG4)
```

So commutant growth in the Clifford model **is** the failure of right
divisibility in the compression monoid — the same non-Ore phenomenon proved
in `FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`, now seen as an index
computation rather than an obstruction.

Nothing here decides Connes embeddability; Section 7 states exactly what is
and is not concluded.

## 2. The compression monoid sits inside the fixed site set

Recall `(CG26)`:

```text
X^Gamma={g Gamma : g^(-1) in P_Gamma}.                (CSG5)
```

Indeed `g Gamma` is fixed by every `pi(gamma)` iff
`g^(-1) gamma g in Gamma` for all `gamma in Gamma`, i.e. iff
`g^(-1) in P_Gamma`.

**Lemma 1.**  The map

```text
iota:L_+ -> X,     iota(p)=p^(-1) Gamma                (CSG6)
```

is injective, takes values in `X^Gamma`, and for `s,p in L_+`

```text
s.iota(p) in X^Gamma  <=>  p s^(-1) in L_+  <=>  p in L_+ s.  (CSG7)
```

**Proof.**  Values: `p in L_+ subset P_Gamma` by `(CSG2)`, and
`iota(p)=p^(-1)Gamma` with `(p^(-1))^(-1)=p in P_Gamma`, so
`iota(p) in X^Gamma` by `(CSG5)`.

Injectivity: `p^(-1)Gamma=q^(-1)Gamma` means `q p^(-1) in Gamma`.  But
`q p^(-1) in L` and `Gamma=E_r(R_+) subset E_r(R)`, and the two factors of
the semidirect product `G=E_r(R) semidirect L` intersect trivially.  Hence
`q p^(-1)=1`.

Membership after translation: `s.iota(p)=(s p^(-1))Gamma`, which lies in
`X^Gamma` iff `(s p^(-1))^(-1)=p s^(-1) in P_Gamma`.  Since
`p s^(-1) in L`, `(CSG2)` turns this into `p s^(-1) in L_+`, which is the
statement `p in L_+ s` because `L_+` is a monoid and `s in L_+`.  End proof.

**Corollary 2.**  For every `s in L_+`,

```text
#(s X^Gamma minus X^Gamma) >= #(L_+ minus L_+ s),      (CSG8)
```

the injection being `p |-> (s p^(-1))Gamma`.

**Proof.**  Immediate from Lemma 1; injectivity of `p |-> s p^(-1)Gamma`
follows from injectivity of `iota` because `s` acts bijectively on `X`.
End proof.

## 3. Right divisibility fails except at the units

**Lemma 3 (units of the compression monoid).**  If `s in L_+` and
`s^(-1) in M_3(N)`, then `s` is a permutation matrix; every permutation
matrix in `SL_3(Z)` normalizes `Gamma`, so `lambda(s)=1` for such `s`.

**Proof.**  Write `B=s^(-1)`, so `s,B in M_3(N)` and `sB=I`.  For `i!=j`,
`sum_k s_(ik) B_(kj)=0` with nonnegative terms, so every product
`s_(ik)B_(kj)` vanishes.  For `i=j`, `sum_k s_(ik)B_(ki)=1`, so exactly one
index `k_i` has `s_(i k_i)B_(k_i i)=1` and hence
`s_(i k_i)=B_(k_i i)=1`.  If `s_(ik)>0` for some `k!=k_i`, then
`B_(kj)=0` for all `j!=i` by the first display and `B_(ki)=0` by the second,
so row `k` of `B` vanishes and `B` is singular — impossible.  Thus each row
of `s` has the single nonzero entry `1`, and `i |-> k_i` is injective, so `s`
is a permutation matrix.

A permutation matrix maps `Lambda_+` bijectively onto `Lambda_+`, hence
`s(R_+)=R_+` and `s Gamma s^(-1)=Gamma`; `(CG16)` gives `lambda(s)=1`.
End proof.

**Theorem 4.**  Let `s in L_+` not be a permutation matrix.  Then
`L_+ minus L_+ s` is infinite.

**Proof.**  Suppose it is finite.  For fixed `i!=j` the matrices
`x_(ij)(n)=I+n e_(ij)`, `n in N`, are pairwise distinct elements of `L_+`,
so all but finitely many of them lie in `L_+ s`; that is,

```text
x_(ij)(n) s^(-1)=s^(-1)+n e_(ij)s^(-1) in L_+ subset M_3(N)  (CSG9)
```

for infinitely many `n`.  The `(i,k)` entry of the left side is

```text
(s^(-1))_(ik)+n (s^(-1))_(jk),                        (CSG10)
```

and nonnegativity for arbitrarily large `n` forces `(s^(-1))_(jk)>=0` for
every `k`.  Every index `j` occurs as the second index of some pair
`i!=j`, so all rows of `s^(-1)` are nonnegative, i.e. `s^(-1) in M_3(N)`.
Lemma 3 makes `s` a permutation matrix, a contradiction.  End proof.

For the six transvections the witnesses are explicit: with `s=x_(ij)(1)`,
take `p_n=I+n e_(ji) in L_+`.  Then `p_n s^(-1)=p_n(I-e_(ij))` replaces
column `j` by `col_j(p_n)-col_i(p_n)`, whose `i`-th entry is
`0-1=-1<0`.  Hence `p_n notin L_+ s` for every `n>=0`, and Corollary 2
gives infinitely many new sites.

## 4. Every new site has an infinite `Gamma`-orbit

**Lemma 5.**  Let `ell in L` with `ell^(-1) notin M_3(N)`.  Then

```text
[Gamma:Gamma intersect ell Gamma ell^(-1)]=infinity.   (CSG11)
```

**Proof.**  Pick `(a,b)` with `(ell^(-1))_(ab)<0`.  For `m>=1` and any column
index `c`, the matrix `mu=m E_(bc) in Lambda_+` satisfies

```text
(ell^(-1) mu)_(ac)=m (ell^(-1))_(ab)<0,
```

so `ell^(-1)mu notin Lambda_+`, i.e. `mu notin ell Lambda_+`.  Thus
`Lambda_+ minus ell Lambda_+` is infinite.

Now `ell Gamma ell^(-1)=E_r(A[ell Lambda_+])`, because `L` acts on `E_r(R)`
entrywise through the ring automorphism `x^mu |-> x^(ell mu)`.  For
`mu in Lambda_+` the element `x_(12)(x^mu)` lies in `Gamma`.  If two of
them, at `mu!=nu`, lay in one coset of `Gamma intersect ell Gamma ell^(-1)`,
then

```text
x_(12)(x^mu)^(-1) x_(12)(x^nu)=x_(12)(x^nu-x^mu)
```

would lie in `E_r(A[ell Lambda_+]) subset M_r(A[ell Lambda_+])`, forcing the
`(1,2)` entry `x^nu-x^mu` into `A[ell Lambda_+]`.  Distinct monomials are
linearly independent, so this puts both `mu` and `nu` in `ell Lambda_+`.
Choosing all `mu` in the infinite set `Lambda_+ minus ell Lambda_+`
therefore produces infinitely many distinct cosets.  End proof.

**Corollary 6.**  Let `s in L_+` and `p in L_+ minus L_+ s`, and put
`z_p=(s p^(-1))Gamma in s X^Gamma minus X^Gamma`.  Then the `Gamma`-orbit of
`z_p` in `X` is infinite.

**Proof.**  The stabiliser of `z_p` in `Gamma` is
`Gamma intersect ell Gamma ell^(-1)` with `ell=s p^(-1)`, and
`ell^(-1)=p s^(-1) notin M_3(N)` by Lemma 1 and `(CSG2)`.  Apply Lemma 5.
End proof.

## 5. Clifford monomials over the new sites are orthogonal to `N`

Let `(mu_j)` be a Kazhdan sequence for the property-`(T)` group `Gamma`:
finitely supported probability measures on `Gamma` with

```text
||sigma(mu_j)-P_sigma||->0                             (CSG12)
```

uniformly over all unitary representations `sigma`, where `P_sigma` is the
orthogonal projection onto `sigma(Gamma)`-invariant vectors.  Such a sequence
exists: take a finite symmetric Kazhdan set `K` with constant `kappa`, put
`a=(1/|K|)sum_(s in K) s`, and let `mu_j=((delta_e+a)/2)^(*j)`.  In every
representation `sigma((delta_e+a)/2)` is a self-adjoint contraction which is
the identity exactly on invariant vectors.  On their orthogonal complement,
which is `sigma`-invariant, a unit vector `xi` satisfies

```text
Re<sigma(a)xi,xi> = 1-(1/(2|K|)) sum_(s in K) ||sigma(s)xi-xi||^2
                  <= 1-kappa^2/(2|K|),
```

since the Kazhdan set gives `max_(s in K)||sigma(s)xi-xi||>=kappa`.  Hence

```text
||sigma((delta_e+a)/2)|_(complement)||<=1-kappa^2/(4|K|),   (CSG12a)
```

the spectrum of `sigma((delta_e+a)/2)` lying in `[0,1]` because that of
`sigma(a)` lies in `[-1,1]`.  The bound depends only on `(K,kappa)`, not on
`sigma`, so the powers converge in norm to `P_sigma` at a rate independent of
`sigma`.  (The `|K|` in the denominator is not cosmetic: averaging over `K`
dilutes the Kazhdan defect by the size of the set.  Only the uniformity is
used below, never the value.)

Because `Ad pi|_Gamma` is a unitary representation of `Gamma` on
`L^2(M_Cl)` whose fixed-point space is `L^2(N)`, `(CSG12)` gives

```text
E_N(y)=lim_j sum_gamma mu_j(gamma) pi(gamma) y pi(gamma)^*  (CSG13)
```

in `||.||_2` for every `y in M_Cl`.

**Lemma 7.**  Let `F subset X` be finite and nonempty and write `c_F` for the
ordered Clifford monomial over `F`.  If the setwise `Gamma`-stabiliser
`Gamma_F` has infinite index in `Gamma`, then `E_N(c_F)=0`.

**Proof.**  Each `pi(gamma) c_F pi(gamma)^*` equals `epsilon(gamma) c_(gamma F)`
with a sign `epsilon(gamma) in {+1,-1}` coming from reordering.  Distinct
Clifford monomials are orthogonal in `L^2`, so

```text
||sum_gamma mu_j(gamma) epsilon(gamma) c_(gamma F)||_2^2
 <= sum_(gamma,gamma': gamma F=gamma' F) mu_j(gamma)mu_j(gamma')
  = <lambda_(Gamma/Gamma_F)(mu_j) delta,delta>,
```

the last expression being the value of `mu_j` in the quasi-regular
representation at the base vector.  Infinite index means
`ell^2(Gamma/Gamma_F)` has no invariant vector, so `(CSG12)` makes that
value tend to `0`.  End proof.

**Lemma 8.**  If a finite `F subset X` contains a point with infinite
`Gamma`-orbit, then `[Gamma:Gamma_F]=infinity`.

**Proof.**  `Gamma_F` permutes the finite set `F`, so every `Gamma_F`-orbit
inside `F` is finite.  If `[Gamma:Gamma_F]` were finite, the stabiliser of
each point of `F` would have finite index in `Gamma_F`, hence in `Gamma`,
making every `Gamma`-orbit of a point of `F` finite.  End proof.

## 6. The index theorem

**Theorem A (restated and proved).**  Let `s in L_+` not be a permutation
matrix.  Then `lambda(s)=infinity`.

**Proof.**  Fix `k>=1`.  By Theorem 4 and Corollary 2 choose `2k` distinct
sites

```text
z_1,...,z_(2k) in s X^Gamma minus X^Gamma,             (CSG14)
```

and note that every `z_i` has infinite `Gamma`-orbit by Corollary 6.  Since
`z_i in s X^Gamma`, the coset `z_i` is fixed by `s Gamma s^(-1)`, so

```text
c_(z_i) in M_Cl intersect pi(s Gamma s^(-1))'=N_s=Ad pi(s)(N),
```

using Lemma 1 of the wall note for the last equality.  Put

```text
q=product_(j=1)^k (1+i c_(z_(2j-1)) c_(z_(2j)))/2.     (CSG15)
```

Each factor is a projection: `(i c_a c_b)^*=i c_a c_b` and
`(i c_a c_b)^2=1` for `a!=b`.  Factors with disjoint index pairs commute, so
`q` is a projection in `N_s`, and expanding the product writes

```text
q=2^(-k)(1+sum over nonempty even F of +-c_F),         (CSG16)
```

a sum of Clifford monomials over nonempty subsets of `{z_1,...,z_(2k)}`.
Every such `F` contains a point of infinite `Gamma`-orbit, so Lemmas 7 and 8
give `E_N(c_F)=0`, whence

```text
tau(q)=2^(-k),      E_N(q)=2^(-k) 1.                   (CSG17)
```

Let `delta` be the Pimsner--Popa constant of `N subset N_s`, the largest
number with `E_N(y)>=delta y` for all positive `y in N_s`.  Taking `y=q`
gives `2^(-k) 1-delta q>=0`, and since `q` is a nonzero projection this
forces `delta<=2^(-k)`.  Hence

```text
lambda(s)=[N_s:N]=delta^(-1)>=2^k                      (CSG18)
```

for every `k`, i.e. `lambda(s)=infinity`.  Together with Lemma 3 this proves
`(CSG3)`.  End proof.

## 7. Consequences and scope

1. **The prediction `(CG25)` is confirmed and strengthened.**  Corollary 7 of
   the wall note derives, from the mere existence of the wall in `M_Cl`, that
   `lambda(x_(12)(1))` or `lambda(x_(23)(1))` is infinite.  Theorem A
   computes both, together with every other positive compressor, directly.
   The index calculus of that note is therefore consistent with the model it
   was designed to constrain, and the consistency test requested in its
   Section 7, item 3, is passed.

2. **Theorem 6 of the wall note is vacuous inside `M_Cl`.**  Every strict
   positive compressor has infinite growth index there, so the
   commutator-cancellation obstruction never applies to this model.  It
   remains a genuine constraint on *other* candidate models: any proposed
   Connes-embeddable wall model must also have infinite growth index at some
   positive elementary transvection, hence — by the same Steinberg identities
   — at every strict positive compressor whose finiteness would cancel.

3. **The growth is arithmetic, not analytic.**  `(CSG4)` identifies the new
   Clifford modes with `L_+ minus L_+ s`.  A model with *finite* growth would
   need the compression monoid to be right divisible by `s` off a finite set,
   which Theorem 4 shows happens only at the units.  This is the exact
   monoid-theoretic reason no finite lamp set and no finite-orbit
   construction can carry the wall, complementing the finite-dimensional
   collapse `commutant-no-growth` and the compact-closure collapse
   `infranormal-compact-closure-normal`.

4. **What is *not* concluded.**  Theorem A says nothing about Connes
   embeddability of `M_Cl`.  It is a computation inside a fixed tracial von
   Neumann algebra which exists unconditionally.  What it does show is that
   the *shape* of the growth demanded by Corollary 5 of the wall note —
   a proper self-inclusion of infinite index, iterated, with all steps
   isomorphic — is realized here in the most extreme possible way, and that
   this shape by itself is harmless: the one-sided Clifford shift

   ```text
   Cl(N) -> Cl(N),     c_n |-> c_(n+1)
   ```

   is an endomorphism of the hyperfinite II_1 factor with infinite-index
   image, so an infinite-index compressor tower is available inside `R`
   itself.  The obstruction to embedding `M_Cl`, if there is one, cannot be
   the index arithmetic; it can only be the coherence of the full
   property-`(T)` group action with such a tower.

## 8. The relative commutant itself, and what the tower really is

Section 7 item 3 of the wall note asks for `N` as well as for the site
count.  Here is what `N` is.

**Proposition 9 (Fourier description).**  Write `m in M_Cl` as
`m=sum_g a_g u_g` with `a_g in Cl(X)` and `sum_g ||a_g||_2^2<infinity`.  Then

```text
m in N  <=>  gamma(a_g)=a_(gamma g gamma^(-1))
             for all gamma in Gamma, g in G.            (CSG19)
```

In particular `N intersect Cl(X)=Cl(X)^Gamma`, and a general element of `N`
is determined by one coefficient per `Gamma`-conjugacy class, that
coefficient being fixed by the centralizer `C_Gamma(g)`.

**Proof.**  `u_gamma m u_gamma^*=sum_g gamma(a_g) u_(gamma g gamma^(-1))`,
and Fourier coefficients are unique.  End proof.

**Proposition 10 (the fixed algebra lives on finite orbits).**  Put

```text
X_fin={x in X : the Gamma-orbit of x is finite}.        (CSG20)
```

Then `Cl(X)^Gamma=Cl(X_fin)^Gamma`.

**Proof.**  Fix a total order on `X`; the monomials `c_F` are an orthonormal
basis of `L^2(Cl(X))` and `gamma(c_F)=epsilon(gamma,F)c_(gamma F)` with a
reordering sign.  If `a=sum_F lambda_F c_F` is fixed then `|lambda_F|` is
constant along `Gamma`-orbits of finite sets, so square summability forces
`lambda_F=0` whenever that orbit is infinite.  A finite `F` has finite orbit
iff every point of `F` does: one direction is Lemma 8, the other is that
`Gamma_F` contains the finite intersection `intersect_(x in F) Gamma_x`.
Finally `X_fin` is a union of orbits, so it is `Gamma`-invariant.  End proof.

**Theorem 11 (on the external cosets there is no middle ground).**  For the
monomial-cone pair and `ell in L`, the `Gamma`-orbit of `ell Gamma` is a
single point if `ell` is a permutation matrix, and infinite otherwise.
Hence

```text
X_fin intersect {ell Gamma : ell in L}
 = X^Gamma intersect {ell Gamma : ell in L}
 = iota(L_+),                                           (CSG21)
```

and `Gamma` acts trivially there, so the part of `Cl(X)^Gamma` carried by
the external cosets is the full Clifford algebra `Cl(iota(L_+))`.

**Proof.**  The stabiliser of `ell Gamma` is `Gamma intersect ell Gamma
ell^(-1)`.  If `ell^(-1) notin M_3(N)` then Lemma 5 makes its index
infinite.  If `ell^(-1) in M_3(N)` then Lemma 3 makes `ell` a permutation
matrix, so `ell Lambda_+=Lambda_+` and `ell Gamma ell^(-1)=Gamma`, giving a
fixed point.  The identification with `iota(L_+)` is Lemma 1.  End proof.

**What the tower is.**  Combining with Lemma 1: under `p |-> iota(p)` the
external part of the tower reads

```text
Cl(iota(L_+)) subset Cl(iota(L_+) s^(-1)) subset ...    (CSG22)
```

with `Ad u_s` acting as **right division by `s`** on the index monoid and
each step adjoining exactly the modes indexed by `L_+ minus L_+ s`.  Because
`L_+` is neither right nor left Ore
(`FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`), this is a directed system with
no common refinement — the compression monoid's own arithmetic, second
quantized.

This localizes the difficulty precisely.  The system `(CSG22)` **by itself**
is harmless: a Clifford algebra with an injective endomorphism of infinite
index is the one-sided Clifford shift, which lives inside the hyperfinite
`II_1` factor and is Connes embeddable.  What is not supplied by `(CSG22)`
is the coupling — the higher Fourier degrees of `(CSG19)`, and the
requirement that a single homomorphism of the whole Kazhdan group `G`
implement all of the compressor shifts simultaneously.  Any construction
attempt should therefore begin from `(CSG22)`, which is free, and spend its
effort exactly on the coupling.

Two honest gaps.  Theorem 11 covers the external cosets `ell Gamma`; a
general coset is `(u,ell)Gamma` and its orbit is not computed here, so
`X_fin` may be larger than `iota(L_+)` elsewhere in `X`.  And Proposition 9
describes `N` but does not identify the higher-degree part concretely;
`C_Gamma(g)`-fixed Clifford coefficients are what would have to be computed.

## References

* `notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md`, Lemma 1, Theorems 2 and
  4, Corollaries 5 and 7, and Section 7 item 3 (the question answered here).
* `notes/FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`, `(ONO1)`--`(ONO10)`, for
  the framing and for `P_Gamma intersect L=L_+`.
* M. Pimsner and S. Popa, *Entropy and index for subfactors*, Ann. Sci.
  Ecole Norm. Sup. 19 (1986), for the index of an inclusion of finite von
  Neumann algebras with respect to the trace-preserving expectation.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, for the
  representation-independent norm convergence used in `(CSG12)`.
