---
rg: 2
id: kt-tensor-mask-isometry-and-positive-density-multiplicity-proof
kind: route
title: Cancel the KT regular carrier and expose the bare multiplicity cocycle
target: kt-regular-mask-removes-trace-faithfulness-from-commutant-wall
requires:
  - kt-steinberg-deleted-line-embeddings-have-scalar-commutants
  - kt-two-positive-compressors-generate-full-obstruction
  - strict-compressor-mixed-return-collapses-shared-pauli-sign
---

# Regular trace masking is exactly isometric on the quantum fiber

## 1. Set-up

Let `U` be a nonprincipal ultrafilter.  The canonical Steinberg construction
supplies genuine representations

```text
alpha_n:G->U(D_n)                                       (1)
```

such that

```text
lim_U tr_(D_n)(alpha_n(g))=0 for every g!=1.            (2)
```

Let `v_n:G->U(k_n)` be arbitrary maps satisfying

```text
lim_U ||v_n(g)v_n(h)-v_n(gh)||_(2,k_n)=0                (3)
```

for every fixed `g,h`.  No character or injectivity condition is imposed.
Put

```text
u_n(g)=alpha_n(g) tensor v_n(g).                        (4)
```

The tensor products use normalized matrix traces.

## 2. Defect cancellation

Exact multiplication in (1) gives

```text
u_n(g)u_n(h)-u_n(gh)
 = alpha_n(gh) tensor
   (v_n(g)v_n(h)-v_n(gh)).                              (5)
```

Since a unitary has normalized `2`-norm one and normalized tensor norms
multiply,

```text
||u_n(g)u_n(h)-u_n(gh)||_2
 =||v_n(g)v_n(h)-v_n(gh)||_2.                           (6)
```

Thus `u=[u_n]` is a homomorphism into the tracial matrix ultraproduct.

More generally, evaluate a word `w` in a fixed generating set.  Then

```text
w(u_n)=alpha_n(w) tensor w(v_n).                        (7)
```

If `w` is a relator of `G`, `alpha_n(w)=I`, and hence

```text
||w(u_n)-I||_2=||w(v_n)-I||_2.                          (8)
```

If two words represent the same element of `G`, multiplying their
difference by the common unitary `alpha_n(g)` gives the same identity.  In
particular (8) applies simultaneously to all relations among the two
positive compressors

```text
B=I+E_12,                 A=C B,                        (9)
```

the cyclic normalizer `C`, and the full elementary packet.  The congruence
carrier adds no two-compressor curvature and removes none.

## 3. The trace becomes regular

For every `g`,

```text
tr_(D_n k_n)(u_n(g))
 =tr_(D_n)(alpha_n(g)) tr_(k_n)(v_n(g)).                (10)
```

The second factor has absolute value at most one.  Equation (2) therefore
implies

```text
lim_U tr(u_n(g))=0 for g!=1.                            (11)
```

At the identity the trace is one.  Thus `u` has the regular character,
regardless of the character of `v`.  It is injective and extends to a
trace-preserving embedding of `L(G)` into the new matrix ultraproduct.

This is the trace-mask phenomenon: the finite congruence carrier supplies
all separation, while the multiplicity factor is invisible to every fixed
group trace.

## 4. The multiplicity algebra embeds isometrically

Write

```text
N=product_U M_(k_n),
M=product_U M_(D_n k_n).
```

Define

```text
j:N->M,              j([x_n])=[I_(D_n) tensor x_n].     (12)
```

Normalized tensor traces show

```text
tr_M(j(x))=tr_N(x),
||j(x)||_2=||x||_2,
||j(x)||=||x||.                                         (13)
```

Hence `j` is a well-defined trace-preserving isometric unital
`*`-embedding.  Direct multiplication gives

```text
[j(x_n),u_n(g)]
 =alpha_n(g) tensor [x_n,v_n(g)],                       (14)
```

and therefore

```text
||[j(x),u(g)]||_2=||[x,v(g)]||_2.                       (15)
```

For every subgroup `H<=G` this implies

```text
x in v(H)'  iff  j(x) in u(H)'.                         (16)
```

Here the equivalence is asserted for the displayed multiplicity copy
`j(N)`; the full commutant of `u(H)` may be larger.

Take `H=Lambda`.  If

```text
x in v(Lambda)' but x notin v(Gamma)',                  (17)
```

then (15) gives

```text
j(x) in u(Lambda)' but j(x) notin u(Gamma)'             (18)
```

with exactly the same separating commutator norm.  Likewise, if
`x in v(Gamma)'` and conjugation by some `v(g)` leaves that commutant, then
`j(x)` gives the identical failure of normalization for `u`.  For the mixed
return `r=t^(-1) gamma t`, (15) is precisely preservation of the condition

```text
[x,v(q)]=0 for q in Gamma,       [x,v(r)]!=0.            (19)
```

Thus neither the full Kazhdan packet nor the two-compressor relation changes
the fiber defect.

## 5. Removing trace-faithfulness from the universal question

Suppose compressor commutant equality failed for some matrix-ultraproduct
representation `v` of `G`, with no trace hypothesis.  Equations (4),
(11), and (18) produce a trace-faithful representation `u` with the same
failure.  Therefore

```text
all trace-faithful representations satisfy
v(Lambda)'=v(Gamma)'
```

implies the same assertion for all matrix-ultraproduct representations.
The converse is immediate.  This proves the equivalence (KTM6).  Replacing
relative commutant equality by `G`-normalization of the `Gamma`-commutant
and using the second part of Step 4 proves the normalization version.

This reduction is special to a group admitting an exact finite-dimensional
regular-character tower.  Step 1 constructs such a tower explicitly for the
binary KT actor; no abstract residual-finiteness assertion is being inserted.

## 6. Positive mass and negligible padding

Let `x_n` be contractions with

```text
max_(lambda in F_Lambda)||[x_n,v_n(lambda)]||_2 -> 0,
||[x_n,v_n(gamma_0)]||_2 >= delta-o(1)                  (20)
```

for some fixed finite stabilizer window and some
`gamma_0 in Gamma`.  By (15), `X_n=I_(D_n) tensor x_n` has exactly the same
defects and the same normalized `2`-mass in dimension `D_n k_n`.

Now add an arbitrary block of dimension `q_n=o(D_n k_n)` to every actor
matrix and extend `X_n` by zero.  There are no cross-block commutators.
Every old normalized commutator is multiplied by

```text
lambda_n=sqrt(D_n k_n/(D_n k_n+q_n))->1.                (21)
```

Thus the lower bound in (20) remains `delta-o(1)` and the vanishing rows
remain vanishing.  The displayed multiplicity leak is macroscopic and is
not diluted by negligible direct-sum padding.

This statement does not claim that an arbitrary perturbative exactification
must preserve the tensor block.  A factor-recognition theorem would be
needed for that stronger conclusion.  It does prove that rank dilution,
regular-character tests, and arbitrary added spectator blocks do not remove
an already-existing leak.

## 7. Full physical mass lives in vanishing adjoint rank

Identify

```text
L^2(M_(D_n k_n))
 =L^2(M_(D_n)) tensor L^2(M_(k_n)).                     (22)
```

The adjoint action of `u_n` is
`Ad(alpha_n) tensor Ad(v_n)`.  Its multiplicity copy is the invariant
carrier line tensored with the whole fiber:

```text
K_n=C I_(D_n) tensor L^2(M_(k_n)).                      (23)
```

Every witness `I_(D_n) tensor x_n` belongs to `K_n` and has normalized
`2`-norm exactly `||x_n||_2`.  Yet

```text
dim(K_n)/dim(L^2(M_(D_n k_n)))
 =k_n^2/(D_n^2 k_n^2)
 =D_n^(-2)->0.                                          (24)
```

Thus a multiplicity leak is macroscopic as a matrix and pointed vector but
microscopic as a proportion of the full adjoint carrier.  A bound on the
normalized rank, trace, or spectral density of the low-energy superoperator
sector can converge to zero while the distinguished op-norm-one vector keeps
a fixed displacement.  This realizes exactly the pointed-vector firewall in
`kt-ccr-holds-on-the-fd-tempered-adjoint-sector`.

## 8. The precise frontier

The trivial multiplicity choice `v_n(g)=I` gives a large commutant
`I tensor M_(k_n)` which every actor matrix fixes.  A nontrivial
multiplicity microstate carries exactly the original source problem by
Steps 2 and 4.  Hence amplification of the irreducible congruence carrier
does not interpolate between the two cases; it is a transparent tensor
envelope.

To refute KT normalization it is now enough, and by the trace-removal
equivalence necessary, to build any matrix-ultraproduct representation of
`G` with the leak (17), without first arranging the regular character.
Conversely, a positive proof must control arbitrary multiplicity
microstates, not only trace-faithful or congruence-looking ones.  The
regular carrier, property `(T)` of its elementary image, and joint
`SL_3(Z)` coherence contribute no additional inequality after tensor
cancellation.

No representation `v` satisfying (17) is constructed here.  The
nonhyperlinear-group route therefore remains open.
