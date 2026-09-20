# Every representation of dimension at most nine kills the five-mark

2026-09-20. The full non-residually-finite hyperbolic-group target
remains open. This is an all-characteristic representation-degree
obstruction, not a classification of arbitrary finite detectors.

## 1. Theorem

Let `Lambda_d` have three `S=PSL_2(F_19)` vertices, pinned edges

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]],
```

central `Z^5=1`, and relations `s_i(xij)=Z^(dij)s_j(xij)`, where
`d in F_5^3` is nonzero. For every field `K`, every `1<=n<=9`,
and every homomorphism `f:Lambda_d -> GL_n(K)`, one has `f(Z)=I_n`.
The central mark is not assumed scalar.

The root lane supplied the all-characteristic argument below; this
lane independently checked it. Its two prior inputs are the proved
amplified Sym4 obstruction and the regular-edge spectral-balance
theorem. No new computation is used.

## 2. Elementary facts about S and the nine-dimensional bound

In `SL_2(F_19)` put

```
u(t)=[[1,t],[0,1]], l(t)=[[1,0],[t,1]], h=diag(2,2^-1).
```

Upper and lower elementary matrices generate `SL_2(F_19)` by
Gaussian elimination; their images therefore generate `S`.
Conjugation by `h` sends `u(t)` to `u(4t)`, so

```
h u(t) h^-1 u(t)^-1 = u(3t).
```

Every upper elementary matrix is a commutator, since multiplication
by three is bijective on `F_19`. Conjugating by the Weyl element
gives the same conclusion for lower ones. Thus `S` is perfect.

Let `U={u(t):t in F_19}`, of order nineteen, and suppose `K` is
algebraically closed with characteristic not nineteen. Restrictions
to `U` are semisimple. If `U` acts trivially, its conjugate lower
subgroup also acts trivially, and generation shows all of `S` acts
trivially. Otherwise a nontrivial `U` character occurs. Index these
characters by nonzero exponents modulo nineteen. Conjugation by
`h` permutes them by multiplication by four or its inverse.
Four has order nine modulo nineteen: `4^3=7!=1` and `4^9=1`.
Every nonzero exponent therefore has orbit of size nine. The nine
distinct eigenspaces have equal positive dimension because `h`
transports them isomorphically. Consequently

```
every nontrivial K[S]-module has dimension at least nine
when char(K)!=19.                               (1)
```

The torus element itself need not be semisimple: even in
characteristic three its permutation of the order-nineteen
eigenspaces suffices. No external projective-degree theorem or
classification of simple finite groups is used. Bound (1), not
existence of degree-nine modules in every characteristic, is asserted.

If every composition factor of an `S`-module is trivial, a
composition-series basis makes its image upper unitriangular, hence
solvable. That image is also perfect, because `S` is perfect.
A solvable perfect group is trivial, as its derived series is
both constant and eventually trivial. Thus a nontrivial module
has a nontrivial simple factor.

## 3. Characteristics other than five

Extend the field to an algebraic closure; matrix identities there
imply the same identities over the original field. Suppose
`char(K)!=5` and `f(Z)!=I`. Since `Z^5=1`, it is semisimple
and has an eigenspace `E` for a nontrivial fifth root. Centrality
makes `E` invariant under the whole triangle. Its restricted
representation has nontrivial scalar mark.

By `hrf-mixed-detectors-have-balanced-edge-spectra`, `dim(E)` is
a positive multiple of five. Since `dim(E)<=n<=9`, it is five.
If the characteristic is not nineteen, (1) makes every vertex
trivial on `E`. A nonzero twisted edge then says `I=(f(Z)|E)^dij`,
impossible for a scalar of exact order five and `dij!=0`.

If the characteristic is nineteen, apply the composition-balance
part of the spectral theorem. The only balanced vector of total
dimension five is the sole simple `L4=Sym^4`: weights at least
six already have dimension at least seven, and the two balance
equations then force `n0=n2=0`, leaving `n4=1`. Thus every
vertex restriction on `E` is exactly `L4`, not an extension.
The amplified Sym4 obstruction at multiplicity one excludes this
case. The theorem follows in all characteristics other than five,
including characteristic zero.

## 4. Characteristic five

Suppose now `char(K)=5`. If some vertex acts nontrivially, it has
a nontrivial simple composition factor by Section 2. Bound (1)
makes that factor's dimension at least nine. Since the total
dimension is at most nine, the whole module is itself that simple
module, of dimension nine. This vertex acts irreducibly.

The central operator `f(Z)` commutes with it, so Schur's lemma
over the algebraically closed field makes `f(Z)` scalar. The
only fifth root of one in characteristic five is one, because
`X^5-1=(X-1)^5`. Hence `f(Z)=I`.

If instead all vertices are trivial, choose an edge with `dij!=0`.
Its relation gives `f(Z)^dij=I`; together with `f(Z)^5=I` and
`gcd(dij,5)=1`, this implies `f(Z)=I`. This handles every
dimension at most nine and completes the proof over all fields.

## 5. Linear and unitary consequences; projective boundary

Every homomorphism from `Lambda_d` into `SL_5(F_q)`, `GL_5(F_q)`,
or `SU_5(F_q)` kills the mark. For the unitary group use its
faithful natural five-dimensional representation over `F_(q^2)`.
The same holds for every subgroup of these groups, without any
surjectivity assumption. More generally, a finite detecting group
cannot have a faithful linear representation of degree at most
nine over any field.

A homomorphism into a projective group does not by itself give a
faithful degree-five representation of a central detecting extension.
If one instead assumes an abstract perfect detector `F` with
`F/<f(Z)>` isomorphic to `PSL_5(q)` or `PSU_5(q)`, identifying
`F` with a quotient of the natural linear or unitary covering
group needs a precise Schur-multiplier/universal-central-extension
theorem, including any exceptional parameters. No such identification
is silently assumed here. All actual degree-five linear realizations
are excluded; the abstract projective-quotient formulation is left
separate. No inference passes through an arbitrary noncentral radical.

## 6. Provenance and verification boundary

Repository search found no prior version of this all-characteristic
nine-dimensional obstruction. The spectral and amplified claims
are explicit dependencies. The root lane supplied the degree-bound
and characteristic-five arguments, independently checked by this
lane. Section 2 supplies elementary perfectness and normal-generation
proofs, avoiding an external simplicity or degree classification.
The defining-characteristic simple-module classification is used
only through the already sourced spectral-balance theorem.

No local or remote computation, installation, finite search, or
certificate run was performed for this result. No priority claim
is made. Higher-degree genuine central detectors remain open.
