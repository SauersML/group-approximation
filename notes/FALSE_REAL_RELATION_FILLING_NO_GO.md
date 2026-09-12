# Real finite-quotient relation filling is quotient-independent

Date: 2026-08-11

## 1. Outcome

The real filling criterion proposed in
`FALSE_FINITE_QUOTIENT_RELATION_FILLING_CRITERION.md` cannot diverge.
For a fixed finite presentation and marked word, its value is exactly the
same for every finite quotient.

More precisely, let

`P=<s_1,...,s_d | r_1,...,r_ell>=F/N`,

let `w in F`, and let `sigma:F->Q` be a surjection onto a finite group which
factors through `P`.  Put

`L=ker(sigma)`, `M_Q=L/[F,L]`.

If `epsilon:F->Z^d` is exponent sum in the chosen free generators, then the
map induced by inclusion,

`M_Q tensor R -> H_1(F;R)=R^d`,

is an isomorphism.  It sends `[x]` to `epsilon(x)`.  Consequently

`D_Q(w;R)`
` =min {sum_j |c_j| :`
`          epsilon(w)=sum_j c_j epsilon(r_j) in R^d}.`       `(RRN1)`

The right side contains no `Q`.  Thus no sequence of finite quotients can
make `D_Q` tend to infinity.  All finite-quotient dependence in the central
relation module is torsion, so every live central-character search must be
modular.

## 2. The real relation module

The five-term exact sequence in integral homology for

`1 -> L -> F -> Q -> 1`

is

`0 -> H_2(Q;Z) -> H_1(L;Z)_Q`
`  -> H_1(F;Z) -> H_1(Q;Z) -> 0`,                    `(RRN2)`

because `F` is free and hence `H_2(F;Z)=0`.  The coinvariants in the middle
are exactly

`H_1(L;Z)_Q=L/[F,L]=M_Q`.                             `(RRN3)`

Both end groups depending on `Q` are finite: a finite group has finite
Schur multiplier and finite abelianization.  Tensoring `(RRN2)` with `R`
therefore gives an isomorphism

`M_Q tensor R ~= H_1(F;R) ~= R^d`.                   `(RRN4)`

The map in `(RRN4)` is induced by the inclusion `L<=F`, so the image of a
word class `[x]` is precisely its exponent-sum vector `epsilon(x)`.

## 3. Exact constancy of the LP

The real marked filling norm was defined by

`D_Q(w;R)`
` =min {sum_j |c_j| :`
`          [w]=sum_j c_j[r_j] in M_Q tensor R}.`      `(RRN5)`

Apply `(RRN4)` to the equality in `(RRN5)`.  It becomes

`epsilon(w)=sum_j c_j epsilon(r_j) in R^d`.           `(RRN6)`

Conversely, `(RRN4)` is injective, so every solution of `(RRN6)` gives the
equality in `(RRN5)`.  The feasible sets, objectives, and optima are
identical.  This proves `(RRN1)`.

If the image of `w` is in `Rad_sof(P)`, then `(RRN6)` is feasible over the
integers.  Indeed the finitely generated abelian group `P_ab` is sofic, so
the quotient map `P->P_ab` kills `w`.  Equivalently,

`epsilon(w) in span_Z{epsilon(r_1),...,epsilon(r_ell)}.` `(RRN7)`

Thus the common value in `(RRN1)` is finite.  In the frequent case
`epsilon(w)=0`, it is exactly zero.

## 4. What remains live

The integral group `M_Q` still depends on `Q` through the finite groups in
`(RRN2)`.  Hence the integral filling norm and the exact modular image can
vary even though the real LP cannot.  A successful central-relator
certificate must use one of the following equivalent torsion phenomena:

1. characters of `M_Q/mM_Q` whose relator phases vanish while the marked
   phase remains visible;
2. growing integral filling coefficients caused by torsion rather than a
   growing real quotient norm; or
3. a marked/relator separation ratio in the canonical finite central module
   `C_(Q,m)` of `FALSE_CANONICAL_CENTRAL_QUOTIENTS.md`.

The computational consequence is sharp: do not build Schreier matrices or
run rational LPs to measure `D_Q`.  Compute the finite abelian torsion data,
the relator classes, and the marked class modulo prime powers.  The existing
`p^k` Baumslag--Solitar amplifier is already a primary-torsion mechanism, so
this closure aligns the finite search with the only part of that construction
which can vary with the quotient.

