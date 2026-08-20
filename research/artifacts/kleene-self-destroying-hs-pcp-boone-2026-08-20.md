# Self-destroying microstates and the HS--PCP Boone target

This artifact records a self-reference route to a nonhyperlinear group and a
finite-dimensionality sensor based on polynomial identities.  It separates
the elementary parts, which are exact, from the one missing theorem:
constant-soundness groupification in normalized Hilbert--Schmidt norm.

## 1. The corrected Kleene window

Fix the normalized Hilbert--Schmidt norm.  Suppose a total computable map sends
a machine `M` to a finite presentation `G_M=<S_M|R_M>` and a word `w_M`, and
there are machine-independent computable rational constants

```text
delta > 0,                0 < alpha < sqrt(2),
```

such that

```text
M does not halt  =>  w_M != 1 in G_M,                              (A)

M halts          =>  Def_R_M(U) < delta
                      implies ||w_M(U)-1||_2 <= alpha              (B)
```

for every finite-dimensional unitary tuple `U`.  Choose computable rational
constants `delta_0,beta` with

```text
0 < delta_0 < delta,          alpha < beta < sqrt(2).
```

Kleene's recursion theorem supplies a machine `M_*` which obtains its own
index, computes `(G_(M_*),w_(M_*))`, and searches all finite dimensions and a
computable dense family of unitary tuples for the strict inequalities

```text
Def_R_(M_*)(U) < delta_0,
||w_(M_*)(U)-1||_2 > beta.                                      (K1)
```

Strict polynomial inequalities on finite matrices are semidecidable, so this
is an effective search.  If `M_*` halts, its witness satisfies the hypotheses
of `(B)` and violates its conclusion.  Hence `M_*` does not halt, and `(A)`
gives `w_(M_*) != 1`.

If `G_(M_*)` were hyperlinear, its canonical group trace would supply
finite-dimensional microstates with relator defect tending to zero and

```text
||w_(M_*)(U_i)-1||_2 -> sqrt(2).
```

Eventually `(K1)` would hold, and openness plus density would make the search
halt.  This contradiction proves that `G_(M_*)` is nonhyperlinear.

The upper bound on `alpha` is essential.  A conclusion merely saying that the
mark is never farther than an arbitrary positive constant from the identity
does not contradict hyperlinearity.

## 2. The game-level fixed point

Lin's `MIP^co=coRE` theorem (arXiv:2510.07162) supplies the required logical
orientation at the level of nonlocal games.  In the constant-gap form, an
effective compiler has constants `c>s` and games `V_M` satisfying

```text
M does not halt  =>  omega_co(V_M) >= c,
M halts          =>  omega_co(V_M) <= s.
```

Choose `s<theta<c`.  A recursion-theorem machine computes its own game and
halts exactly when it finds a finite-dimensional strategy of value greater
than `theta`.  Halting would exhibit commuting value greater than `theta` but
activate soundness `omega_co<=s`; hence it cannot halt.  Completeness then
gives commuting value at least `c`, while failure of the finite-strategy search
gives finite-dimensional value at most `theta`.

This is already a literal self-destroying finite-dimensional verifier.  It is
not yet a group presentation.  Lin's theorem builds on recursive compression
and tracially embeddable strategies; Ji--Natarajan--Vidick--Wright--Yuen,
arXiv:2001.04383, is the tensor-product `MIP*=RE` compression source.

## 3. A two-letter polynomial-identity tape

For the standard polynomial

```text
s_m(X_1,...,X_m)
  = sum_(sigma in S_m) sign(sigma) X_(sigma(1)) ... X_(sigma(m)),
```

Amitsur--Levitzki says that `s_(2d)` vanishes under every substitution in
`M_d(C)`.  In the free algebra `C<x,y>`, set

```text
u_j = x y^j x,
p_n = s_(2n)(u_1,...,u_(2n)).                                  (AL1)
```

Every permutation summand in `p_n` is a different free monomial: the `xx`
separators recover the ordered exponent list.  Thus `p_n!=0` in the free
algebra.  Under every homomorphism `rho:C<x,y> -> M_d(C)`, however,
`rho(p_d)=0`.

Adjoin two-sided formal inverses `q_n` with

```text
p_n q_n = q_n p_n = 1                    for every n>=1.          (AL2)
```

The resulting **countably presented associative algebra** is nonzero because
it embeds in the free skew field, where each nonzero `p_n` is invertible.  It
has no unital finite-dimensional representation, since a `d`-dimensional
representation turns the `n=d` instance of `(AL2)` into `0=1`.

This is an exact finite-dimensionality detector.  It is not a finitely
presented group, a star-algebra of unitaries, or a quantitative HS obstruction.
Those three conversions are part of the missing groupification theorem.

## 4. Multiplicity is the tape

Let `H` be a finite group and `pi` an irreducible complex representation of
dimension `r`.  On a `pi`-isotypic block of an exact finite-dimensional
representation,

```text
Q C^d = C^r tensor C^k,
H acts as pi(H) tensor I_k,
Comm(H)|_Q = I_r tensor M_k(C).                                 (MT1)
```

Consequently two elements `x,y` centralizing `H` restrict to
`I_r tensor X,I_r tensor Y`.  The polynomial tape therefore detects the
multiplicity dimension itself: `p_k(X,Y)=0`.  The rectangular escape is
reinterpreted as the storage space on which the detector runs.

For approximate group representations, one must first exactify the fixed
finite group and retain a positive-density `pi`-sector.  More seriously, the
degree and coefficient mass of `p_k` grow with `k`, so `(MT1)` alone supplies
no dimension-independent HS estimate.

## 5. Conjugacy-compressed terminal flags

If `r` is one fixed relator and `c_n=a_n^(-1) r a_n`, then every unitary
evaluation satisfies the exact identity

```text
||c_n(U)-1||_2 = ||r(U)-1||_2.                                 (CC1)
```

Thus the length or runtime hidden in `a_n` does not amplify the norm of the
terminal flag.  If a semantic compiler additionally proves

```text
||w(U)-c_(N(d))(U)||_2 <= C Def(U)                              (CC2)
```

with `C` independent of dimension and runtime, then

```text
||w(U)-1||_2 <= (C+1) Def(U).                                  (CC3)
```

Equation `(CC1)` is exact and elementary.  The uniform semantic comparison
`(CC2)` is the hard part: writing the last flag as a conjugate does not by
itself compress the accumulated error of a van Kampen derivation equating the
mark with that flag.

## 6. Arbitrary finite predicates have finite irreducible CPU sectors

Let `S` be a nonempty subset of `{+1,-1}^k`, choose a cyclic ordering of its
`m=|S|` elements, and work on the basis `(e_s)_(s in S)`.  Take the finite group
generated by all diagonal sign matrices and the `m`-cycle permuting this basis.
Its natural `m`-dimensional representation is irreducible: invariance under all
diagonal signs makes an invariant subspace a sum of coordinate lines, and the
transitive cycle leaves only the empty or full coordinate set.

For each Boolean variable, the diagonal involution with entries equal to that
variable's signs on `S` belongs to this group.  Their joint spectrum is exactly
`S`, with one joint eigenline for each allowed assignment.  Thus arbitrary
nonlinear finite local rules can live in an honest finite-group irreducible
sector.  This solves local predicate storage, not synchronization of different
predicate sectors.

## 7. The remaining compiler

The Boone tower already converts an arbitrarily long modular-machine
computation into the fixed-shaped exact criterion

```text
[k,t(a,b)] = 1  iff  the machine halts on (a,b).
```

The missing HS--PCP Boone compiler must make the halting implication robust
with constants independent of runtime, in exactly the form `(A)+(B)` above.
The proposed finite-control architecture is:

1. exactify a fixed finite CPU and select a positive-density irreducible
   sector;
2. use its commutant multiplicity factor as the two-letter tape;
3. run the Amitsur--Levitzki sequence until finite multiplicity triggers zero;
4. feed that event, or the self-game event, into recursively compressed local
   checks;
5. return a terminal flag through a fixed holonomy or conjugacy class;
6. charge attempted sector escape through positive-density overlap and fixed
   holonomy.

The literature makes steps 3 and the verifier-level form of step 4 concrete,
but does not supply steps 1--6 as one finitely presented group with uniform
normalized-HS soundness.  Taller--Vidick, arXiv:2507.22444, locate the same
boundary in LCS language: their constant-soundness RE-hardness has
completeness `1-epsilon`, and they state that perfect completeness would imply
a nonhyperlinear group.  Paddock--Slofstra, arXiv:2310.07901, connect BCS
algebras and `R^U`-satisfiability directly to the nonhyperlinear-group problem.

One control loss was removed later on 2026-08-20:
`odd-selector-priority-decoding` assigns every odd joint selector atom to its
least active branch.  Thus simultaneous activation of several verifier
branches does not itself need to pay Hilbert--Schmidt energy.  For an LCS
lowering of step 4, the remaining analytic issue is agreement of decoded
unreadable observables across local contexts.  This does not solve the
runtime-independent comparison `(CC2)`, but it prevents the compiler target
from spending effort on a selector-overlap condition that sound decoding does
not require.
