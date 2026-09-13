# Invariant-vector witnesses cannot prove SL_3(Z) is not purely matricial field

Lane `ex-mf-kazhdan-cstar`, 2026-09-12.  Unreviewed.

Magee--de la Salle (arXiv:2312.03220v2, Corollary 1.3) prove `SL_4(Z)` is not
purely matricial field (PMF) with one *invariant-vector witness*: a
nonamenable subgroup `H` (the block `SL_2(Z)`) with a nonzero `H`-fixed vector
in every nontrivial finite-dimensional unitary representation.  For finitely
many nonamenable subgroups `H_1, ..., H_k` of a group `Gamma`, call them
*witnesses* if every nontrivial finite-dimensional unitary representation of
`Gamma` has a nonzero vector fixed by some `H_j`.  Witnesses make `Gamma`
not PMF: with generating sets `S_j` of `H_j` put
`y = diag(sum_(s in S_j) s)_(j <= k)` in `M_k(C[Gamma])`; then
`||rho(y)|| = max_j |S_j|` for every such `rho` containing a nontrivial
subrepresentation, while `||lambda_Gamma(y)|| < max_j |S_j|` by Kesten and
`lambda_Gamma|_(H_j) = infinity * lambda_(H_j)`.  (Strong convergence with
scalar coefficients implies it with matrix coefficients.)

**Theorem A.**  `SL_3(Z)` has no finite family of invariant-vector witnesses.
More precisely, for every finite family of nonamenable subgroups
`H_1, ..., H_k <= SL_3(Z)` there are irreducible unitary representations
`pi` of `SL_3(Z)` with finite image, of unbounded dimension, and with
`pi^(H_j) = 0` for all `j`.

**Theorem B.**  Let `D` be a division algebra of degree 3 over `Q` and
`Gamma_D = SL_1(O_D)` for a maximal order `O_D`, a cocompact lattice in
`SL_3(R)` with property (T).  Every nonamenable subgroup of `Gamma_D` is
Zariski dense in `SL_1(D)`.  Consequently every nonamenable `H <= Gamma_D`
has, for all but finitely many primes `p`, no nonzero fixed vector in any
nontrivial irreducible representation of `Gamma_D` through
`SL_1(O_D/pO_D) = SL_3(F_p)`.

Theorem A kills the invariant-vector mechanism for the question Magee--de la
Salle leave open ("we would be very interested to know the answer", p. 2);
Theorem B shows that for cocompact arithmetic Kazhdan lattices of type
`A_2` from division algebras no nonamenable subgroup is even a candidate.

Notation: `q = p` an odd prime; `Omega_p = Sym^2(SL_2(F_p)) <= SL_3(F_p)`, the
image of the *principal* `SL_2` acting on binary quadratic forms
`(x^2, xy, y^2)`; `Omega_p = PSL_2(F_p)`, the index-two spinor kernel in
`SO_3(F_p)`.  The block `SL_2` is `[[*,*,0],[*,*,0],[0,0,1]]`.

## 1. Lemma 1: Deligne's representations have principal-SL_2 invariants

Let `pi` be one of the representations of `SL_3(F_q)` in MdlS Example 2.2, the
restriction of a cuspidal representation of `GL_3(F_q)` of degree
`(q-1)(q^2-1)` attached to the anisotropic torus `F_(q^3)^x`.

Values used.  (i) MdlS Example 2.2: for `g` in the block `SL_2(F_q)`,
`Tr pi(g) = 0` when `(g-1)^2 != 0`.  (ii) Green's formula for the cuspidal
character on unipotent classes of Jordan type `mu`:
`chi(u_mu) = prod_(i=1)^(l(mu)-1) (1 - q^i)`; it gives `(q-1)(q^2-1)` at
`mu = (1,1,1)` and `1 - q` at `mu = (2,1)`, the two values MdlS print, and `1`
at the regular unipotent class `mu = (3)`.

Elements of `Omega_q = Sym^2(SL_2(F_q))`, `q` odd.  `Sym^2` has kernel
`{+-1}`, so `|Omega_q| = q(q^2-1)/2`.  A unipotent `u != 1` of `SL_2` maps to a
regular unipotent (its nilpotent part `N` has `N^2 != 0` because `2 != 0`), and
`Sym^2(-u) = Sym^2(u)`; this gives `q^2 - 1` regular unipotent elements.  Every
other nonidentity element is `Sym^2(g)` with `g` semisimple with eigenvalues
`a, a^(-1)`, `a != +-1`, with eigenvalues `(a^2, 1, a^(-2))`.  If `a^2 != -1`
it is regular semisimple and `SL_3(F_q)`-conjugate to a block element with the
same eigenvalues (centralizer a torus of surjective determinant); if `a^2 = -1`
it is conjugate to `diag(-1,-1,1)`, the block element `-I_2`.  In both cases
`(g-1)^2 != 0` for the block representative, so the trace is `0`.  Hence

```text
dim pi^(Omega_q) = (1/|Omega_q|) sum_(h in Omega_q) Tr pi(h)
                 = [ (q-1)(q^2-1) + (q^2-1) * 1 ] / (q(q^2-1)/2) = 2.
```

So every Deligne representation has a 2-dimensional `Omega_q`-fixed space and
`||pi(Sym^2(S) + Sym^2(S)^(-1) + Sym^2(T) + Sym^2(T)^(-1))|| = 4`, while the
regular norm is the `PSL_2(Z)` Kesten norm `< 4`.  **The MdlS--Deligne family
is not strongly convergent.**  (Check: with `SO_3(F_q) = PGL_2(F_q)` in place
of `Omega_q` the same count gives `1`.)

## 2. Lemma 2: a family with no principal-SL_2 invariants

Let `q = p == 1 mod 4`.  Let `theta` be a character of `F_(q^2)^x` whose
restriction to `mu_(q+1) = ker(N: F_(q^2)^x -> F_q^x)` is the quadratic
character, and `sigma` the cuspidal representation of `GL_2(F_q)` attached to
`theta` (cuspidal because `theta` is nontrivial on `mu_(q+1)`, i.e.
`theta^q != theta`).  Let `mu` be any character of `F_q^x`, `P` the stabilizer
of a line `L` in `F_q^3`, and

```text
pi = Ind_P^(GL_3(F_q)) (mu on L  (x)  sigma on V/L),     irreducible.
```

**Claim.** `pi|_(SL_3(F_q))` has no nonzero `Omega_q`-fixed vector.

Standard values of `sigma`: `q-1` at `1`; `(q-1) theta(z)` at central `z`;
`-theta(z)` at `z u`, `u` unipotent `!= 1`; `0` at noncentral split semisimple
elements; `-(theta(zeta) + theta(zeta^q))` at elliptic elements with
eigenvalues `zeta, zeta^q`.  By Mackey, `pi^(Omega_q)` is the sum over
`Omega_q`-orbits of points `x = [v]` of `P^2(F_q)` of the fixed vectors of
`(mu (x) sigma)` restricted to the stabilizer `Omega_x`, acting on `L = <v>` and
`V/L`.  Identify `P^2 = P(Sym^2 F_q^2)`; the orbits are the conic
(`disc = 0`), the exterior points (split forms) and the interior points
(anisotropic forms), since `PSL_2(F_q)` is already transitive on each.

* *Conic point* `[x^2]`.  `Omega_x` contains `Sym^2` of the unipotent radical,
  which acts on `V/L = <xy, y^2>` as `[[1, 2b],[0,1]]`, `b in F_q`: the full
  unipotent radical of a Borel of `GL_2`.  Cuspidal `sigma` has no fixed vector
  there.  Contribution `0`.
* *Exterior point* `[xy]`.  `Omega_x = N(T_s)`, order `q-1`.  The torus
  `diag(a, a^(-1))` fixes `xy` and acts on `V/L = <x^2, y^2>` as
  `diag(a^2, a^(-2))`: noncentral unless `a^2 = -1`, where it is `-I` (this
  occurs since `4 | q-1`).  The other coset acts on `L` by `-1` and on `V/L`
  with eigenvalues `+-1`, noncentral split: value `0`.  The sum is
  `(q-1) + (q-1) theta(-1)`.  In the cyclic group `mu_(q+1)` of order
  `== 2 mod 4`, `-1` is not a square, so `theta(-1) = -1`.  Contribution `0`.
* *Interior point* (norm form of `F_(q^2)`).  `Omega_x = N(T_ns)`, order `q+1`.
  The torus `mu_(q+1)/{+-1}` fixes the form and acts on `V/L` elliptically with
  eigenvalues `z^2, z^(-2)`; the other coset acts on `V/L` with eigenvalues
  `+-1`, value `0`.  Squaring maps `mu_(q+1)/{+-1}` onto the squares of
  `mu_(q+1)`, where `theta = 1`; no `z^2 = -1` occurs.  The sum is
  `(q-1) - [2 * (q+1)/2 - 2] = 0`.  Contribution `0`.

So `pi^(Omega_q) = 0`, and every constituent of `pi|_(SL_3)` lacks
`Omega_q`-fixed vectors.  The degree is `(q-1)(q^2+q+1)` up to the splitting
of the restriction.

## 3. Proof of Theorem A

Let `H <= SL_3(Z)` be nonamenable and finitely generated (see the last step)
and `Z` its Zariski closure over `Q`.
`H cap Z^0` has finite index in `H`, so `Z^0` is not solvable and contains a
`Q`-simple semisimple subgroup `S` of type `A_1` or `A_2`.  Three types:

1. `S = SL_3`.  Then `H` is Zariski dense and, by strong approximation for
   finitely generated Zariski-dense subgroups (Matthews--Vaserstein--Weisfeiler),
   `H -> SL_3(F_p)` is onto for all but finitely many `p`.  No nontrivial
   irreducible representation of `SL_3(F_p)` has an `SL_3(F_p)`-fixed vector.
2. `S` of type `A_1` acting reducibly on `Qbar^3`.  The decomposition `2 + 1`
   is unique, hence defined over `Q`, and `S` is `GL_3(Q)`-conjugate to the
   block `SL_2`.  For `p` avoiding the denominators, `H mod p` lies in the
   parabolic `U x| GL_2(F_p)` and its projection to `GL_2` contains
   `SL_2(F_p)` (strong approximation for the projection).  A subgroup of
   `U x| SL_2(F_p)` projecting onto `SL_2(F_p)` contains `U` or meets `U`
   trivially; in the second case it is a complement, conjugate to the block
   `SL_2(F_p)` because `H^1(SL_2(F_p), F_p^2) = 0` (`-I` is central and acts
   by `-1`).  Either way a conjugate of the block `SL_2(F_p)` lies in
   `H mod p`, so Deligne's representations twisted by that conjugation (MdlS
   Example 2.2) have no `H`-fixed vector.
3. `S` of type `A_1` acting irreducibly: `S = SO_Q` for a rational ternary form
   `Q`, indefinite because `H` is infinite.  For almost all `p`, `Q` is
   nondegenerate mod `p`, all such forms are similar, `H mod p` contains
   `Omega_Q(F_p)` (strong approximation for `Spin_Q`), and after conjugation
   Lemma 2 gives, for `p == 1 mod 4`, representations with no `H`-fixed vector.

Now let `H_1, ..., H_k` be given.  By the Tits alternative each contains a
nonabelian free subgroup `F_j`; a vector fixed by `H_j` is fixed by `F_j`, so it
suffices to treat the finitely generated `F_j`, each of one of the three types.
Choose distinct primes `p_1, ..., p_k`, larger than 5 and than every exceptional
prime of the strong approximation statements for all `F_i`, with
`p_j == 1 mod 4` when `F_j` is of type 3, and an irreducible `pi_j` of
`SL_3(F_(p_j))` with `pi_j^(F_j) = 0` as above.  Put
`pi = pi_1 (x) ... (x) pi_k`, irreducible for
`SL_3(Z/p_1...p_k) = prod_j SL_3(F_(p_j))`.

Fix `j`.  Let `I` be the image of `F_j` in `prod_i SL_3(F_(p_i))`, `N_i` the
perfect core (last term of the derived series) of its projection to the `i`-th
factor, and `I^(inf)` the perfect core of `I`; it projects onto each `N_i`.
For our primes `N_i` is `SL_3(F_(p_i))`, a conjugate of `U x| SL_2(F_(p_i))` or
of `SL_2(F_(p_i))`, or a conjugate of `Omega(F_(p_i)) = PSL_2(F_(p_i))`.  Their
simple quotients are `PSL_3(F_(p_i))` or `PSL_2(F_(p_i))`, pairwise
nonisomorphic across distinct primes `>= 5`.  A simple quotient of a product of
perfect groups is a quotient of a factor, so by induction on `k` and Goursat's
lemma `I^(inf) = prod_i N_i`.  Hence

```text
pi^(F_j) <= pi^(I^(inf)) = (x)_i pi_i^(N_i) = 0,
```

because `N_j` contains the subgroup (`SL_3`, block `SL_2` or `Omega`) that
`pi_j` does not fix.  Dimensions grow with the primes.  `QED`

## 4. Proof of Theorem B

`D` has degree 3, so `D (x) R = M_3(R)` and `Gamma_D` is a cocompact lattice in
`SL_3(R)` (Godement, `D` anisotropic); property (T) passes to lattices.  Let
`H <= Gamma_D` be nonamenable with Zariski closure `Z <= SL_1(D)`, and `S` as
above.  If `S` is of type `A_1` acting reducibly on `Qbar^3`, its centralizer is
a 1-dimensional torus, unique, hence a `Q`-torus of `SL_1(D)`; its centralizer
in `D` is a `Q`-subalgebra of dimension 5 (block `M_2 x M_1` over `Qbar`).  A
division algebra of prime degree 3 has only subalgebras of dimension 1, 3, 9.
Contradiction.  If `S` acts irreducibly it preserves a symmetric form `b`,
unique up to scalar, so the adjoint involution of `b` is Galois-stable and
descends to an involution of the first kind on `D`; then `[D]` has order at
most 2 in `Br(Q)`, impossible in degree 3.  So `S = SL_1(D)` and `H` is Zariski
dense; strong approximation gives `H mod p = SL_1(O_D/p) = SL_3(F_p)` for
almost all `p` (`D` splits at almost all `p`).  `QED`

## 5. Exact census at small primes (computer check)

Program `experiments/mf-kazhdan-cstar/dist.c` (C, run on MSI 2026-09-12).
For `G = SL_3(Z/n)` it enumerates `G`, computes exact conjugacy classes by
closure under the elementary generators, builds `H = Sym^2(SL_2(Z/n))` and the
block `SL_2(Z/n)`, and computes the permutation character
`P(g) = |C_G(g)| |g^G cap H| / |H|`.  The operator `f -> P * f` on class
functions has rank equal to the number of irreducible `chi` with
`<P, chi> != 0`; its matrix `Q_ij = sum_(x in C_j) P(g_i x^(-1))` is reduced mod
`2^61 - 1` and mod `10^9 + 7` (equal ranks printed).  The nullspace spans the
missing characters; projecting `delta_e` onto it gives `sum chi(1)^2` over
the missing ones.

| `n` | `|G|` | classes | missing for principal `Sym^2` | missing for block | missing for both |
|---|---|---|---|---|---|
| 2 | 168 | 6 | 2, `sum d^2 = 18` (the two 3-dim) | 2, `18` | 2 |
| 3 | 5616 | 12 | 0 | 4, `1024 = 4*16^2` | 0 |
| 5 | 372000 | 30 | 4, `32674 = 2*124^2 + 2*31^2` | 10, `92160 = 10*96^2` | 0 |
| 7 | 5630688 | 64 | 6, `43362 = 4*96^2 + 2*57^2` | 24, `1548288` | 4, `36864 = 4*96^2` |
| 4 | 43008 | 30 | 9, `4050` | 13, `8803` | 9 |

Readings (the decompositions of `sum d^2` are the natural ones in the degree
list of `SL_3(F_q)`, not separately certified):

* `n = 3, 5`: the block misses exactly the Deligne cuspidal representations
  (degrees `16`, `96`), as MdlS Example 2.2 predicts.
* `n = 3`: the principal `SL_2` misses nothing, and the cuspidal degree-16
  representations are not missed, matching Lemma 1.
* `n = 5`: the two degree-124 misses are the Lemma 2 family
  (`(q-1)(q^2+q+1) = 124`; two classes of such `theta` up to twist).  Two
  degree-31 representations (`q^2+q+1`) are also missed.
* `n = 7` (`3 | q-1`): four degree-96 components of the split cuspidal
  representations (`(q-1)(q^2-1)/3`) have no fixed vector for either subgroup.
  So even one prime level has representations escaping both witnesses.
* Rank mod a prime is a lower bound for the rank over `Q`; two unrelated primes
  agree in every run.

## 6. Consequences

* Theorem A answers negatively the natural extension of the MdlS proof to
  `SL_3(Z)`: no finite list of subgroups can witness non-PMF.  Whether
  `SL_3(Z)` is PMF stays open (`sl3z-purely-matricial-field`); an obstruction
  must see more than fixed vectors, e.g. norm excess `||pi(x)|| > ||lambda(x)||`
  without eigenvalue `|S|`.
* Lemma 1 refutes the most natural candidate sequence, the MdlS--Deligne
  representations: they do not converge strongly.
* Theorem B isolates `Gamma_D = SL_1(O_D)`, `deg D = 3`, as a Kazhdan lattice
  on which invariant-vector witnesses cannot even start
  (`cubic-division-lattice-purely-matricial-field`).

Trust surface: the strong approximation theorem for finitely generated
Zariski-dense subgroups (Matthews--Vaserstein--Weisfeiler 1984; Nori 1987;
Weisfeiler 1984), the cuspidal character values of `GL_2(F_q)` and Green's
unipotent values for `GL_3(F_q)` cuspidals, Godement compactness, and Kazhdan's
theorem for lattices are imported without re-reading their sources.  Everything
else is derived above.
