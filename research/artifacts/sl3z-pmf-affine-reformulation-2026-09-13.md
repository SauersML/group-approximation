# SL_3(Z) purely matricial field: parabolic and affine reformulations

Lane `ex-sl3z-purely-matricial`, 2026-09-13.  Unreviewed.

PMF = purely matricial field (Magee--de la Salle Definition 1.2): some sequence
of finite-dimensional unitary representations `rho_i` has
`||rho_i(z)|| -> ||lambda(z)||` for every `z` in the group ring.  PFF = the same
with finite images.

## 0. Sources read this session

- **[MdlS]** arXiv:2312.03220v2, read from the PDF (pp. 1--8).  Proposition 2.1
  is proved in three steps.  Step 1 (Section 2.2) concludes "No `C_ij` is
  contained in the kernel of `phi`", using that `phi` is a *new* representation
  of `SL_4(Z/p^r Z)`.  Step 2 (Section 2.3) uses the column group
  `U_1 = {Upsilon(u_1,u_2,u_3)}`, the stabilizer `G_1`, the group `U_2` (entries
  `(1,3),(2,3)`) and the Heisenberg group `H = {[x;y;z]}` (entries `(2,3)`,
  `(3,4)`, `(2,4)`) to find `v` with `phi([x;y;z]) v = exp(2 pi i y / p^r) v`
  (display (2.4)).  Step 3 (Section 2.4) shows the span of `G_2 v`, with
  `G_2 = SL_2` on coordinates `2,3`, is `Ind_N^(G_2) triv`, which contains the
  trivial representation.
- **[GKM]** Gao--Kunnawalkam Elayavalli--Mj, arXiv:2607.29571v1 (31 Jul 2026),
  from the arXiv HTML.  Theorem 1.1: "Let G be a finitely generated residually
  finite amenable group and L be an exact MF/PMF/PFF group. Then G⋊L is
  MF/PMF/PFF."  Their remark on exactness: "Indeed, even in the case of
  trivial actions, i.e, direct products, preservation of strong convergence is
  unknown in the absence of this assumption."  The abstract and Section 1 do not
  mention `SL_n(Z)`, relative property (T) or the Haagerup property.
- **Literature bound.**  The web-search budget is exhausted and the arXiv API
  returned nothing, so the check was three arXiv listing searches (2026-09-13):
  "purely matricial field" in all fields, "strong convergence" representations
  group in abstracts, and "Kunnawalkam Elayavalli strong convergence".  New since
  the predecessor's search: GKM 2607.29571; Barbieri--Jezernik 2602.11905 (free
  products of finite groups); Magee--Puder--van Handel 2504.08988 (surface
  groups); Chen--Garza-Vargas--van Handel 2412.00593; Gao--Kunnawalkam
  Elayavalli 2604.14106 (Toeplitz exactness).  No listed title or abstract
  concerns `SL_d(Z)` or property (T).

## 1. Proposition 1: amenable-kernel semidirect products, without exactness

**Proposition 1.**  Let `Q` be a countable group with finite-dimensional unitary
representations `sigma_n -> lambda_Q` strongly.  Let `A` be a countable amenable
group on which `Q` acts by automorphisms.  Suppose `A = A_0 >= A_1 >= ...` are
`Q`-invariant subgroups of finite index with `cap_N A_N = {e}`.  Then
`G = A x| Q` has finite-dimensional unitary representations converging strongly
to `lambda_G`, and they have finite image when the `sigma_n` do.

If `A` is finitely generated and residually finite, the intersection of all
subgroups of index `<= N` is a characteristic subgroup of finite index, so such
a chain exists.  Proposition 1 therefore contains the PMF and PFF cases of
[GKM] Theorem 1.1, with no exactness assumption on `Q`.

*Proof.*

0. **Matrix coefficients.**  Strong convergence says `z -> (sigma_n(z))_n`
   induces an isometric *-homomorphism `C*_r(Q) -> prod_n M_(k_n) / sum_n M_(k_n)`.
   Tensoring an injective *-homomorphism with `M_d` keeps it injective, hence
   isometric.  So `limsup_n ||(id (x) sigma_n)(x)|| = ||(id (x) lambda_Q)(x)||`
   for `x in M_d(C[Q])`.  The same holds along every subsequence, so the limit
   exists.
1. **Finite affine actions.**  `X_N = A/A_N` carries the `G`-action
   `(a,q) . bA_N = a q(b) A_N`, well defined because `q(A_N) = A_N`.  Let `pi_N`
   be the permutation representation on `l^2(X_N)`, `p: G -> Q` the quotient
   map, and `rho_(N,n) = pi_N (x) (sigma_n o p)`.  It is finite-dimensional, with
   finite image if `sigma_n` has.
2. **Limit in `n`.**  For `z = sum c_(a,q) (a,q)`,
   `rho_(N,n)(z) = (id (x) sigma_n)(x_(N,z))` with
   `x_(N,z) = sum c_(a,q) pi_N(a,q) (x) q in M_(|X_N|)(C[Q])`.  By step 0,
   `lim_n ||rho_(N,n)(z)|| = ||rho_(N,inf)(z)||`, where
   `rho_(N,inf) = pi_N (x) (lambda_Q o p)`.
3. **Identification.**  `lambda_Q o p = Ind_A^G 1`, and
   `pi (x) Ind_A^G 1 = Ind_A^G (pi|_A)` for every representation `pi` of `G`.
   So `rho_(N,inf) = Ind_A^G (pi_N|_A)`, where `pi_N|_A` is the quasi-regular
   representation of `A` on `A/A_N`.
4. **Upper bound.**  `A` is amenable, so `pi_N|_A` is weakly contained in
   `lambda_A` (Hulanicki--Reiter).  Induction preserves weak containment, and
   `Ind_A^G lambda_A = lambda_G`.  So `||rho_(N,inf)(z)|| <= ||lambda_G(z)||`.
5. **Lower bound.**  For `N <= N'` the map `X_(N') -> X_N` is `G`-equivariant, so
   `pi_N <= pi_(N')` and `||rho_(N,inf)(z)||` is nondecreasing in `N`.  The
   coefficient `<pi_N(a) delta_(A_N), delta_(A_N)> = 1_(A_N)(a)` tends to
   `delta_e(a)` pointwise.  So `lambda_A` is weakly contained in
   `(+)_N pi_N|_A`, and by induction `lambda_G` is weakly contained in
   `(+)_N rho_(N,inf)`.  Hence `lim_N lim_n ||rho_(N,n)(z)|| = ||lambda_G(z)||`.
6. **Diagonal.**  Fix `z_1, z_2, ...` dense in `C[G]` for `||.||_1`.  Choose
   `N_m`, then `n_m`, with `| ||rho_(N_m,n_m)(z_j)|| - ||lambda_G(z_j)|| | < 1/m`
   for `j <= m`.  Both norms are 1-Lipschitz in `||.||_1`, so
   `rho_m = rho_(N_m,n_m)` converges strongly to `lambda_G`.  QED.

Exactness never enters: the only coefficient algebra is `M_(|X_N|)(C)`, which
is finite-dimensional.  The MF version (asymptotic homomorphisms in place of
`sigma_n`) has the same proof.

**Model test.**  With `A` trivial the proposition says only that `Q` is PMF.
Amenability is what makes it work: for `A = F_2` with trivial `Q`, the
quasi-regular representations `l^2(F_2/A_N)` contain the trivial representation,
and step 4 fails.

## 2. Corollary 2: `Z^2 x| SL_2(Z)` is PMF, and relative property (T) does not obstruct PMF

`SL_2(Z)` is PMF.  Free groups are PMF ([MdlS] p. 2, citing Haagerup--Thorbjørnsen).
The Sanov subgroup `F = <[[1,2],[0,1]], [[1,0],[2,1]]>` is free of index 12 in
`SL_2(Z)`, because `Gamma(2) = {+-I} x F` has index 6.  Induction from a
finite-index subgroup preserves strong convergence.  With coset representatives
`t_j` and `g t_j = t_(j') f_j(g)`, we get
`Ind sigma(g) = sum_j E_(j'j) (x) sigma(f_j(g))`, a matrix over `C[F]`, while
`Ind lambda_F = lambda_(SL_2(Z))`; apply step 0.  Proposition 1 with `A = Z^2` and
`A_N = N! Z^2` then makes `Z^2 x| SL_2(Z)` PMF.  The same follows from [GKM]
Theorem 1.1, since `SL_2(Z)` is exact.

The pair `(Z^2 x| SL_2(Z), Z^2)` has relative property (T) (Kazhdan; Burger).  So
this group does not have the Haagerup property, while every class of PMF groups
listed in [MdlS] p. 2 and in van Handel's survey (arXiv:2510.12520, Section 2.3)
is a-T-menable.  [MdlS] p. 2: "as far as we know there is no direct relation"
between property (T) and PMF.  Corollary 2 shows that relative property (T) for
an infinite normal subgroup is compatible with PMF.  The same holds for the
integral maximal parabolics of `SL_3(Z)`, which are `Z^2 x| GL_2(Z)` with a
twisted action, `GL_2(Z)` being exact and virtually free.  The theorem is [GKM]'s.
The relative-(T) reading is this lane's, checked only against the listings above.

## 3. Corollary 3: `SL_3(Z)` is PMF iff the Kazhdan group `Z^3 x| SL_3(Z)` is

- `=>`: Proposition 1 with `A = Z^3` and `A_N = N! Z^3`.
- `<=`: `l^2(G)` is the orthogonal sum over cosets `Qg` of copies of `lambda_Q`.
  So `||lambda_G(z)|| = ||lambda_Q(z)||` for `z in C[Q]`, and the restrictions of a
  strongly convergent sequence converge strongly.

The same equivalence holds for MF of reduced algebras.  `Z^3 x| SL_3(Z)` has
property (T) (import: Bekka--de la Harpe--Valette), and it is the index-2
subgroup of the integral parabolic `P_(3,1)(Z)` of `SL_4(Z)`.

## 4. Proposition 4: the Magee--de la Salle mechanism lives in `P_(3,1)`, except level matching

**Proposition 4.**  Let `p` be a prime, `r >= 1` and
`P_r = (Z/p^r)^3 x| SL_3(Z/p^r)`.  Let `tau` be a representation of `P_r` whose
restriction to `(Z/p^r)^3` contains a character `xi` with `xi != 0 mod p`.  Then
`tau` has a nonzero vector fixed by `G_2 = SL_2(Z/p^r)` on coordinates `2,3`.

*Proof.*  [MdlS] Steps 2 and 3 apply verbatim.  Every group they use (`U_1`,
`G_1`, `U_2`, the coordinate-`(1,2)` copy of `SL_2`, `H`, `N`, `G_2`) lies in
`P_r`.  The one input from outside `P_r` is Step 1, and its only role is to
produce `xi != 0 mod p`, which is assumed here.  QED.

**The gap between 3 and 4.**  An irreducible representation of a finite quotient
`(Z/M)^3 x| SL_3(Z/M)` of `P = Z^3 x| SL_3(Z)` is a tensor product `(x)_p tau_p`
over the primes of `M`, by the Chinese remainder theorem.  It has a
`G_2`-invariant vector exactly when every `tau_p` has one.  Proposition 4
supplies one at each prime where `Z^3` is visible at the full level with a
primitive character.  In a representation of `SL_4(Z/M)` that is new at every
prime, Step 1 forces this at all primes.  In `P` nothing does.  A factor on which
`Z^3` is invisible (or visible only at a lower level than the `SL_3` part) is an
arbitrary representation of `SL_3(Z/p^b)`.  It may be of Deligne type, with no
`G_2`-invariants.

So the whole Magee--de la Salle obstruction for `SL_4(Z)` is Proposition 4 plus
*level matching*: the rest of `SL_4(Z)` (normal generation of congruence kernels
by elementary matrices) forces every prime factor to see `Z^3` at full level.
By Corollary 3 the `d = 3` question is the same question for `P_(3,1)(Z)`, where
level matching is simply absent.

## 5. Consequences for `sl3z-purely-matricial-field`

1. A refutation cannot come from a maximal parabolic of `SL_3(Z)` or from
   relative property (T) alone (Corollary 2).  It must use the Kazhdan property
   of a group generated by at least two opposite parabolics.
2. A strongly convergent sequence for `Z^3 x| SL_3(Z)` must keep, in every
   irreducible constituent, a prime at which `Z^3` is invisible or seen at a
   lower level, and the `SL_3` factor there must have no `G_2`-invariants
   (Proposition 4).  `sl3z-has-no-invariant-vector-witnesses` shows such factors
   exist.
3. **Descent to thin subgroups.**  The argument of
   `cubic-division-congruence-sc-descends-to-thin-subgroups` applies to any
   strongly convergent `rho_i` of `SL_3(Z)`.  For `H <= SL_3(Z)` finitely
   generated and Zariski dense (e.g. a thin free group), `rho_i|_H` factors
   through the congruence quotients `H -> SL_3(Z/N_i)`, which are onto for `N_i`
   prime to a finite set.  And `||lambda_(SL_3(Z))(z)|| = ||lambda_H(z)||` for
   `z in C[H]`.  So a positive answer gives constituents of congruence quotients
   of a thin free group converging strongly to its regular representation.
   Restriction to the block `SL_2(Z)` gives the same for congruence quotients of
   `SL_2(Z)`.  van Handel (Section 2.2) records such number-theoretic strong
   convergence as open.
