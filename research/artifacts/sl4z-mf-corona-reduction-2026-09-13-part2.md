# MF of C*_r(SL_4(Z)): the torus dichotomy and the Step 3 firewall (part 2)

Lane `ex3-sl4z-mf`, 2026-09-13.  UNREVIEWED.  Continues
`research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md`.

**Conventions.**
- `d >= 3` and `Gamma = SL_d(Z)`.
- `U = {u(v) = I + sum_(i<d) v_i e_(i,d) : v in Z^(d-1)}` is the column unipotent
  subgroup, isomorphic to `Z^(d-1)`.
- Block elements `diag(A, 1)`, `A in SL_(d-1)(Z)`, satisfy
  `diag(A,1) u(v) diag(A,1)^-1 = u(Av)`.
- A *representation* is a unital *-homomorphism `sigma : C*(Gamma) -> B` into a unital
  C*-algebra.  This covers unitary representations (`B = B(H)`) and corona
  representations (`B = Q_k`).

## 1. The joint spectrum of the column unipotent subgroup

**Definition.**  Identify `C*(U)` with `C(T^(d-1))` by sending `u(v)` to `e_v`, where
`e_v(theta) = exp(2 pi i theta . v)`.  The kernel of `sigma|_(C*(U))` is
`C_0(T^(d-1) \ Y)` for a nonempty closed set `Y`, the joint spectrum.

**Invariance.**  `Ad sigma(diag(A,1))` sends `sigma(e_v)` to `sigma(e_(Av))`, and
`e_(Av)(theta) = e_v(A^T theta)`.  So it sends `sigma(f)` to `sigma(f o A^T)` for every
continuous `f` and preserves the kernel.  Hence `Y` is invariant under `SL_(d-1)(Z)`
acting linearly.

**Lemma 1.**  Let `m >= 2`.  A closed `SL_m(Z)`-invariant subset `Y` of `T^m` is either
a finite set of torsion points or all of `T^m`.

*Proof.*
(a) *Some point of `Y` has an irrational coordinate.*  Let `theta_j` be irrational.
- For `i != j`, the matrix `I + e_(ij)` sends `theta` to `theta + theta_j e_i`.  The
  multiples of `theta_j` are dense mod `1`, so `Y` contains the circle
  `theta + T e_i`.
- Pick `t` with `theta_i + t` irrational, and set `theta' = theta + t e_i`.  For each
  `k != i`, the same step with `I + e_(ki)` adds the circle `theta' + T e_k`.
- Running through all `k != i` leaves coordinate `i` unchanged.  So `Y` contains every
  point whose `i`-th coordinate is `theta_i + t`.  Such `t` are dense, so `Y = T^m`.

(b) *Every point of `Y` is torsion.*  If the orders are bounded by `M`, then
`Y subset (1/M!) Z^m / Z^m`, a finite set.  Otherwise:
- Take `theta^(s) in Y` with orders tending to infinity.  The order of a point is the lcm
  of the orders of its coordinates, so some coordinate `j(s)` has order
  `N_s >= order^(1/m)`, which tends to infinity.
- Pass to a subsequence with `j(s) = j` constant and `theta^(s) -> theta^inf`.  Fix
  `i != j`.
- `theta^(s)_j = a_s / N_s` with `gcd(a_s, N_s) = 1`, so its multiples run through
  `(1/N_s) Z / Z`.  Hence `Y` contains the `1/N_s`-dense set
  `theta^(s) + (1/N_s) Z e_i` inside the circle `theta^(s) + T e_i`.
- `Y` is closed, so it contains `theta^inf + T e_i`.  That circle has a point with an
  irrational coordinate, so `Y = T^m` by (a).

**Lemma 2.**  If `Y` is finite, then `sigma` factors through `C*(SL_d(Z/NZ))`, where
`N` is the lcm of the orders of the points of `Y`.

*Proof.*
- For `v in Z^(d-1)`, `e_(Nv) = 1` on `Y`, so `sigma(u(Nv)) = 1`.  So
  `I + N e_(i,d)` lies in the normal subgroup `K = {g : sigma(g) = 1}` for every `i < d`.
- For `k != l`, choose a signed permutation matrix `P in SL_d(Z)` with `P e_1 = +-e_k`
  and `P e_d = +-e_l`.  A third basis vector exists because `d >= 3`, and its sign fixes
  the determinant.  Then `P (I + N e_(1,d)) P^-1 = I +- N e_(k,l)`.
- So `K` contains every `I + t e_(kl)` with `t in NZ`, and hence their normal closure
  `E_d(Z, NZ)`.
- By `sln-z-principal-congruence-elementary-generated` (Bass--Milnor--Serre,
  Corollary 4.3 b)), `E_d(Z, NZ)` is `ker(SL_d(Z) -> SL_d(Z/NZ))`.

**Theorem A (`sln-z-unipotent-spectrum-finite-or-full-torus`).**  Let `d >= 3` and let
`sigma` be any representation of `SL_d(Z)`.  Then the joint spectrum of the column
unipotent `Z^(d-1)` is either all of `T^(d-1)`, or a finite set of torsion points, in
which case `sigma` factors through some `SL_d(Z/NZ)`.

*Remarks.*
- The ingredients are elementary or classical.  This lane claims no novelty for
  Theorem A.
- For finite-dimensional representations the spectrum is finite, and Theorem A recovers
  the factorization that MdlS quote from Bass--Milnor--Serre (arXiv:2312.03220v2, p. 3).
- Lemma 1 needs only `m = d - 1 >= 2`.  Lemma 2 uses `d >= 3` twice: for BMS, and for the
  signed permutation.

## 2. Norm four away from the full spectrum

**Theorem B (`sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`).**  Let
`sigma : C*(SL_4(Z)) -> B` be a unital *-homomorphism whose column unipotent spectrum is
not all of `T^3`.  Then `||sigma(S + S^-1 + T + T^-1)|| = 4`.  If `B = B(H)`, the block
`SL_2(Z)` fixes a nonzero vector.

*Proof.*
- By Theorem A, `sigma` factors through the finite group `G = SL_4(Z/NZ)`.
  `C*(G)` is the direct sum of the algebras `M_(d_rho)` over irreducible `rho`, with
  central projections `p_rho`.
- `sigma` is unital, so `sigma(p_rho) != 0` for some `rho`.  `sigma` is then injective,
  hence isometric, on the simple summand `C*(G) p_rho`.
- In that summand, `z p_rho` corresponds to `rho(z)`, for the finite-dimensional
  representation `rho o (SL_4(Z) -> G)` of `SL_4(Z)`.
- By MdlS Theorem 1.1 (`sl4z-representations-have-sl2-invariant-vectors`), `rho` fixes a
  nonzero vector under the block `SL_2(Z)`, so `||rho(z)|| = 4`.
- Hence `||sigma(z)|| >= ||sigma(z) sigma(p_rho)|| = ||z p_rho|| = 4`, and
  `||sigma(z)|| <= 4` always.
- On a Hilbert space, `sigma(p_rho) H` is a nonzero `rho`-isotypic subspace, and it
  contains the fixed vectors of `rho`.

**Consequence for (C).**
- A corona representation with `||pi(z)|| < 4` must have column unipotent spectrum `T^3`.
- Every MF embedding already has this property, since `lambda` restricted to `Z^3` has
  Haar spectrum.
- So the congruence mechanism of Magee--de la Salle covers exactly the corona
  representations the MF question never meets.  The crux
  `sl4z-corona-representations-have-block-sl2-norm-four` is equivalent to its
  full-spectrum case.

## 3. The Step 3 firewall

Claim `mdls-averaging-at-non-torsion-character-gives-spectral-gap`, whose proof is in its
route.
- Realize a full-spectrum corona representation faithfully on a Hilbert space.
- The spectral measure of `A = {[0;y;z]}` (entries `(2,4)` and `(3,4)`) splits into atoms
  at torsion points, atoms at non-torsion points, and a continuous part.
- The `G`-span of the eigenspaces at non-torsion atoms is weakly contained in
  `lambda_SL2(Z)`, where `G` is the coordinate-`(2,3)` block `SL_2(Z)`.  That block is
  conjugate to the upper-left block by a signed permutation, so the norms agree.
- Therefore norm four must come from torsion atoms or from the continuous part.
- The firewall does not extend to the continuous part.  Take `Z^2 x| SL_2(Z)` acting on
  `l^2(Z^2)` by translations and linear maps.  `Z^2` has Haar spectrum, yet `delta_0` is
  an `SL_2(Z)`-fixed vector.

## 4. Where the crux stands

**Handled.**
- Finite unipotent spectrum: Theorem B.
- Eigenvectors at non-torsion characters: firewall, which gives only spectral gap.

**Open.**
- The full spectrum, with norm four coming from torsion atoms of unbounded level or from
  the continuous part.
- At a torsion atom of level `p^r` inside a full spectrum, Step 3's finite average needs
  the eigenvector to be invariant under the `SL_2(Z)`-stabilizer of the character.  That
  stabilizer contains the principal congruence subgroup of level `p^r`.  In a
  representation that factors through no finite quotient, nothing supplies this.

**Tool noted, not developed.**  The corona is countably degree-1 saturated
(Farah--Hart; standard, not re-read).  It gives nonzero fibre elements annihilating
`C_0(T^3 \ {theta})` and commuting with the stabilizer of `theta`, using log-radial bump
functions, which are almost invariant under finitely many linear maps.  They do not give
the missing congruence invariance.

**Sharpest next target.**  Decide the crux in the full-spectrum case.  A refutation would
be an asymptotic homomorphism of `SL_4(Z)` that is not near any genuine representation,
with a spectral gap for the block `SL_2`.  By part 1, Theorem 3, it would also refute
`sl4z-matricially-stable`: a non-stability theorem for a group whose rational cohomology
lies in degrees `0` and `3`, which is outside Dadarlat's even-degree obstruction.  That
cohomology computation is unverified here.
