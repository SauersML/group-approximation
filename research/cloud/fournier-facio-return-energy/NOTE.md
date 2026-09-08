# A return-energy obstruction for common-block models

## Question and choice of lane

The target is the hyperlinearity of the torsion-free nonsofic group constructed
by Francesco Fournier-Facio in *A torsion-free non-sofic group*,
[arXiv:2608.02025v2](https://arxiv.org/abs/2608.02025). This note takes the
negative, tracial branch. It does **not** decide that target.

The repository already reduces a positive answer, in the common-block model,
to a singular invariant charge concentrated at block dimension infinity. It
also proves that on a positive-charge family of blocks some nontrivial actor
has Haar spectral law and wandering columns. The point here is to replace
the qualitative recurrence argument by a dimension-sensitive inequality. It
gives an explicit amount of return energy which every finite block that is
too small must pay.

Before choosing this route I checked the other two live candidates. The
binary-Leavitt Atlas route has already been reduced to a shared-reservoir
authentication problem after all bounded prefix tests, while the Kun--Thom
route requires an extrinsic relative-commutant cocycle corrector. Both need
new simultaneous constructions. The argument below is useful on the
Fournier--Facio lane because it is a genuinely tracial, basis-column estimate.

## Finite-dimensional theorem

Let \(U\in U(d)\), let \(e\) be a unit vector, and put
\[
 a_k=\langle U^k e,e\rangle,\qquad
 E_N(U,e)=\sum_{k=1}^{N}(N+1-k)|a_k|^2.
\]

### Theorem 1 (local return-energy bound)

For every \(N\geq 0\),
\[
 d\ \geq\ { (N+1)^2\over (N+1)+2E_N(U,e)}.                 \tag{1}
\]
Equivalently, when \(d<N+1\),
\[
 E_N(U,e)\ \geq\ {(N+1)(N+1-d)\over 2d}.                  \tag{2}
\]
In particular, if \(|a_k|\leq\varepsilon\) for \(1\leq k\leq N\), then
\[
 d\geq {N+1\over 1+N\varepsilon^2}.                       \tag{3}
\]

#### Proof

Set \(v_i=U^i e\), \(0\leq i\leq N\), and let \(G\) be their Gram matrix.
Then \(G\geq0\), \(\operatorname{rank}G\leq d\), and
\(\operatorname{Tr}G=N+1\). If
\(\lambda_1,\ldots,\lambda_r\) are its nonzero eigenvalues,
Cauchy--Schwarz gives
\[
 (N+1)^2=(\sum_i\lambda_i)^2
 \leq r\sum_i\lambda_i^2
 \leq d\operatorname{Tr}(G^2).                            \tag{4}
\]
Since \(G_{ij}=\langle U^j e,U^i e\rangle\), its absolute value depends
only on \(|i-j|\), and therefore
\[
 \operatorname{Tr}(G^2)
 =(N+1)+2\sum_{k=1}^{N}(N+1-k)|a_k|^2.
\]
Substitution in (4) proves (1). Rearranging proves (2). Finally
\(2E_N\leq N(N+1)\varepsilon^2\), which substituted in (1) proves (3).
This is the elementary Gram-matrix argument underlying the Welch bound;
see L. R. Welch, “Lower bounds on the maximum cross correlation of signals,”
*IEEE Transactions on Information Theory* 20 (1974), 397–399,
[DOI 10.1109/TIT.1974.1055219](https://doi.org/10.1109/TIT.1974.1055219).
No external result is needed for the proof above. ∎

### Corollary 2 (small blocks have a return-energy tax)

Suppose \(X=\bigsqcup_y X_y\) is partitioned into finite blocks, \(U\)
preserves every \(\ell^2(X_y)\), and \(d(x)=|X_y|\) for \(x\in X_y\). Set
\[
 R_N(x)=\sum_{k=1}^{N}(N+1-k)
       |\langle U^k\delta_x,\delta_x\rangle|^2.
\]
For every \(D\leq N\), pointwise on \(\{x:d(x)\leq D\}\),
\[
 R_N(x)\geq {(N+1)(N+1-D)\over2D}.                        \tag{5}
\]
Hence for every finitely additive probability charge \(\mu\) on \(X\),
\[
 \int_X R_N\,d\mu\geq
 {(N+1)(N+1-D)\over2D}\,\mu\{d\leq D\}.                  \tag{6}
\]

#### Proof

Apply (2) in the block containing \(x\). The right side decreases with
\(d\), proving (5). Integration of the nonnegative simple lower bound proves
(6); only finite additivity is used. ∎

This is quantitative even for a purely finitely additive charge. Countable
additivity, dominated convergence, and a choice of a recurrent power
depending on the block are not hidden in the argument.

## Application to the Fournier--Facio survivor

Use the repository's common-block notation. On the positive fixed-block
sector \(F\), let \(U=P_FB_gP_F\), let \(d(x)\) be its block dimension, and
normalize the charged state to a probability charge \(\nu\). The established
wandering statement says, for fixed \(k\ne0\) and every \(\varepsilon>0\),
\[
 \nu\{x:|\langle U^k\delta_x,\delta_x\rangle|
                 \geq\varepsilon\}=0.                    \tag{7}
\]
Only finitely many powers occur in \(R_N\). Outside a finite union of null
sets it is at most \(N(N+1)\varepsilon^2/2\), while always
\(R_N\leq N(N+1)/2\). Thus
\[
 \int_F R_N\,d\nu=0.                                      \tag{8}
\]
Combining (6) and (8), with \(N=D\), recovers the known conclusion
\[
 \nu\{x:d(x)\leq D\}=0\quad(D\geq1).                      \tag{9}
\]
More importantly for approximate constructions, return energy at most
\(\eta\) implies
\[
 \nu\{d\leq D\}\leq
 {2D\eta\over (N+1)(N+1-D)}\qquad(D\leq N).               \tag{10}
\]

This is the new reduction: any proof that the compression relations force a
positive charged mass of blocks of dimension at most \(D\), even only
quantitatively along microstates, contradicts regular-character return
energy by (10). It suffices to establish tightness at scales
\(D_N\leq(1-c)(N+1)\) while the corresponding energy is
\(o(N^2/D_N)\).
No common recurrent exponent need be selected.

## Concrete tests and sharpness

The accompanying Python script evaluates the formula exactly over the
rationals for permutation-cycle unitaries.

* **Calibration:** for a cycle of length \(d\), \(a_k=1\) exactly when
  \(d\mid k\). At \(N=d-1\), (1) is equality.
* **Different case:** at \(d=3,N=4\), only \(a_3=1\), so \(E_N=2\).
  Formula (1) gives \(d\ge25/9\), which dimension \(3\) satisfies.
* At \(d=2,N=5\), returns occur at powers \(2,4\); the verifier gets
  \(E_N=6\) and checks both (1) and (2).

Cycles also show why this cannot close the problem: taking \(d>N\) makes all
first-\(N\) returns zero. A singular charge concentrated on cycle lengths
tending to infinity attains every fixed return constraint. Another marginal
moment estimate cannot finish this lane.

## Exact open residue

**OPEN — simultaneous compression tightness.** In every common-block,
purely singular amenable near representation of the Fournier--Facio group
with regular character, do its two compression relations force constants
\(c>0\) and scales \(N_j\to\infty\), \(D_j\leq(1-c)(N_j+1)\), such that
\[
 \limsup_j\nu\{d\leq D_j\}>0
 \quad\text{and}\quad
 \int R_{N_j}\,d\nu=o(N_j^2/D_j)?
\]
The second condition follows from sufficiently uniform regular-character
control; the first is the genuinely simultaneous assertion and is not
proved. It must use coupling to the other generators and compressors. The
cyclic examples refute deriving it from torsion-freeness, Haar marginal law,
or null boundary alone.

## Status

* **PROVED:** Theorem 1, Corollary 2, quantitative tail estimate (10), and
  the exact cycle computations in the accompanying script.
* **CONDITIONAL:** Applied to the repository's established common-block
  reduction and wandering-column theorem, the result rederives dimension
  escape. If simultaneous compression tightness holds, no common-block
  Fournier--Facio hyperlinear witness exists.
* **OPEN:** simultaneous compression tightness; exclusion of overlapping or
  infinite-component models; hyperlinearity of the Fournier--Facio group;
  and both global existence questions. No claim here proves a non-hyperlinear
  group or a hyperlinear nonsofic group.
