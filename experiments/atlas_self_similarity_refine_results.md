# Relative-unitary continuation of the self-similarity phase

Date: 2026-08-11

## Question

For the first all-depth survivor

\[
r=a_2b_1c_2b_1a_2b_1c_2(cb)_1,
\]

keep both chart marginals equal to the honest 64-dimensional $A_8$-irrep
$W=(5,2,1)$, and vary only their relative unitary $U\in U(64)$. Can one
simultaneously make $r(U)$ nontrivial and make it commute with the twelve
standard transvection generators of the two charts?

`atlas_self_similarity_refine.py` uses exact cyclic derivatives and Cayley
retractions. Its scalar objective is

\[
 {1\over |J|}\sum_{j\in J}
 \Re\operatorname{tr}_{64}([s_j,r(U)])
 -\lambda\Re\operatorname{tr}_{64}(r(U)),            \tag{1}
\]

where $J$ is either all twelve constraints or a periodically refreshed worst
tail. Thus the second term rewards normalized Hilbert--Schmidt distance from
the identity rather than imposing a guessed target phase.

## Reproducible continuation

First generate the lowest-RMS exact complement:

```text
sage -python experiments/atlas_self_similarity_block.py \
  --save-best phase-best.npy
```

Then run the decisive worst-tail continuation:

```text
sage -python experiments/atlas_self_similarity_refine.py \
  --init phase-best.npy --weights 0.2 --iterations 600 \
  --centrality-batch 6 --focus-every 3 \
  --save-prefix phase-best-focus

sage -python experiments/atlas_self_similarity_refine.py \
  --init phase-best-focus-w0.2.npy --weights 0.2 --iterations 450 \
  --centrality-batch 8 --focus-every 3 \
  --save-prefix phase-structure
```

The runs used four BLAS threads. Each was bounded and completed in less than
one minute. No random restart was used.

## Signal

| state | max centrality defect | RMS defect | normalized trace of $r$ |
|---|---:|---:|---:|
| exact local seed | 1.250000 | 0.822851 | $0.5i$ |
| six-tail, 100 steps | 0.746916 | 0.679461 | $-0.00168+0.78072i$ |
| six-tail, 200 steps | 0.469242 | 0.395817 | $-0.00083+0.92941i$ |
| six-tail, 600 steps | 0.333204 | 0.293748 | $-0.00503+0.96186i$ |
| eight-tail, 150 steps | 0.069685 | 0.054663 | $7.6\cdot10^{-8}+0.999353i$ |
| eight-tail, 300 steps | 0.051057 | 0.040086 | $6.8\cdot10^{-9}+0.999656i$ |
| eight-tail, 450 steps | 0.029580 | 0.023307 | $2.4\cdot10^{-9}+0.999882i$ |

An independent guarded run reached maximum defect $0.023597$ at step 500
before its timeout. Its final matrix was not saved, so the retained step-450
state is the reproducible artifact.

For that retained state,

\[
 \|r(U)-iI\|_2=0.0153837,
 \qquad
 \|r(U)-iI\|_{\mathrm{op}}=0.0423631.               \tag{2}
\]

All 64 eigenphases lie between $1.52843$ and $1.61313$, tightly around
$\pi/2$. The relative unitary itself is not a small perturbation of the exact
seed: its normalized Hilbert--Schmidt displacement is $0.78677$, and its
entries are dense. Therefore the solver has not merely polished the original
local block; it has found a genuinely global alignment.

## Meaning and next gate

This does not yet prove that an exact $U$ with $r(U)=iI$ exists. It is,
however, qualitatively different from the earlier atlas plateaus: both the
full-chart defect and the scalar-phase error decrease together, by almost two
orders of magnitude, in one fixed dimension. Since $iI$ commutes with both
irreducible chart images automatically, the numerical problem has collapsed
to the exact matrix equation

\[
 r(U)=iI_{64}.                                       \tag{3}
\]

The next work should be structure extraction and exact solving near the
retained state: compute the tangent rank of `(3)`, project with a
Newton/Levenberg step, and identify an algebraic block model. More blind seed
or weight sweeps are lower value.

Solving `(3)` exactly would certify a nontrivial central phase after
centralizing the normal closure of this one relator. It would not by itself
prove that the class survives in the smaller quotient $R/[P,R]$, because
commutators involving the other Leavitt relators could still kill it. That
multi-relator central-kernel gate and the downstream negative-corner
construction remain separate.

## Local polishing and conditioning

`atlas_self_similarity_newton.py` exports the Sage representation matrices
once, then uses the existing CPU PyTorch installation to minimize
$\|r(U)-iI\|_2^2$ over one exponential tangent chart. Repeated L-BFGS restarts
gave:

| stage | $\|r-iI\|_2$ | $\|r-iI\|_{\rm op}$ |
|---|---:|---:|
| retained Cayley state | $1.5384\cdot10^{-2}$ | $4.2363\cdot10^{-2}$ |
| 40 L-BFGS closures | $2.6773\cdot10^{-3}$ | $6.5326\cdot10^{-3}$ |
| 208 more closures | $5.0521\cdot10^{-4}$ | $1.4157\cdot10^{-3}$ |
| 1,251 more closures | $2.4993\cdot10^{-4}$ | $6.7466\cdot10^{-4}$ |
| 2,002 more closures | $2.4381\cdot10^{-4}$ | $6.6225\cdot10^{-4}$ |

The final restart improved only slowly, so this is not merely stale L-BFGS
history. `atlas_self_similarity_gauss_newton.py` independently applies the
exact tangent Jacobian and adjoint with matrix-free LSMR. Its random adjoint
identity check passed with relative error $1.2\cdot10^{-16}$. Four
200-iteration inner solves reached $1.4266\cdot10^{-4}$, and two
1,000-iteration solves reached

\[
 \|r-iI\|_2=1.11046\cdot10^{-4},\qquad
 \|r-iI\|_{\rm op}=2.82906\cdot10^{-4}.             \tag{4}
\]

Every inner solve hit its Krylov iteration cap. This is evidence for a very
ill-conditioned tangent problem, not evidence that the residual is zero.
Further floating-point polishing has sharply diminishing value until the
exact structure below is used.

## Exact square-root reduction

Write

\[
 A=\rho_U(a_2),\quad E=\rho_U(c_2),\quad
 B=\rho(b_1),\quad C=\rho(c_1).
\]

Here $A,E$ are commuting involutions with four joint eigenspaces of dimension
16, while $B,C$ generate the fixed $D_8$ restriction. Put $T=ABE$. Then

\[
 r=TBT\,CB.
\]

Consequently

\[
 r=iI
 \quad\Longleftrightarrow\quad
 TBT=iBC
 \quad\Longleftrightarrow\quad
 (BT)^2=iC.                                         \tag{5}
\]

Since $BT=BABE$, the exact problem is to factor a square root of the fixed
operator $iC$ as

\[
 Y=BABE,\qquad Y^2=iC,                               \tag{6}
\]

subject to the joint-multiplicity constraint on $A,E$. In particular $Y$
must commute with $C$. On the $C=+1$ eigenspace its eigenvalues lie in
$\{\pm e^{i\pi/4}\}$, and on the $C=-1$ eigenspace they lie in
$\{\pm e^{-i\pi/4}\}$. This finite spectral-factorization problem is the
right target for exact character and projector analysis. It replaces further
blind optimization.

A bounded GAP size query for the corresponding four-involution central-phase
presentation did not finish; only its abelianization $C_2^4$ was returned.
Do not enlarge that raw coset enumeration without first exploiting `(5)`.

Finally, all restriction multiplicities have a common factor eight. The
64-dimensional data is eight copies of a minimal 8-dimensional package:

\[
 W|_{D_8}/8=2\tau\oplus\!\bigoplus_{\chi\in\widehat{D_8}^{(1)}}\!\chi,
 \qquad
 W|_{V_4}/8=2\!\bigoplus_{\psi\in\widehat{V_4}}\!\psi. \tag{7}
\]

Therefore an exact 8-dimensional solution amplifies directly to dimension
64. `atlas_self_similarity_block8_search.py` instantiated this canonical
package without Sage. All eight independent starts converged in 1.3 seconds
total to $\|r-iI\|_2<3.3\cdot10^{-8}$; the best error was
$1.29\cdot10^{-8}$.

## Exact 8-dimensional construction

The minimal numerical solution exposed a signed-permutation construction.
Use the canonical basis $0,\ldots,7$ from the block-eight search. Let

\[
 S=(0\ 7)(1\ 6)(2\ 5)(3\ 4),\qquad
 P=(0\ 6)(2\ 4)(3\ 5)(1\ 7),                       \tag{8}
\]

and put

\[
 F={I+iC\over\sqrt2},\qquad A=BPB,\qquad E=PSF.    \tag{9}
\]

Direct permutation calculation gives

\[
 P^2=S^2=1,\quad PC=-CP,\quad PS=SP,\quad SC=CS.   \tag{10}
\]

It follows that $PFP=F^*$, hence $E$ is a self-adjoint involution. A second
direct calculation gives

\[
 [A,E]=0,\qquad
 \operatorname{Tr}(A)=\operatorname{Tr}(E)
 =\operatorname{Tr}(AE)=0.                          \tag{11}
\]

The four joint eigenspace ranks are therefore

\[
 {1\over4}\operatorname{Tr}((1\pm A)(1\pm E))=2,   \tag{12}
\]

so $(A,E)$ is exactly two copies of the regular $V_4$ representation. Finally,

\[
 BABE=PE=SF,\qquad (SF)^2=F^2=iC.                  \tag{13}
\]

Using the equivalence `(5)`, the survivor relation is exactly

\[
 r=iI_8.                                            \tag{14}
\]

`atlas_self_similarity_block8_exact.py` verifies every identity in
`(8)--(14)` exactly over $\mathbb Q(\zeta_8)$. Since the two restrictions of
the 64-dimensional $A_8$ irrep are eight copies of the canonical packages,
eightfold amplification gives a relative alignment of two honest $A_8$
charts for which $r=iI_{64}$ exactly.

This completes the one-relator phase gate. It still does not prove that $r$
survives in $R/[P,R]$: centralizing the other Leavitt relators can add new
relations. The next computation must incorporate representatives of those
other relators or prove the multi-chart central-kernel survival algebraically.
