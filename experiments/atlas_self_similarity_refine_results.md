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
