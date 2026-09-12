# Finite-order boundary geodesic results

Date: 2026-08-11

## Target

The radius-five atlas window has two exact regular-representation endpoints:

* tensor flip (J) kills 27,022 of the 27,256 collision-tree words and
  fails on the 234-word boundary;
* the unique inner wall alignment (L_k) kills all 234 boundary words and
  20,628 of the tensor-flip controls, but fails on 6,394 controls.

For the coordinate-reversal involution (k), put

\[
 D=J^*L_k.
\]

Exact permutation arithmetic gives (D^4=1).  Every square root (F^2=D)
is therefore a degree-three polynomial in (D).  Up to a global scalar there
are eight spectral sign branches.  The structured midpoint model is

\[
 U=JF.
\]

`atlas_boundary_geodesic.py` evaluates these branches implicitly on the
20,160-dimensional regular space.  It uses only four permutations per
polynomial application and never forms a dense regular matrix.

## Balanced signal run

The bounded run used eight evenly spaced boundary words, eight evenly spaced
wall-failure words, four words killed by both endpoints, and one deterministic
Hutchinson probe.  Endpoint calibration behaved as required: each endpoint
had zero measured projective loss on the constraints it solves and loss
within (10^{-4}) of one on its exposed set.

All eight square-root branches were destructive.  Across the branches:

| constraint stratum | mean projective loss |
|:---|:---|
| 234-word boundary sample | `0.993708` to `0.994668` |
| 6,394 wall-failure sample | `0.967634` to `0.969161` |
| 20,628 shared-control sample | `0.830121` to `0.892257` |

The best observed maximum loss was `0.998676`.  The smallest sampled trace
moduli were between `0.00105` and `0.0364`.  Thus no branch even weakly
interpolates the two endpoints: it sends typical tested words close to trace
zero, including words solved by both endpoints.

This is numerical evidence, not an exact lower bound.  It is nevertheless
strong enough to stop this finite family.  The branch set is exhaustive for
square roots which are functions of the single order-four operator (D), so
additional seeds or a denser sample would not change the ansatz.  A future
interpolation would need extra noncommuting directions or multiplicity
coupling; it should not use another spectral branch of (J^*L_k).

Reproduce the bounded run with

```text
python3 experiments/atlas_boundary_geodesic.py \
  --boundary-samples 8 --wall-failure-samples 8 \
  --shared-samples 4 --probes 1
```
