# Thompson V: exact presentation check and numerical model probes

Date: 2026-09-12. Lane `nh-thompson-v`. All computation ran on MSI (acn112),
using the code in `experiments/thompson-v-models/`.

## 1. The presentation, checked exactly

Bleak--Quick, arXiv:1511.02123v2, Theorem `thm:2gen-KB`: `V` has generators
`u = t_(00,01) t_(10,110) t_(10,111)` and `v = (01 10 11)`. The convention is
the right action with `t^s = s^-1 t s`. The seven relators are copied verbatim
from the TeX source into `presentation_bq2.json`:

```text
u^6, v^3, (u^3 v)^4, and four long relators (lengths 69, 31, 25, 35).
```

`verify_bq2.py` evaluates each relator on every binary string of length 12
under prefix substitution:

- all seven relators are the identity of `V`;
- `u` has order 6 and `v` has order 3;
- `u^3 = t_(00,01)`, and `(u^3)^(v u^-1 v u^3 v) = t_(11,001)`, as stated in the
  corollary `cor:2gen-Tietze`;
- **erratum:** the displayed formula `t_(10,000) = (u^3)^(v u^-2 v u^3)` is false
  under the paper's own conventions. Only the relators and the other two
  formulas are used here.

With the orientation of `v` reversed, four relators fail, so the reading is
pinned down.

## 2. Normalized-HS probe (`hs_probe.py`)

**Setup.**

- `u = W_u D_6 W_u^*` and `v = W_v D_3 W_v^*`, with balanced spectra of 6th and
  3rd roots of unity. So `u^6 = v^3 = 1` hold exactly, every power of `u` and of
  `v` is traceless, and `a = u^3` has squared normalized HS energy exactly `2`.
- **Loss:** the mean over the five remaining relators of
  `||r - I||_2^2 = 2 - 2 Re tr(r)/d`.
- **Optimizer:** Riemannian gradient descent on `W_u, W_v` in `U(d)`, with
  exact gradients and adaptive steps.

A model of small defect here is a model of `V` that is far from trivial on the
marked word. By `thompson-v-ce-one-word-trace-face-is-binary`, a family with
defect tending to `0` would be the signal for hyperlinearity.

**Results.** Best of the runs, 1200--2000 iterations each. A random start gives
a max defect of about 1.41 and a mean squared defect of about 2.

| d | runs | max relator HS defect | mean squared defect |
| --- | --- | --- | --- |
| 6 | 3 | 1.17--1.28 | 0.62--0.99 |
| 12 | 3 | 1.18--1.19 | 0.79--1.00 |
| 24 | 3 | 1.15--1.16 | 0.80--0.87 |
| 36 | 2 | 1.14--1.17 | 0.82--0.86 |
| 48 | 5 | 1.14--1.16 | 0.76--0.84 |
| 72 | 2 | 1.15--1.16 | 0.78--0.81 |

Test words that are not powers of generators (`[u,v]`, `uv`, `u^3 v`) keep
energies near `2` at the optimum. The optimized models look generic, not
structured.

## 3. Permutation probe (`perm_probe.py`)

**Setup.** `u` is conjugate to a product of 6-cycles and `v` to a product of
3-cycles, so `u^6 = v^3 = 1` exactly and `a = u^3` is fixed-point-free.
Simulated annealing over the conjugators minimizes the mean proportion of points
moved by the five remaining relators.

**Results** (40000 steps):

| n | best cost |
| --- | --- |
| 36 | 0.54 |
| 72 | 0.57 |
| 144 | 0.70 |

In each case `(u^3 v)^4` and the relator of length 25 are satisfied exactly,
and the relators of lengths 69, 31 and 35 move 78--100% of points.

## 4. What this does and does not show

- There is no signal toward hyperlinearity or soficity: no near-solutions
  appear at `d <= 72` or `n <= 144`.
- There is no evidence for a quantitative ceiling either. The HS plateau does
  not decay with `d`, but the optimizer has not been calibrated. It was never
  run on a presentation with known exact far-from-trivial solutions. Its
  plateau may be a local-descent artifact, and first-order descent from Haar
  starts is exactly the kind of search a structured model family could evade.
- The next useful computation is a calibration: run the same parametrization
  on a finite group whose regular representation is an exact solution, and
  check that descent finds it. Only then can the plateau be read.
