---
rg: 2
id: hexagon-flux-is-adjacent-level-weil-ratio
kind: claim
title: The S3 hexagon flux on flat towers equals the adjacent-level ratio of Weil classes, hence the Legendre class of the prime
distinct_from:
  lambda-exact-face-closes-at-p-three: that consumes the flux value through the capstone assembly; this is the dictionary LEMMA itself -- the identification of the hexagon comparison scalar with computable Gauss-class arithmetic -- isolated so the capstone's cited-level dependency becomes one precisely-shaped statement.
  two-adic-tower-format-of-surviving-lambda-exact-enemy: that pins the format of the tower data (interlocked depth-shifting transports, forced Haar marginals); this evaluates the obstruction cocycle OF that format on oscillator bands, turning the format's one free joint-realization parameter into an arithmetic constant.
---

Claim (the dictionary lemma).  Let p be odd and consider the flat
multi-scale tower of a surviving Lambda-exact enemy of the collapse
at the pair `(SL_3(Z), SL_3(Z[1/p]))`, with its three interlocked
transports `V_h, V_h', V_h''` satisfying `V_h = V_h' V_h''` on
oscillator bands (irreducible Heisenberg components with faithful
central character).  Then the canonical-transport comparison scalar
(the hexagon flux) equals the ratio of the canonical metaplectic
normalization classes at adjacent congruence levels of the
`(e_12, e_23)` polarization pair, and this ratio is

```text
flux = (-1 | p)  =  -1 for p = 3 mod 4,   +1 for p = 1 mod 4.
```

MECHANISM.  (i) Each one-level leg (`h'`, double weight on `e_23`;
`h''`, double weight on `e_12`) factors through the Stone--von
Neumann model polarized at its OWN double-weight direction, where it
acts as a positive-kernel scaling operator -- canonical with no
Gauss factor.  (ii) Composing legs of different polarizations
inserts the canonical intertwiner `F` (the Gauss-normalized partial
Fourier transform between the two polarized models) at the meeting
level.  (iii) The two-level `h`-leg is polarization-agnostic:
`Ad(h)` scales both root directions equally, so its transport is the
same positive scaling in either model and contributes no class.
(iv) The closed hexagon `V_h^* V_h' V_h''` therefore reduces to a
conjugation by `F` at level `a` against a conjugation by `F` at
level `a - 1`: an adjacent-level ratio of Weil classes.  (v) The
classes are MEASURED, witness-clean (artifact
`svn-pinning-derivation-2026-08-21`, section C'): the canonical
class at level q obeys the exact Gauss arithmetic
(`A(1) = (2|q) eps_q`, `A(+1)/A(-1) = (-1|q)` at seven levels), and
the adjacent-level ratio of `(-1|q)` is the CONSTANT `(-1|p)` --
alternation at `p = 3 mod 4` (Jacobi squares cancel at even levels),
triviality at `p = 1 mod 4`.

## Attempts

- **What is proved versus derived versus measured.**  Steps (iv)-(v)
  are arithmetic, machine-verified at seven levels with all
  intertwining witnesses at 1e-15 and the no-anomaly control
  `F^4 = 1`.  Steps (i)-(iii) constitute the derivation obligation:
  the polarization-factoring of the leg transports.  The
  double-weight computation behind (i) is exact (`Ad(h')` weights
  `(-1, +2, +1)` on `(e_12, e_23, e_13)`, `Ad(h'')` weights
  `(+2, -1, +1)`, `Ad(h)` weights `(+1, +1, +2)`), and (iii) is the
  statement that equal scaling of both legs commutes with every
  polarization choice -- the two clean halves.  The single remaining
  obligation is (ii): that the canonical multiplicity cut of the
  SvN decomposition matches the Gauss-normalized `F` and not some
  other section; this is exactly where the naive instruments failed
  and where the verified-primitive calculus now supplies the
  operators explicitly.
- **Consequence chain.**  With this lemma the capstone
  `lambda-exact-face-closes-at-p-three` loses its last cited-level
  dependency of substance: coprime levels (Weyl slot, proved) +
  regular type (Kazhdan floor, proved) + flat remainder (shift
  invariance, proved) + THIS lemma (flux = -1 at p = 3) close the
  entire Lambda-exact face, and `(RC3-p3)` becomes exactly the
  uniform-outlier exclusion -- the lane's single wall, now attacked
  through the extreme-point compression.
- **Two-sided check at p = 2.**  The same mechanism with the
  level-8 quadratic characters of the 2-adic metaplectic theory
  gives trivial ratio (all 2-power symbols +1), consistent with the
  constructive-side reading of the p = 2 pair and with every
  historical closure failure at 2 -- the dictionary explains the
  failure pattern rather than merely avoiding it.
