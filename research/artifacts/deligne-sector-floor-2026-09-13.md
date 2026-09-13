# Exponents between Frobenius and normalized HS for the Deligne sector (lane ex2-nh-deligne-sector-floor, 2026-09-13)

Status: commentary, unreviewed. Established statements live in the nodes named in Section 0; everything
else here is analysis, heuristics, or where approaches die.

Notation. `g >= 2`, `Gamma = Sp_(2g)(Z)`, `Gamma~` its universal-cover preimage with covering generator `z`,
`Gamma_n = Gamma~/<z^n>`, `zeta = exp(2 pi i theta)` with `zeta^n = 1` and `zeta^2 != 1`. A *sector tuple* is
`rho : S cup {z} -> U(d)` with `rho(z) = zeta I`; `X_r = rho(r) zeta^(-k_r) - I` are its relator defects.
`sigma(d)` is the least `max_r ||X_r||_HS` in dimension `d` (normalized), and `F(d) = d^(1/2) sigma(d)` is its
unnormalized Frobenius form.

## 0. Landed

| node | status | content |
| --- | --- | --- |
| `deligne-cover-sector-floor-below-exponent-one-half` | open | `(SF1)`: `sigma(d) >= c d^(-b)`, some `b < 1/2`, at `g >= 3` |
| `deligne-monomial-cover-models-have-a-detecting-cycle-floor` | established, unreviewed | monomial models over exact quotients: `max_r eta_r >= 4 nu / A_0(N)`, every genus |
| `sp2g-universal-cover-lattice-is-operator-hs-stable` | open | BDL Conjecture 1.8 for `Gamma~_g`, `g >= 3` |
| `deligne-sp2g-covers-mf-radical-is-2z-at-genus-three` | open, conditional route | `Rad_MF(Gamma_n) = <z^2>` for `g, n >= 3` |
| `deligne-sp2g-covers-not-mf-from-operator-hs-stability` | route | one application of Conjecture 1.8 through the quotient map |

## 1. The profile and the ladder of rungs

**Monotone profile.** `sigma(dm) <= sigma(d)` (tensor with `1_m`), and `sigma(D)^2 <= sigma(d)^2 + 4d/D`
(direct sum with a remainder block). So `sigma` is essentially non-increasing, `F^2` is subadditive, and
`F(d) <= 2 d^(1/2)`. Non-hyperlinearity of `Gamma_n` is `F(d) >~ d^(1/2)`.

**Rungs, weakest first.**
- I0: `F(d) >= delta_n` (established at `g >= 3`, Frobenius stability).
- I1: sector tuples with rank-`<= k` defects live in bounded dimension.
- I2: `F(d) -> infinity`.
- I3: `F(d) >= c d^(1/2 - b)`, some `b < 1/2`, i.e. `(SF1)`.
- I4: `F(d) >= c d^(1/2)`, the goal.

Implications: `I4 => I3 => I2 => I1`. Nothing on main derives `I1` from `I0`. The crux of every rung above `I0` is
the same hypothetical object: a tuple whose defect has a bounded number of `O(1)` singular values and is
operator-small elsewhere. Frobenius stability needs the `O(1)` part below `delta_n` and cannot see it.

**Microstate dimension form.** `(SF1)` says that an `eta`-microstate on a fixed window needs
`d >= (c/eta)^(1/b)`: a *superquadratic* dimension lower bound, against the established quadratic
`d >= (delta_n/eta)^2`.

## 2. Why dimension-free Schatten inputs cannot beat exponent 1/2

Let a stability theorem give, for every tuple in every dimension, `||X_r||_p >= delta_p` in an
*unnormalized* Schatten norm.
- **For `p >= 2`.** `||X||_2 >= ||X||_p`, so `||X||_HS >= delta_p d^(-1/2)`.
- **For `p < 2`.** `||X||_HS >= d^(-1/p) ||X||_p`, which is worse.

So any dimension-free Schatten-scale input gives at best exponent `1/2`. The same holds for linear-rate
Frobenius stability below a fixed threshold `delta_0`: a tuple with `eta d^(1/2) > delta_0` is simply outside
its range. To reach `b < 1/2` one needs one of three things:
1. stability valid at Frobenius defects that *grow* with `d`, e.g. `dist_F <= K def_F` whenever
   `def_F <= d^a`, which gives `b = 1/2 - a`;
2. a supply of many almost-independent tests, one per unit of dimension;
3. operator-norm control of corrections.

Section 3 is a case of (2); Section 4 is (3).

## 3. Monomial models: an abelian supply of tests

**The floor.** For a monomial model over `X = Gamma/N`, `N` normal, the phase curvature `c = delta a - theta k
mod Z` is quantized on every integral 2-cycle: `<c, Sigma> in -theta <k, Sigma> + Z`. The `d` deck translates
of one detecting cycle give `d` tests, which yields `(MCF1)`, `max_r eta_r >= 4 nu / |Sigma|_1`. Details are in
the node's proof route.

**Hodge form of the problem.** On the 2-complex `Y = Y_(Gamma/N)`,

```text
sum_r eta_r^2  ~  (1/d) min_(a real, m integer) || beta + delta a - m ||_2^2
             =  (1/d) dist^2( P beta, P(Z^(cells)) ),    P = projection onto Z_2(Y; R).
```

So the minimal defect is a lattice-distance problem in the real 2-cycle space. Detecting cycles are dual
lattice vectors, and `(MCF1)` is the elementary transference bound, amplified by deck symmetry.

**Conditional dimension-free or `d^(-1/4)` floor (commentary, two hypotheses).** Let `Y^(3)` include finitely
many 3-cells killing `pi_2` (`Gamma` is of type `F_infinity`).
- (IF) **Integer cosystolic filling, uniform over normal covers.** For integer 2-cochains `m`, some integer
  `n` has `delta n = delta m` and `||n||_1 <= K ||delta m||_1`.
- (B) `H^2(N; R) = R [k]` for the normal subgroups used (Borel's stable range; the exact range at small `g`
  is not checked here).

Sketch.
- Write `delta a - beta = c + m`. Then `delta m = -delta c` is integer-valued with support at most
  `C ||c||_2^2`, so `||delta m||_1 <= C' ||c||_2^2`.
- (IF) gives an integer cocycle `m' = m - n`, and `c' = c + n` is a real cocycle with
  `[c'] = -theta [k] - [m']`.
- By (B) and Deligne (`3` never divides the index of the integral lattice in `R [k]`; indeed it is `1` or
  `2`), `|coefficient of [k] in [c']| >= dist(theta, (1/2)Z)`.
- The harmonic norm of pulled-back `k` scales like `d^(1/2)`. Hence
  `nu' d^(1/2) h_0 <= ||c||_2 + K C' ||c||_2^2` with `||c||_2 <~ (|R| d)^(1/2) eta`.
- Conclusion: `eta >~ d^(-1/4)`, and a dimension-free floor if the filling also has bounded entries.

Real filling from `[T_2]` does not suffice: it loses integrality, and integrality is the whole content.
(IF) is the HS-row analogue of the cosystolic inequality that Gohla--Thom need for soficity, known only for
p-adic buildings.

**Heuristic exponent for congruence quotients (not checked).**
- Cocompact arithmetic surface subgroups (norm-one units of an indefinite rational quaternion algebra) sit
  in `Sp_4` through left multiplication, with Toledo invariant twice the Euler number.
- Their level-`m` congruence subgroups have genus `~ m^3`. After a bounded-scale triangulation, a surface
  maps to a 2-cycle of mass `~ m^3` on `Y_(Gamma(m))`.
- The orbifold Euler characteristic carries a factor `1/6`, so the Toledo invariant is not always divisible
  by `3`. Example with trivial discriminant factor: `(p-1)p(p+1)/6 = 20, 56, 220` for `p = 5, 7, 11`.
- Against `[Gamma : Gamma(m)] ~ m^10` this suggests `(MCF1) ~ d^(-3/10)` over `Gamma/Gamma(m)` at genus two.
- **Unverified:** the embedding into `Gamma(m)` itself, the exact Toledo normalization modulo 3, and how index
  relates to level for general normal `N`. For general normal subgroups the ratio can be worse.

**Where monomial methods stop.** A general tuple has no per-vertex holonomy. Products of commutators of
unitaries are arbitrary determinant-one unitaries, so one cycle sees only `det`, i.e. only `d mod 3`, which
gives floors of order `1/d`.
