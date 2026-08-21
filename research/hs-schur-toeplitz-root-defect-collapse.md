---
rg: 2
id: hs-schur-toeplitz-root-defect-collapse
kind: claim
title: Toeplitz direct finiteness kills the Schur root mark in normalized-HS microstates
artifacts:
  - research/artifacts/schur-toeplitz-root-defect-envelope-2026-08-20.md
distinct_from:
  leavitt-steinberg-hs-stable: that asks for correction of every almost representation of the simple Leavitt Steinberg group; this asks only for collapse of one named root in the packet-headed Toeplitz envelope.
  finite-window-decoder: that seeks four contractions on a positive-density Pauli corner; this may instead propagate the finite-index root kernel through the one-sided Toeplitz coefficient recurrence.
  toeplitz-tail-retains-contextual-schur-density: that asks for a conditional-expectation survive-or-recurse theorem for packet commutants; this asks for the equivalent coefficient-root defect to disappear directly.
---

OPEN. For the explicit finitely generated recursive ascending-HNN
presentation and word

```text
(H_f,w_f)=(EL_5(R_f)*_alpha,x_12(P_f))
```

from `schur-toeplitz-root-mark-is-fd-invisible`, prove first the qualitative
ultraproduct statement that every homomorphism

```text
Phi:H_f->U(product_omega M_(d_n))
```

satisfies `Phi(w_f)=1`. A sufficient stronger form is a finite-window modulus
`omega(epsilon)->0` such that every normalized-HS
`epsilon`-representation on that window satisfies

```text
||phi(w_f)-1||_2 <= omega(epsilon).                         (HST1)
```

The exact proof intersects finite-index kernels of exponent-`p` root groups
and then uses direct finiteness of the resulting finite coefficient quotient.
The approximate proof must replace this dimension-dependent intersection by
a weighted root-character argument. A sufficient recurrence is a sequence
`a_n<=1` measuring the mass on which the transported coefficient ideal still
detects `P_f`, with

```text
a_0 >= c||phi(w_f)-1||_2^2-C sqrt(epsilon),
a_n <= lambda a_(n+1)+C(n+1)^k sqrt(epsilon),
0<lambda<1.                                                (HST2)
```

The stable letter satisfies

```text
t x_ij(e_n)t^-1=x_ij(e_(n+1)),                         (HST3)
```

so all levels are consequences of one finite conjugacy menu. The relation
`P_f=1-xy` supplies the proper-corner orientation exactly; no
linear combination of represented packet words has to be converted into one
group word. Steinberg additivity and multiplication transport the coefficient
through roots. The unresolved step is a dimension-free weighted substitute
for intersecting all root kernels, or equivalently a first-hit decomposition
whose discarded root-character masses are summable.

The qualitative statement already makes `H_f` nonhyperlinear: hyperlinearity would give
microstates converging to the canonical delta trace, while the nontrivial
order-`p` word `w_f` has fixed positive delta-trace distance from the
identity. Higman's embedding theorem then puts this finitely generated
recursively presented nonhyperlinear group inside a finitely presented
overgroup, which is also nonhyperlinear because hyperlinearity passes to
subgroups.

Mandatory falsification test: the argument must use the one-sided relation
and the strict defect `P_f`. Any proof based only on the finite packet and
Steinberg covariance would contradict the finite-overgroup and direct
relator-certificate barriers.

There is now a second exact formulation of the analytic wall.
`hs-steinberg-root-kernel-is-linear-sofic` asks whether a tracial-HS model of
the Steinberg group makes the coefficient quotient by its common root kernel
linear sofic.  If it does, stable finiteness of rank-metric matrix
ultraproducts kills `P_f` immediately; this implication is the route
`hs-schur-root-collapse-via-linear-sofic-kernel`.  This separates the open
work into a metric decoder, rather than mixing it with Toeplitz algebra.

## Attempts

- **Intersect rounded root kernels.** For a fixed finite root window, the
  exponent-`p` commuting families can be rounded and jointly diagonalized.
  This does not reproduce the exact proof: the additive codimension of the
  joint kernel grows with matrix dimension, and the word depth required to
  show that its generated ideal contains `P_f` has no uniform bound. A
  forward union bound therefore loses exactly the amplification-invariant
  information the construction needs.
- **Linear-sofic root-kernel reduction.**  For an exact finite-dimensional
  root representation, conjugation formula `(SRK4)` makes the finite spectral
  character set carry left and right coefficient multiplication, and the
  common kernel quotient is finite.  In a tracial ultraproduct these spectra
  can become diffuse.  The precise proposed replacement is
  `hs-steinberg-root-kernel-is-linear-sofic`; it is sufficient because its
  rank ultraproduct is stably finite, but it is not automatic from HS-small
  error since an arbitrarily small full-rank perturbation has normalized rank
  one.
- **Direct relator telescoping.** Writing `x_12(P_f)` as a product of root
  words does not put `P_f` in the defining relator ideal. Such a certificate
  would kill the nonzero mark algebraically and contradict the faithful
  model of `schur-idempotent-is-an-injective-toeplitz-defect`.
- **Bare first-hit attack dies.** In `R_f`, put

  ```text
  e_n=x^n P_f y^n,                 n>=0.
  ```

  The Toeplitz relations give `e_n^2=e_n` and `e_n e_m=0` for `n!=m`, but
  `toeplitz-defect-idempotents-do-not-localize-root-characters` constructs
  one additive character detecting every `e_n`. Coefficient orthogonality is
  therefore not spectral first-hit orthogonality.
- **Active Heisenberg/Schur attack.**
  `toeplitz-defect-roots-form-independent-heisenberg-cells` attaches a
  transverse root pair to every `e_n`. A fiber detecting `r` centers then
  costs a factor `p^r` in representation dimension. This repairs the bare
  character defect but still permits dimensions growing as `p^N` and the
  hyperfinite infinite-tensor absorption model. The missing inequality is
  specifically the contextual Schur branch balance: a fixed fraction of the
  `e_n` carrier must enter a new active cell while at most one copy exits,
  giving `lambda<1` in `(HST2)`. Toeplitz transport supplies fresh cells;
  Fanizza/Schur orientation must supply the strict coefficient.
- **Self-similar syntax is closed.** By
  `schur-toeplitz-envelope-has-proper-self-embedding`, every cell and every
  root triangle is a stable-letter conjugate of the base cell. Derived
  covariance through depth `n` has polynomial word cost. This removes the
  infinite-presentation problem but not the analytic stationary-flow escape:
  conjugacy equalizes successive marginals, while the Schur child restriction
  must still supply the strict factor `lambda<1`.
- **Predicate orientation in every head is closed.**
  `schur-toeplitz-head-is-matrix-amplified-forbidden-algebra` identifies the
  depth-`N` head with `M_N(P_fk[B_f])` and proves the deep tail is scalar on
  it. Thus the recurrence does not have to recover a character-density sum
  from an anonymous tail commutant. What remains is a normalized-HS decoder
  showing that the finite packet multiplicity carried by this literal head
  factor passes through the represented root triangles with the oriented
  child coefficient `(OCB3)`.
- **The present shift does not supply that decoder.**
  `packet-headed-toeplitz-shift-is-schur-type-preserving` proves that
  `sigma^n` carries each full forbidden Wedderburn block isomorphically to the
  next full block. The prefix matrix amplification adds identical copies but
  never restricts through the `Q` child. Therefore `(HST2)` cannot be derived
  from the current coefficient self-map alone. The missing syntax is exactly
  the non-type-preserving child-MASA placement of
  `toeplitz-schur-child-masa-recurrence`; after that placement, the V4
  five-fourths exit law is the sharper local payment ledger.
- **A non-type-preserving replacement shift is now exact.**
  `binary-schur-child-toeplitz-self-embedding` uses `x |->x^2` and identifies
  the two-site head with `M_2(I)`.  On every forbidden sector it embeds the
  old full block diagonally in the two corrected-child blocks, so the desired
  factor-two restriction is present in the coefficient endomorphism itself.
  The remaining wall is no longer construction of a child-MASA placement;
  it is the single matrix-only estimate
  `binary-schur-toeplitz-one-branch-hs-payment`.  Merely iterating the binary
  shift is insufficient, because exponentially growing matrices realize the
  stationary regular branch flow.
- **The affine sign gives only a two-cycle.**
  `affine-sign-twist-swaps-active-blocks-but-is-stationary` computes the one
  nontrivial internal holonomy made available by the affine `S_3`: it
  exchanges the two active `M_3` blocks.  Twisting the Toeplitz embedding by
  this sign is genuinely non-type-preserving, but its transition matrix is a
  permutation with spectral radius one.  It equalizes the two charts and
  cannot provide the strict backward coefficient in `(HST2)`.
- **Why ordinary Toeplitz truncation is not a counterexample by itself.** In
  truncated unilateral-shift matrices, the rank-one defect has vanishing
  normalized trace. Here the canonical root mark has fixed delta-trace
  distance from the identity. A countermodel must therefore decouple root
  phase mass from coefficient-defect rank; locating or excluding precisely
  that decoupling is the root-character transport problem above.
