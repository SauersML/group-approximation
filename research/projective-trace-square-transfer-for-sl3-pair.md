---
rg: 2
id: projective-trace-square-transfer-for-sl3-pair
kind: claim
title: Projective trace-square transfer for the co-dense SL3 arithmetic pair
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that forces an actual subgroup-central unitary into the ambient commutant; this asks only that its commutator with the one ambient generator become scalar in normalized Hilbert--Schmidt norm.
  no-spherical-leak-in-matrix-ultraproducts: that excludes every nontrivial spherical component and is equivalent to full relative-commutant collapse; this permits a leak whenever its ambient commutator is scalar, because scalarity already suffices for the HNN trace contradiction.
  no-exact-quasi-regular-leak: that excludes only the exact HNN coefficient profile and contains no quantitative transfer inequality; this proposes a dimension-free projective energy inequality for all regular approximate representations of the fixed arithmetic presentation.
---

Let

```text
C = SL_3(Z),
A = SL_3(Z[1/2]) = <C,h>,
h = diag(2,1,1/2).
```

Fix finite presentation relators for `A` and a finite generating set `S_C`
of `C`.  There are a constant `K<infinity` and a modulus `eta(delta)->0`
such that every finite-dimensional unitary assignment `rho` with presentation
defect at most `delta`, and every unitary `U` of the same matrix size, satisfy

```text
1-|tr([U,rho(h)])|^2
 <= K sum_(c in S_C) (1-|tr([U,rho(c)])|^2) + eta(delta).       (PTS1)
```

Equivalently, after passing to inner superoperators,

```text
||[Ad(U),Ad(rho(h))]||_2^2
 <= K sum_(c in S_C) ||[Ad(U),Ad(rho(c))]||_2^2 + 2 eta(delta), (PTS2)
```

because for every unitary `W in U(d)`, with normalized trace and normalized
Hilbert--Schmidt norm on `M_(d^2)`,

```text
||Ad(W)-I||_2^2 = 2-2|tr(W)|^2.                               (PTS3)
```

The claim is projective: `(PTS1)` concludes that `[U,rho(h)]` is close to
*some scalar*, not necessarily to `1`.  This phase quotient is exactly the
weakening consumed by the HNN marked word.

## Attempts

- **The native joint relation has a strictly smaller finite certificate.**
  `native-transfer-has-finite-trace-certificate` proves that after restricting
  to the balanced involution `c`, imposing
  `[c,h c h^-1]=1`, and retaining only regular-trace actor microstates, the
  qualitative transfer is equivalent to one linear inequality with one
  finite actor trace window.  Tensor amplification preserves all of these
  native conditions.  This does not prove the present universal claim, but
  it rigorously separates the downstream matrix target from arbitrary-unitary
  PRCC: neither an unknown modulus nor infinitely many trace tests remain in
  the weaker lamp problem.
- **The quantitative wall collapses to the universal qualitative wall.**
  `projective-transfer-linear-bound-equals-no-ultraproduct-leak` proves a
  stronger compactness statement than the previously recorded tensor
  observation.  If no linear bound
  `e_h<=L(q_C+delta)` exists, choose a violation
  `e_n>n(q_n+delta_n)` and take `ceil(1/e_n)` diagonal tensor copies.
  Relator defect and total `C`-energy become `O(1/n)`, while target energy is
  at least `1-exp(-1)`.  Hence exclusion of a qualitative projective leak in
  every matrix ultraproduct automatically gives `(PTS1)` with the linear
  modulus `eta(delta)=L delta`; there is no separate Lojasiewicz-rate
  problem.  Combined with perfectness, this identifies the present claim
  with **universal** relative-commutant collapse.  It also exposes an
  overstrength in the current route: `(PTS1)` ranges over arbitrary
  approximate assignments, while the HNN contradiction consumes only the
  regular-trace microstate class.  A regular-trace-restricted transfer theorem
  would suffice for the goal and need not settle arbitrary trace profiles.

- **Diagonal tensor powers are an exact projective error amplifier.**  Put
  `E(W)=1-|tr(W)|^2`.  Normalized traces multiply, so for every unitary `W`
  and integer `k>=1`,

  ```text
  E(W^(tensor k)) = 1-(1-E(W))^k <= k E(W).                 (AMP1)
  ```

  Apply the same diagonal tensor power simultaneously to `rho` and `U`.
  Every commutator word tensors, hence its projective energy follows `(AMP1)`;
  every ordinary presentation relator obeys the telescoping estimate
  `||rho(r)^(tensor k)-I||_2 <= k ||rho(r)-I||_2`.  Consequently, if a
  sequence had target energy `e_n -> 0` but ordinary relator defect
  `delta_n=o(e_n)` and `C`-energy `q_n=o(e_n)`, choosing
  `k_n=floor(1/e_n)` would produce a new sequence with vanishing relator
  defect and `C`-energy but target energy tending to `1-exp(-1)`.  This is a
  rigorous error-delocalization mechanism: tensoring copies a projective bad
  region until it has constant trace mass.  It does **not** prove `(PTS1)`,
  because an enemy can keep `e_n=O(delta_n+q_n)`; it shows that the remaining
  obstruction is precisely that locked linear-scale regime, not arbitrarily
  dilute target error.
- **Creutz--Peterson character rigidity stops at the generated factor.**
  Their operator-algebraic superrigidity theorem for commensurators
  (arXiv:1311.4513, Theorem B / Theorem 6.3) assumes
  `pi(A)''=M` and concludes that this generated finite factor is either
  finite-dimensional or the regular factor.  In `(PTS1)`, however, `U` lies
  in an ambient matrix ultraproduct outside `pi(A)''`.  Replacing `pi` by
  `Ad(U) pi` gives two representations agreeing on `C`, but the theorem does
  not assert uniqueness of extensions of a fixed `C`-representation inside a
  larger finite algebra.  This scope gap is real, not cosmetic: in the exact
  HNN algebra
  `L(<A,t | [t,C]=1>)`, the embeddings `pi` and `Ad(t) pi` agree on `C` and
  differ on `h`.  Thus exact character/factor rigidity cannot prove the
  transfer; finite-dimensional approximability must enter essentially.

- **Exact models now pass with a uniform quantitative gap.**
  `exact-projective-codensity-has-a-uniform-trace-square-gap` proves `(PTS1)`
  with `eta(0)=0` and one dimension-independent `K` for every exact
  finite-dimensional representation.  Perfectness of `SL_3(Z)` cancels the
  scalar phases on fixed commutator expressions, property (T) moves `U` close
  to `rho(C)'`, and co-density identifies that commutant with `rho(A)'`.
  Thus projective centralizers and finite congruence quotients are no longer a
  falsification gate.  What remains is entirely the uniform-outlier sector of
  approximate ambient representations.
- **Coset-Bernoulli firewall.** If the generalized coset Bernoulli crossed
  product of `coset-bernoulli-ce-refutes-relative-commutant-collapse` is
  Connes embeddable, its base-coordinate unitary produces an exact
  `C`-central witness.  Its commutator with `h` is non-scalar, so it also
  refutes `(PTS1)`.  Projectivization weakens RCC but does not evade that CE
  countermodel.
- **Hecke reduction.** `hecke-far-commutator-defect-formula` already compresses
  ordinary commutator energy to one spherical coefficient.  The missing
  calculation is the modulus-square/projective analogue restricted to the
  nonlinear inner orbit `{Ad(U)}`.  Property (T) controls the surrounding
  Hilbert space but not, by itself, this fixed set.
- **Finite test.** On congruence quotients minimize the ratio of the left side
  of `(PTS1)` to its `C`-energy.  The exact theorem bounds this ratio uniformly
  in the quotient level; computation is now only a calibration of the proven
  exact constant, not a possible refutation of the zero-defect case.
