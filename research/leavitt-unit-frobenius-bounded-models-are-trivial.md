---
rg: 2
id: leavitt-unit-frobenius-bounded-models-are-trivial
kind: claim
title: Frobenius-bounded asymptotic representations of the binary Leavitt unit group are pointwise Hilbert--Schmidt trivial
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that asks whether any normalized Hilbert--Schmidt model exists; this asks only that models whose unnormalized Frobenius defects stay bounded are trivial, a statement implied by the negative answer there.
  leavitt-unit-bounded-block-models-are-asymptotically-trivial: that proves triviality when the Frobenius defects of the selected blocks tend to zero, which forces operator-norm control; this keeps them bounded but not small, where a bounded number of dimensions may carry order-one operator-norm error.
  scaled-kazhdan-transport: that transports asymptotic commutants of operator-norm almost representations with Frobenius-mass weights on the commutant side; this concerns almost representations whose own defects are only Frobenius-bounded, where that transport is not available.
  deligne-cover-sector-floor-below-exponent-one-half: that asks for polynomial Frobenius floors for sector tuples of finite Deligne covers; this is a bounded-Frobenius rigidity statement for the simple Kazhdan group U with full MF radical.
---

**OPEN.**  Let `R = L_(F_2)(1,2)` and `U = R^x`.  Prove: for every sequence
`k_L -> infinity` and maps `phi_L : U -> U(k_L)` with

```text
limsup_L ||phi_L(gh) - phi_L(g) phi_L(h)||_F < infinity      for all g, h in U,   (FB)
```

where `||X||_F = Tr(X^* X)^(1/2)` is the unnormalized Frobenius norm, one has
`||phi_L(g) - 1||_(2,k_L) -> 0` for every `g`, with `||X||_(2,k)^2 = (1/k) Tr(X^* X)`.

By `leavitt-unit-frobenius-bounded-threshold-iff-fb-rigidity` this is exactly
the statement that the bounded-block threshold of
`leavitt-unit-bounded-block-models-are-asymptotically-trivial` extends from
`k eps^2 -> 0` to `k eps^2 = O(1)`.

## Where it sits

- **It follows from non-hyperlinearity of `U`.**  (FB) with `k_L -> infinity`
  gives normalized defects `k_L^(-1/2) ||·||_F -> 0`, so `phi_L` is a
  Hilbert--Schmidt asymptotic homomorphism and its tracial ultraproduct is a
  homomorphism `V : U -> U(M^omega)`.  Its kernel is normal, and `U` is simple
  (`binary-leavitt-all-ranks-full-mf-radical`).  If some `s` had
  `lim_omega ||phi_L(s) - 1||_2 > 0`, the kernel would be proper, hence trivial,
  and `U` would embed in the unitary group of a matrix ultraproduct, i.e. be
  hyperlinear.  So a negative answer to `binary-leavitt-unit-group-hyperlinear`
  implies this claim (along every ultrafilter, hence for the sequence).
- **It implies the Frobenius-to-zero case,** which is already established:
  `||X||_op <= ||X||_F`, so Frobenius defects tending to zero are operator-norm
  defects tending to zero, and full MF radical kills those.
- **Shape of the defects.**  A Frobenius defect bounded by `C` is at most `t` in
  operator norm off a subspace of absolute dimension at most `C^2 / t^2`.  So (FB)
  describes homomorphisms into the unitary group of
  `prod_L M_(k_L)(C) / K`, where `K` is the closed ideal of sequences whose
  spectral projections above every fixed `t > 0` have uniformly bounded rank.
  (An index count suggests that quotient is stably finite; this is a sketch,
  not used anywhere.)

## Attempts

**Rerun the norm-corona transport modulo bounded rank.**  The proof of
`kazhdan-asymptotic-commutant-transport` passes to
`prod B(M_(k_n)) / bigoplus`, where the conjugation maps become a homomorphism,
takes the Kazhdan projection there, and uses stable finiteness.
With (FB) defects, conjugation errors are operators on the Hilbert--Schmidt
space `M_(k_n)` of rank `O(k_n)` inside dimension `k_n^2`, not small in
operator norm: `Ad(1 - 2p) - 1` has norm `2` for a rank-one projection `p`.
The natural quotient kills every projection of rank `O(k_n)` on that space.
The near-commutant of a nearly irreducible Kazhdan image has dimension far
below `k_n`, so its Kazhdan projection vanishes in the quotient, and the
order argument carries no information.  Estimates on operator-bounded test
matrices do survive, since `||B Y||_(2,k) <= ||B||_F ||Y||_op / sqrt(k)`, but the
stable-finiteness step needs control on all of the Hilbert--Schmidt space.
Dead as stated; an argument must control the small near-commutant directly.

**Absorb the bounded-rank defect into a codimension-bounded subspace.**  Cutting
out the span of the large singular directions of all relator defects on words
of length at most `L` leaves a subspace of bounded codimension where those
relators hold in operator norm.  But the generators move a bounded-rank part of
that subspace outside it, so the compressed maps again have order-one defects
of bounded rank.  The count never closes without an approximately invariant
bounded-dimensional defect support, which would itself be a bounded-dimensional
almost representation.  Dead as stated.

**No general stability theorem can give it.**  The Attempts of
`binary-leavitt-unit-group-hyperlinear` record rank-one compressions of
irreducible representations of `SL_3(Z)` that are far from genuine
representations in their dimensions; their defects have bounded rank, so they
satisfy (FB) and are far from representations.  Any proof must use
information specific to `U`, such as full MF radical or the absence of
finite-dimensional representations, not property (T) alone.

**Firm the quotient and use its finiteness (2026-09-13, lane `solve-nh-frobenius-b`).**
The quotient above is now `frobenius-bounded-corona-is-stably-finite`
(ESTABLISHED): the spectrally bounded-rank sequences form a closed ideal, the
quotient is stably finite, every (FB) model is a homomorphism into its unitary
group, and the tracial states factor through it.  This does not decide the
claim: `U` embeds in the unitary group of the stably finite `C*_r(U)`, so
finiteness of the target algebra alone cannot kill a homomorphism.  The
manuscript's rigidity uses finiteness on the Hilbert--Schmidt space of the
coordinate matrices, where commutants are the invariant vectors of `Ad`.

**Locate the one failing step of the manuscript's transport (2026-09-13).**
Write `A(g) = Ad(V(g))` on `(M_k, ||.||_HS)`, `a = V(g) V(h)`, `b = V(gh)`,
`E = a - b` with `||E||_F <= C`.  Then `(A(g) A(h) - A(gh)) x = E x a^* + b x E^*`,
so for operator-bounded test matrices `||x||_op <= M`,
`||(A(g) A(h) - A(gh)) x||_(2,k) <= 2 C M / sqrt(k) -> 0`.  Backward transport
is algebraic: if `uLu^(-1) <= L` and `x` is an operator-bounded 2-norm
asymptotic commutant of `V(L)`, then
`[V(l), V(u)^* x V(u)] = V(u)^* [V(u) V(l) V(u)^*, x] V(u)` and
`V(u) V(l) V(u)^* - V(u l u^(-1))` is Frobenius-bounded, so `V(u)^* x V(u)` is
again an asymptotic commutant.  In the manuscript's defect corollary every
step except one survives (FB) errors on the operator-bounded test sequence
`x = V(c)`, `c in C_H(L)`: the failing step is FORWARD transport,
`V(u) V(c) V(u)^*` in the asymptotic commutant of `V(L)`.  Forward transport
for (FB) models of `H = EL_12(R)` is equivalent to this claim (the converse is
immediate), so it isolates the gap; it is not new information about the gap.
Forward transport is exactly where the manuscript uses the Kazhdan projection
and stable finiteness of `prod B(M_k) / bigoplus`.  Candidate quotients tested:
- The closed two-sided ideal of `prod B(M_k)` generated by the `Ad` errors
  contains all rank-`O(k)` operators and kills the commutant projection
  (first Attempt above).
- Operators `x |-> a x b` with `a` or `b` in the bounded-rank ideal do kill
  operator-bounded test matrices in normalized 2-norm, but they are not an
  ideal of `B(M_k)`: composing with arbitrary operators on `M_k` loses
  operator-boundedness of the test vector, and the ideal they generate is the
  first one.  Restricting to the `C*`-algebra generated by `A(G)` does not
  help, because norm limits of finite `Ad`-combinations need not preserve
  operator-boundedness on `M_k`.
- Trace counting does not replace finiteness: the normalized trace on
  `B(M_k)`, of dimension `k^2`, gives the near-commutant projection `P` trace
  tending to `0` whenever the near-commutant has dimension `o(k^2)`, while `P`
  fixes the test matrix `1_k`.  So `U^* P U <= P` yields equality only in the
  II_1 shadow, which is blind to test vectors.
Dead as stated.  What is missing is a finiteness statement for one-sided
compressions of commutant projections that is tested on operator-bounded
matrices.

**Counterexample hunt (2026-09-13).**  None found.
- Permutation models: an (FB) model into symmetric groups is a sofic
  approximation with bounded absolute Hamming defect, so its ultraproduct
  homomorphism is trivial by `leavitt-unit-group-has-only-trivial-sofic-morphisms`
  and simplicity.
- Exact finite models cannot supply a Frobenius screen for the criterion's
  hypotheses: in a finite group `u L u^(-1) <= L` forces equality, so
  compression defects die in any model that is exactly multiplicative on large
  balls.
- Compressions `P_L pi P_L` of a unitary representation `pi` of `U` with
  `||[pi(s), P_L]||_F` bounded on generators are (FB) models.  A nontrivial one
  would make the limit character an amenable trace, so `U` would be hyperlinear
  with Frobenius-bounded microstates, which is strictly more than
  hyperlinearity.  No representation with such bounded-boundary finite-rank
  projections was found.
