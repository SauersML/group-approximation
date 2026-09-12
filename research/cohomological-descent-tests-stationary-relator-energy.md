---
rg: 2
id: cohomological-descent-tests-stationary-relator-energy
kind: route
title: Test almost-stationarity against the small-angle cohomological descent direction
target: two-kazhdan-stationary-curvature-has-no-small-angle-part
requires: []
artifacts:
  - research/artifacts/stationary-curvature-and-operator-flat-gradient-basin-2026-09-05.md
---

In the normalized-HS ultraproduct let K_delta be the closure of classes
represented by L2-bounded matrices A_j with delta_j||A_j||op->0.
Its vectors have representatives satisfying that condition, by slow
diagonal approximation. For a fixed word defect D-I of HS size O(delta),
left or right multiplication on such representatives has vanishing
error. Thus wordwise adjoints define a genuine G action on K_delta.

Products AB/delta of operator-bounded errors with HS size O(delta)
are orthogonal to K_delta: their pairing with a core vector Y has
absolute value at most
`||Y||op ||A||_2||B||_2/delta=O(delta||Y||op)`. Applying this to
the exact associativity identity for section defects shows that their
normalized projection onto K_delta is a skew-Hermitian 2-cocycle.
Full H2 vanishing makes it the coboundary of a skew cochain b.
Choose generator representatives b_(j,s) with bounded HS norm and
delta_j||b_(j,s)||op->0. The sections on S are its literal letters,
so their matrix values are the original U_s.

Let P be projection onto K_delta and c_r=[(U_j(r)-I)/delta_j].
Finite-word expansion of exp(-delta_j b_(j,s))U_(j,s) gives
`[L_r(b_j)]=P c_r`, where L_r is the left logarithmic word
derivative. The projected pair curvature is canceled by db, and
finite multiplication propagates this cancellation to each defining
word. Exponential Taylor remainders and mixed old-defect terms are
o(delta) in HS by delta||b||op->0.

For the differentiable curve exp(-t delta_j b_(j,s))U_(j,s),
the initial tangent norm is O(delta_j). Almost-stationarity makes
its energy derivative o(delta_j^2). Direct differentiation instead
gives the limit

```text
lim_j (1/delta_j^2) dF/dt|_0
 =-2sum_r Re<c_r,P c_r> =-2sum_r||P c_r||_2^2.
```

Indeed the exact normalized derivative is -L_r(b_j)U_j(r), which
differs from -L_r(b_j) by o(1) in HS. Thus every P c_r=0.
If a low-angle piece retained positive relative energy at cutoffs
t_j->0, that piece would itself be a K_delta test vector with
positive pairing, a contradiction. Taking arbitrary subsequences
and ultrafilters proves STG1 with its ordinary limsup. Spectral
Markov bounds and joins of the hard supports give the stated rank
and two-sided complementary norm conclusion.

If STG2 failed, choose positive-defect tuples with maximum operator
relator defect less than 1/j and gradient norm less than delta_j/j.
They satisfy STG1, yet every normalized defining error lies below
each fixed positive angle cutoff eventually, and the maximum of
their normalized HS norms is one. This contradiction proves uniform
t0,c0. No H1 or finite-dimensional comparison representation is
needed in this argument.

Inside this basin, `F'=-||grad F||_2^2<=-c_PL^2 F`. Dividing
the energy derivative by the gradient norm and integrating gives
path length at most `2sqrt(F(U_0))/c_PL`. The normalized-trace
gradient is a finite sum of conjugates of twice the skew parts of
the relator unitaries. Hence
`||(grad F)_s||op<=2 n_s alpha`, for
alpha=max_r||U(r)-I||op. Fixed-word differentiation gives
`D^+alpha<=C_R alpha`, so alpha(t)<=alpha_0 exp(C_R t).
A first exit at alpha=t0 therefore takes time at least
`log(t0/alpha_0)/C_R` and has energy at most the claimed
`F(U_0)(alpha_0/t0)^theta`.

At an exit, one relator has a singular error of size t0, forcing
energy at least t0^2/d. STG3 excludes such an exit. In fixed
dimension the smooth flow exists globally on the compact product
unitary group, and its finite HS length and decaying energy give
an exact limit. Without STG3 the operator boundary can be reached
despite the small HS path length, so no global stability conclusion
is justified.
