---
rg: 2
id: machine-free-digit-reading-group-is-mf
kind: claim
title: The machine-free digit-reading group is operator-MF
root: true
distinct_from:
  c-free-aanderaa-rope-is-mf-with-fine-quotients: that is the full C-free rope with the machine; this is its smallest instance with the machine removed, stated as a self-contained analytic problem with equivalent formulations.
  boone-base-has-corona-inner-instruction-automorphisms: that is the Turing-engine free edge; this is the modular-compiler reading edge, and the two are the two known faces of the same non-residual phenomenon.
---

Fix `m >= 3` and `n >= 1`.  Show that the finitely presented group

```text
Gamma^K = < x, t, p, a_1, ..., a_(2n) |
           [a_i, p] = 1,  a_i t a_i^-1 = x^-i t x^i,  a_i x a_i^-1 = x^m,
           [a_i, b_j] = 1 (1 <= i, j <= 2n) >,
b_j := t_j^-1 p t_j t^-1 p^-1 t,   t_j := x^-j t x^j,                 (DR1)
```

is operator-MF (embeds in the unitary group of `prod M_k / (+) M_k`).

## Why this is the whole prize

`Gamma^K` is Cohen's `p`/`a_i` rope over the trivial machine
(`K_M -> < x, t >`, `y` dropped), with the free letters `d = t^-1 p t p^-1`
and `b_j` eliminated.  It is not residually finite: in any finite quotient
`x` has finite order `N`, hence `t_alpha = t_(alpha+N)`, hence `w_alpha(b) =
w_(alpha+N)(b)` (see [[c-free-aanderaa-rope-is-mf-with-fine-quotients]]).  A
proof that `Gamma^K` is MF must therefore produce genuinely approximate
representations.  Adding back the machine only inserts central HNN letters
over subgroups of `< x, y, t >` (the engine is MF by
[[modular-machine-boone-group-is-mf]]), so a proof for `Gamma^K` that is
compatible with such letters closes
[[c-free-aanderaa-rope-is-mf-with-fine-quotients]] and hence, through
[[product-commuting-aanderaa-cohen-compiler]] and
[[mf-safe-compiler-via-product-commuting-aanderaa-cohen]], the
finite-presentation `Pi^0_2`-completeness of MF.

## Equivalent formulations

*Corona conjugacy.*  Let `Gamma' = < x, t, F(b,d), a_i | a_i t a_i^-1 =
t_i, a_i x a_i^-1 = x^m, a_i d a_i^-1 = b_i d, a_i b_j a_i^-1 = b_j >`, a
genuine HNN tower over the free group `F(x,t) * F(b,d)`, with `< t, a_1,
..., a_(2n) >` free.  Then `Gamma^K` is the HNN extension of `Gamma'` by
`p` with `p t p^-1 = t d`, `[p, a_i] = 1`, and `Gamma^K` is MF iff there is
an embedding `Phi : Gamma' -> U(corona)` and a corona unitary `U` with `U
Phi(a_i) U^* = Phi(a_i)` and `U Phi(t) U^* = Phi(t) Phi(d)` (Ueda's corner
and Shulman's Theorem 20 for the "if", restriction for the "only if").

*Digit-multiplicative pairs.*  Writing `T_alpha = X^-alpha T X^alpha` and
`B_i = T_i T^-1` for unitaries `X, T`, the group `< x, t, p, a_i >` forces

```text
T_(i + m alpha) T^-1 = (T_alpha T^-1) B_i          (1 <= i <= 2n, alpha in N),   (DR2)
```

i.e. `alpha -> T_alpha T^-1` is the digit-word map `w_alpha(B)`.  Finite
groups cannot satisfy `(DR2)` with `X` of order `N` unless the `B_i` are
trivial.  `Gamma^K` is MF iff `(DR2)` admits approximate unitary solutions
of arbitrarily high accuracy on arbitrarily long initial segments of `alpha`,
together with the commuting `p` and the `a_i` implementing `(X, T) -> (X^m,
X^-i T X^i)`, and separating the group.

## Attempts

Everything in [[c-free-aanderaa-rope-is-mf-with-fine-quotients]] and
[[tape-group-trichotomy-for-mf-safe-higman-compilers]]: finite quotients,
synchronized HNN, twisted edges, Fell absorption, inner envelopes, and a
change of tape all fail or relocate the edge.  Not attempted: a direct
random-matrix or self-similar construction of `(X, T)` satisfying `(DR2)`
approximately (for instance `X` a shift on a Cantor-like digit space and
`T` a diagonal-plus-shift operator), which is the natural next attack.

*What finite quotients can see.*  If `x` has order `r` in a quotient in
which the `b_i` survive, periodicity forces `w_alpha(b) = w_(alpha+r)(b)`
for all `alpha`; when `r | m - 1` the digit sum is a function of `alpha mod
r`, and the assignment `b_i -> B^i` with `B^r = 1` satisfies every
constraint.  Conversely the constraints force `beta_i = beta_(i+r)` and
collapse products to digit sums, so the image of `F(b)` in any finite
quotient of `Gamma^K` in which `x` has order `r` is cyclic of order dividing
`r`.  In a solvable quotient `A x| Q` with `A` a torsion-free abelian normal
subgroup containing `x`, the `b_j` die outright (`m b_j = b_j` from `[a_i,
b_j] = 1`).  So every residual method — finite or solvable — is blind to the
free structure of the word component, which is where the MF approximants
must be genuinely non-exact.

*Shift edge versus digit edge.*  Write `Gamma_2 = < F(x,t) * F(b,d), p |
p t_alpha p^-1 = t_alpha w_alpha(b) d >`.  Then `Gamma_2 = HNN(P_0; x)` with
`P_0 = (T * F(b,d)) *_psi` residually finite and `x` conjugating the free
subgroup `T = < t_alpha : alpha in Z >` to itself by the shift `t_alpha ->
t_(alpha+1)`.  A finite quotient of `P_0` synchronizes the shift exactly iff
the kernel of `T -> Q` is shift-invariant, i.e. the shift induces an
automorphism `phi` of the image, so `q(t_(alpha+1)) = phi(q(t_alpha))` and
`alpha -> q(t_alpha)` is periodic of period `ord(phi)`; the digit edge then
forces `w_alpha(b) = w_(alpha+N)(b)`.  So the shift edge and the digit edge
cannot both be synchronized by one finite quotient, in any order.  What
remains is the approximate version: the tuples `(lambda(q(t_alpha)))_(|alpha|
<= A)` and `(lambda(q(t_(alpha+1))))` need only be conjugate up to `o(1)` in
operator norm on windows `A -> oo`, with the digit refinement kept exact on
the window.  Whether tuples of regular representations that are locally
isomorphic up to length `L(A) -> oo` are asymptotically unitarily conjugate
is the concrete operator-theoretic question; single unitaries of large
order are (eigenvalue equidistribution), tuples are not known to be.

