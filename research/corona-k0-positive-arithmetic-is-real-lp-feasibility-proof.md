---
rg: 2
id: corona-k0-positive-arithmetic-is-real-lp-feasibility-proof
kind: route
title: Sum coordinate witnesses for necessity and diagonalize rational finite-stage solutions for sufficiency
target: corona-k0-positive-arithmetic-is-real-lp-feasibility
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Notation is that of the target claim.  Throughout, "eventually" means "for
all sufficiently large `n`".

## Step 0. The two projection monoids

**(a) Matrix coronas.**  By `matrix-corona-projection-monoid-is-rank-germs`,
`V(Q_d)` is isomorphic to the monoid `D_d^+` of germs, modulo eventual
equality, of sequences `r=(r_n)` of nonnegative integers with
`r_n <= k d_n` for some fixed `k`.  Addition is coordinatewise.  The algebraic
order, which is Murray--von Neumann subequivalence, is eventual `<=`.  The
unit `[1]` is the germ of `(d_n)`.  Consequently

```text
a < b   iff   r_n <= s_n eventually  and  r_n < s_n for infinitely many n.   (P0)
```

**(b) II_1 reduced products.**  Let `N` be a II_1 factor with trace `tau`.
Write `Tr` for `tau tensor Tr_k` on `M_k(N)`, which is again a II_1 factor
with trace range `[0,k]`.  Note that `M_k(A_N) = l^infty(M_k N)/c_0(M_k N)`.

*Lemma II.*

(i) Every projection of `M_k(A_N)` has a lift `(p_n)` consisting of
projections.

(ii) For projections `p = [p_n]` and `q = [q_n]`, `p` is subequivalent to `q`
iff `Tr(p_n) <= Tr(q_n)` eventually, and `p ~ q` iff `Tr(p_n) = Tr(q_n)`
eventually.

(iii) Hence `[p] |-> germ of (Tr(p_n))` is an isomorphism of `V(A_N)` onto
the monoid of germs of bounded sequences in `[0,infty)`, under eventual
equality.  Its algebraic order is eventual `<=`, and `[1]` is the germ of
the constant sequence `1`.  So `(P0)` holds verbatim with real `r_n,s_n`.

(iv) `A_N` is stably finite.

*Proof.*

(i) Lift a projection to self-adjoint `a_n` with `||a_n^2-a_n|| -> 0`.
Eventually `1/2` is not in the spectrum of `a_n`, so
`p_n = chi_((1/2,infty))(a_n)` is a projection in `M_k(N)` with
`||p_n - a_n|| -> 0`.  Put `p_n = 0` on the finitely many other indices.

(ii) Suppose `v^*v = p` and `vv^* <= q`.  Lift `v` to `v_n`.  Replacing `v_n`
by `q_n v_n p_n` keeps a lift, and `||v_n^*v_n - p_n|| -> 0`.  Eventually
`v_n^*v_n` is invertible in the corner `p_n M_k(N) p_n`.  Then
`w_n = v_n (v_n^*v_n)^(-1/2)` is a partial isometry with `w_n^*w_n = p_n`
and range inside the range of `q_n`.  Hence `Tr(p_n) <= Tr(q_n)`.

Conversely, suppose `Tr(p_n) <= Tr(q_n)` for `n >= n_0`.  Comparison in the
II_1 factor `M_k(N)` gives partial isometries `w_n` with `w_n^*w_n = p_n`
and `w_nw_n^* <= q_n`.  Put `w_n = 0` for `n < n_0`.  Then `[w_n]`
implements `p <= q`.

The statement for `~` is the same argument with `w_nw_n^* = q_n`.

(iii) The map is well defined and injective by (ii).  It is additive
because orthogonal sums add traces.  It is surjective because every
`t in [0,k]` is the trace of a projection in `M_k(N)`.

The algebraic order `a <= b`, meaning `a + c = b` for some `c`, corresponds
to eventual `<=`.  Take `c` to be the germ of `max(t_b - t_a, 0)`, which
agrees eventually with `t_b - t_a`.

(iv) Let `v in M_k(A_N)` with `v^*v = 1`.  By the argument of (ii) with
`p_n = 1`, `v_n` is eventually within `o(1)` of an isometry `w_n` of the
II_1 factor `M_k(N)`.  Every such isometry is a unitary, since
`Tr(w_nw_n^*) = Tr(1)` and `Tr` is faithful.  So `vv^* = [w_nw_n^*] = 1`.
`[]`

## Step 1. Necessity: (1) implies (2), and (3) implies (2)

Take a (Cor) interpretation.  Choose rank lifts `r_w(n)`, and put
`r_u(n) = d_n`.  Let `Sigma_0` be a finite subsystem.

By Step 0(a), every condition of `Sigma_0` holds coordinatewise on a common
tail `n >= n_0`.  Equalities hold as eventual equalities and weak
inequalities as eventual inequalities.  Strict conditions hold weakly on the
tail.  By `(P0)`, each strict condition `c` is also strict at some
coordinate `n_c >= n_0`.

Let `n_1,...,n_m` be these coordinates, or any single `n >= n_0` if
`Sigma_0` has no strict condition, and put

```text
y_w = ( r_w(n_1) + ... + r_w(n_m) ) / ( d_(n_1) + ... + d_(n_m) ).
```

Every condition is homogeneous linear, so it survives this positive
combination.  Every weak condition holds at every summand.  Each strict
condition is strict at one summand and weak at the others, hence strict in
the sum.  Finally `y_u = 1` and `y >= 0`.  So `Sigma_0` is real-feasible.

The same computation, with the real trace germs of Step 0(b)(iii) and the
denominator `m`, proves that (3) implies (2).

## Step 2. A rational-point lemma

*Lemma RP.*  Let `F` be a subset of `R^m` defined by finitely many linear
equalities, weak inequalities and strict inequalities with rational
coefficients.  Then every point of `F` is a limit of rational points of `F`.

*Proof.*  Let `y in F`.  Let `A` be the affine subspace cut out by the
equalities together with the weak inequalities that are tight at `y`, each
read as an equality.  `A` is defined over `Q` and contains `y`.  Gaussian
elimination over `Q` gives a rational point of `A` and a rational basis of
its direction space, so `A cap Q^m` is dense in `A`.

The remaining weak inequalities and all strict inequalities are strict at
`y`, so they hold on a neighborhood of `y` in `A`.  The tight weak
inequalities hold on all of `A`.  So rational points of `A` near `y` lie in
`F`.  `[]`

## Step 3. Sufficiency: (2) implies (1), with (6)

Enumerate `Sigma = {c_1, c_2, ...}`, repeating the last condition if
`Sigma` is finite.  Let `W_n` be the finite set of variables occurring in
`c_1,...,c_n`.  Let `Sigma_n` consist of `c_1,...,c_n` together with the
bounds `x_w <= k_w u` for `w in W_n`, which belong to `Sigma`.  Let
`F_n` be the set of `r in [0,infty)^(W_n)` with `r_u = 1` satisfying
`Sigma_n`.

By (2), `F_n` is nonempty.  It is cut out by finitely many rational
equalities, weak inequalities and strict inequalities, so Lemma RP gives a
rational point `r(n) in F_n`.  If a real solution `y` of the whole of
`Sigma` is given, then `y|W_n in F_n`, and we choose `r(n)` within `1/n` of
it.

Let `d_n >= 1` be a common denominator of the coordinates of `r(n)`, and put

```text
x_w(n) = d_n r_w(n)   (w in W_n),         x_w(n) = 0   (w not in W_n).
```

These are nonnegative integers.  Once `w in W_n`, the bound in `Sigma_n`
gives `x_w(n) <= k_w d_n`.  So `x_w` is a germ in `D_d^+`, and Step 0(a)
turns it into a stable projection class over `Q_d`.

Fix a condition `c_m`.  For every `n >= m`, all of its variables lie in
`W_n`, and `r(n)` satisfies `c_m` with `r_u(n) = 1`.  By homogeneity, the
integer vector `x(n)` satisfies `c_m` with `u` evaluated as `d_n`, which is
the rank of the identity.  So on the tail `n >= m`:

- an equality holds exactly, hence as an equality of germs;
- a weak inequality holds, hence in the algebraic order;
- a strict inequality holds strictly at every coordinate, hence strictly
  in the sense of `(P0)`.

Thus `x` is a (Cor) interpretation of `Sigma` in `Q_d`.  In the second
case, `rank(p_(w,n))/d_n = r_w(n) -> y_w`.  This proves (2) implies (1) and
the (Cor) half of (6).

## Step 4. Amplification: (5)

Let `d'_n = m_n d_n`.  Send the germ `(r_n)` to `(m_n r_n)`.  This map
preserves:

- sums;
- eventual equality and eventual `<=`;
- strictness at infinitely many coordinates;
- the bounds, since `m_n r_n <= k m_n d_n`;
- the unit, since `d_n` goes to `d'_n`.

So it carries a (Cor) interpretation in `Q_d` to one in `Q_(d')`.

## Step 5. The II_1 reduced products: (2) implies (4) implies (3)

Let `N` be any II_1 factor.  Repeat Step 3 without rational approximation.
Take any `r(n) in F_n`, or `r(n) = y|W_n` when a global real solution `y`
is given.  Let `p_(w,n)` be a projection in `M_(k_w)(N)` with
`Tr(p_(w,n)) = r_w(n)`, and `0` when `w` is not in `W_n`.  This is possible
because `r_w(n) <= k_w`.

The tail verification is literally that of Step 3, now using Step 0(b)(iii).
It gives a (II) interpretation, with `Tr(p_(w,n)) = y_w` constant in the
second case.  This proves (4) and the (II) half of (6).  (4) implies (3)
because II_1 factors exist, for example the hyperfinite one.  Together with
Step 1, conditions (1)--(4) are equivalent.

## Step 6. The faithful-trace transfer (Corollary)

Let `P_w in M_(k_w)(M)` be a pi-interpretation, and put
`y_w = Tr(P_w)`, where `Tr = tau tensor Tr_(k_w)`.  Since `Tr` is a faithful
normal trace:

- Murray--von Neumann equivalence preserves `Tr`, and direct sums add it.
  So every equality of classes in `V(M)` becomes a real equality.
- Subequivalence gives `<=`.
- `[1]` gives `1`, and `P_w in M_(k_w)(M)` gives `y_w <= k_w`.
- Suppose `P <= Q` holds strictly in `V(M)`.  Then `P ~ Q' <= Q` with
  `Q' != Q`, since otherwise `P ~ Q`.  So `Tr(Q) - Tr(P) = Tr(Q - Q') > 0`
  by faithfulness.
- The condition `0 < x_z` becomes `y_z = Tr(P_z) > 0`.

So `y` is a real solution of all of `Sigma`.  By Step 3 there is a (Cor)
interpretation with normalized ranks converging to `y`.  Its `x_z`-class is
nonzero because `0 < x_z` lies in `Sigma`.

For `Delta`, the root `z = x_13(q)` with `q = s_1t_1` is an involution,
since `x_13(q)^2 = x_13(2q) = 1` in characteristic two.  It is nontrivial,
because its image in `EL_20(L_(F_2)(1,2))` is the nonidentity elementary
matrix `1 + qe_13`, as `q != 0`.  Hence `tau_lambda(z) = 0` and
`P_z = (1-lambda(z))/2` is a projection of trace `1/2`.

## Step 7. The II_1 twin and the two adjoint coronas

**`Delta * Z` is ICC.**  In a free product, the centralizer of a nontrivial
element of one free factor lies in that factor.  This follows from the
reduced normal form: if `g` is outside the factor `B` and `1 != b in B`, then
`gbg^(-1)` has reduced length at least `3`.

Let `t` generate `Z`.  If `g` is not in `<t>`, the conjugates
`t^k g t^(-k)` are pairwise distinct, because `t^(k-l)` does not
commute with `g`.  If `g = t^m` with `m != 0`, the conjugates
`delta g delta^(-1)` for `delta in Delta` are pairwise distinct, because
`Delta cap <t> = 1`, and `Delta` is infinite.

So `N = L(Delta * Z)` is a II_1 factor.  It contains `L(Delta)`, and its trace
restricts to `tau_lambda`.

**The homomorphism.**  The constant sequence `g |-> [(lambda(g))_n]` is a
homomorphism `Delta -> U(A_N)`.  It is injective, because
`||lambda(g) - 1||_2 = sqrt 2` for `g != 1`, so the constant sequence is not
in `c_0`.  `A_N` is stably finite by Lemma II(iv), and its projection monoid
is cancellative by Lemma II(iii).  By Steps 1, 3 and 5 it solves exactly
the rank systems solved by matrix coronas.

**Adjoint coronas.**  The Hilbert--Schmidt adjoint corona of `Q_d` is
`prod B(M_(d_n),HS)/directSum = Q_(d^2)`, a matrix corona, hence stably
finite.  The analogue for `A_N` is `prod B(L^2 N)/directSum`.  It is
properly infinite, because `1` is the sum of two orthogonal projections
each equivalent to `1` in every coordinate `B(L^2 N)`, and so in the
product and in the quotient.  This is survivor (S2) of the target claim.

**Divisibility.**  In `V(A_N)`, the germ `(t_n)` equals `2(t_n/2)`.  In
`V(Q_d)`, the germ `(1,1,1,...)` is not `2y` for any `y`, because `2y_n = 1`
has no integer solution.  So the two monoids differ in a negated
existential statement but in no positive one.  This is survivor (S1).

The target claim follows.  `[]`
