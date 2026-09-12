# Microscopic exact corners admit a dimension-weighted error ledger

The number of successive extractions need not enter the global error.
This allows arbitrarily small nonzero corners to prove flexible HS
stability under a quantitative seed estimate. Mere qualitative seed
existence does not supply that estimate by the argument below.

## 1. Finite extraction ledger

Start with a unitary tuple U^(0) on H_0=C^d. At step i let
H_i=P_i H_i direct_sum H_(i+1), with r_i=rank P_i>0, and let rho_i
be an exact representation on P_i H_i satisfying, for every generator,

    ||U_s^(i) J_i-J_i rho_i(s)||_HS <= xi_i sqrt(r_i),  (ML1)

where J_i is inclusion. Choose U_s^(i+1) to be a unitary polar
completion of the compression Q_i U_s^(i) Q_i, Q_i=I-P_i. Choose
inverse generators compatibly. There is no lower bound on r_i/d.

For any finite number N of steps, let

    V_s=direct_sum_(i<N) rho_i(s) direct_sum U_s^(N).

Then, in the original coordinates,

    ||U_s^(0)-V_s||_HS^2 <= 3 sum_(i<N) xi_i^2 r_i.    (ML2)

Replacing the final residual tuple by the trivial representation gives

    ||U_s^(0)-(direct_sum_(i<N)rho_i(s) direct_sum I)||_HS^2
      <=3 sum_(i<N)xi_i^2 r_i+4 dim H_N.              (ML3)

These bounds hold separately for each generator and for arbitrarily
large finite N; they do not use a triangle inequality across all N
off-diagonal changes.

To prove them, abbreviate U_s^(i) by U_i and put

    E_i=U_(i+1)-Q_i U_i Q_i.

If the singular values of Q_i U_i Q_i are s_l, polar completion gives

    ||E_i||_1=sum_l(1-s_l)
      <=sum_l(1-s_l^2)
      =||P_i U_i Q_i||_HS^2
      =||Q_i U_i P_i||_HS^2
      <=xi_i^2 r_i.                                  (ML4)

The equal off-diagonal masses use unitarity. Also (ML1) gives

    Re Tr(rho_i(s)^* P_i U_i P_i)
      >=r_i-(xi_i^2 r_i)/2.                          (ML5)

On each later diagonal block, the current compression differs from
the original U_0 by the compressions of the earlier E_l. In the total
diagonal overlap with V_s, the contribution of a fixed E_l is paired
with the unitary direct sum of all later final blocks on H_(l+1).
Its absolute value is therefore at most ||E_l||_1, once, regardless of
how many later blocks there are. The final overlap with U_N is dim H_N.
Thus

    Re Tr(V_s^* U_0)>=d-(3/2)sum_i xi_i^2 r_i.

Both matrices are unitary, proving (ML2). If the last block is identity,
its overlap with U_N is at least -dim H_N rather than dim H_N. The
same argument proves (ML3).

## 2. A linear microscopic seed estimate suffices

Fix a finite presentation with longest relator length ell>=1, and put

    delta(U)=max_R ||R(U)-I||_(2,n)

for tuples on C^n. Suppose there are constants K and delta_*>0 such
that every tuple with 0<delta(U)<delta_* admits either:

* a nonzero corner of rank r<=n and an exact representation with
  retained-column error at most K delta(U) sqrt(r), as in (ML1); or
* a full flexible exact correction, with normalized generator error
  at most K delta(U) and relative padding at most K delta(U)^2.

Then the group is flexibly HS-stable, with the explicit Holder rates

    generator error = O(delta_0^(1/(c+1))),
    relative padding = O(delta_0^(2/(c+1))),
    c=6K^2 ell^2.                                    (ML5H)

No uniform lower bound on the corner rank or rank fraction is required.
Constants are independent of dimension and of the number of extractions.

Here is a quantitative finite-iteration proof. Start with defect delta_0
and a threshold theta in (0,1), and continue extracting while the residual
dimension n_i exceeds theta d. Stop immediately if a residual is exact
or the second alternative occurs. Define

    A_i=(1/d)sum_(l<i) xi_l^2 r_l,
    xi_l=K delta(U^(l)).

The comparison tuple in (ML2) has exact extracted blocks. Telescoping
each relator against U^(0), and then restricting its defect to the
residual block, gives

    x_i=n_i/d,
    delta(U^(i)) <= (delta_0+ell sqrt(3A_i))/sqrt(x_i),
    delta(U^(i))^2 <= (2/x_i)(delta_0^2+3ell^2 A_i).   (ML6)

Consequently, with B_i=delta_0^2+3ell^2 A_i,

    B_(i+1)<=B_i(1+c r_i/n_i),     c=6K^2 ell^2.

If n_(i+1)>0, put u=r_i/n_i<1 and use
log(1+cu)<=cu<=-c log(1-u). Induction gives the sharper bounds

    B_i<=delta_0^2 x_i^(-c),
    delta(U^(i))^2<=2delta_0^2 x_i^(-c-1).             (ML7)

Choose a fixed 0<delta_bar<delta_* and, for sufficiently small delta_0,

    theta=(2delta_0^2/delta_bar^2)^(1/(c+1))<1.

Every pre-step x_i>theta satisfies

    delta(U^(i))^2<=delta_bar^2,
    delta(U^(i))^2 x_i<=delta_bar^2 theta,
    B_i<=delta_bar^2 theta/2.                         (ML7a)

This inductively verifies the seed threshold at every step. Intermediate
defects need only stay below this fixed admissible threshold; they need
not all tend to zero. Every extraction removes at least one dimension,
so there are at most d extractions.

If an extraction first crosses to n_(i+1)<=theta d, its multiplier in
the B recurrence is at most 1+c, also when it removes all n_i dimensions.
Thus B_terminal<=(1+c)delta_bar^2 theta/2. Equation (ML3) gives a
same-dimensional exact correction with squared normalized error at most

    [4+(1+c)delta_bar^2/(2ell^2)] theta.               (ML7b)

If the full flexible alternative occurs earlier, write q for its padding
on the current residual and combine it with the already exact blocks.
Then q<=K delta(U^(i))^2 n_i, so q/d<=K delta_bar^2 theta. The squared
global error, normalized by d+q, is at most

    6A_i+2K^2 delta(U^(i))^2 (n_i+q)/(d+q)
    <=[delta_bar^2/ell^2
       +2K^2(1+K delta_bar^2)delta_bar^2] theta.        (ML7c)

The first term uses (ML2) and one final triangle inequality; the second
retains the residual's dimension weight. An exact residual gives the
same conclusion directly from (ML2). Equations (ML7b)--(ML7c) prove
(ML5H), including its padding exponent. The case delta_0=0 is already
an exact representation.

For SL_5(Z), a concrete sufficient spectral input is

    lambda_min(Delta_(Q_(2n),U)) <= L^2 delta(U)^2      (ML8)

for every sufficiently small-defect tuple, with L uniform in n.
Take epsilon=L delta(U). At small defect, MSC14 gives a nonzero
spectral space of rank r<=n/(1-a), a=2h epsilon^2/kappa^2<=1/2, and

    xi<=sqrt(h)(1+4/kappa)L delta(U).

Its coisometry gives the first alternative when r<=n. When r>n, its
padded polar correction gives the second, with padding bounded by
4h L^2 delta(U)^2/kappa^2. Thus (ML8) suffices without any positive
normalized count. The estimate (ML8) is an additional, unproved input.

## 3. Why a qualitative nonzero seed leaves a rate problem

A hypothesis asserting merely that each approximate sequence has a
nonzero spectral seed at some cutoff epsilon_j->0 provides no bound
comparing epsilon_j with its defect. The next residual is controlled
by delta_0 and the accumulated quantity A_i through (ML6). To justify
further extractions at vanishing cutoffs, that residual must remain an
approximate sequence. Assuming this before controlling A_i would be
circular.

The issue is visible in the abstract ledger. If the available seed
estimate were xi approximately delta^alpha with 0<alpha<1, its squared
cost could be of order x^alpha when residual squared defect is of
order x. Infinitesimal rank increments are then compatible with

    dx/dt=x^alpha,
    x(t)=(x(0)^(1-alpha)+(1-alpha)t)^(1/(1-alpha)).

At every fixed t>0 this upper-bound model does not tend to zero with
x(0). This is not a construction of unitary tuples or a counterexample
to the qualitative seed implication. It identifies what the stated
ledger and a merely qualitative modulus fail to control. The linear
estimate avoids it through the proved discrete Gronwall bound (ML7).

Canonicality has a separate scale restriction. Extracted corners of
rank o(d) need not have canonical normalized traces; an exact trivial
block is a simple example. A residual of dimension at least theta d
does remain canonical if its accumulated ledger A_i tends to zero:
(ML2) makes its projection asymptotically reducing for the original
canonical tuple, and the ICC conditional-expectation argument then
gives canonical corner traces. This holds even for a varying number
of extraction steps. Without control of A_i, canonicality of the
intermediate residuals is not automatic either.

The result therefore removes any need for a positive-density seed when
a uniform linear seed modulus is available. It does not show that mere
nonzero seeds supply that modulus, or that arbitrarily many qualitative
extractions alone resolve the nonhyperlinearity endpoint.
