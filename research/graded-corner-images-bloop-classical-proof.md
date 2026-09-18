---
rg: 2
id: graded-corner-images-bloop-classical-proof
kind: route
title: Read the context degree map, cap each question at two active answers, and collapse by idempotent implications
target: graded-corner-images-of-bloop-force-classical-solution
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - paddock-slofstra-bcs-forbidden-projection-dictionary
---

Notation as in the target claim.  Write `true` as the `+1` eigenvalue, so the
literal idempotent is `T_x=(1+z_x)/2`.

## Step 0. Atoms

For a context `c` with `k` variables, and a sign vector `phi in {+-1}^c`,
put `phi(S)=prod_(x in S) phi(x)` and `z_S=prod_(x in S) z_x`, for `S <= c`.
Then

```text
Pi_phi = prod_(x in c) (1+phi(x)z_x)/2 = 2^(-k) sum_(S<=c) phi(S) z_S,
Pi_phi z_S = phi(S) Pi_phi,        sum_phi Pi_phi = 1.                (P0)
```

The second identity uses `z_x^2=1` and commutation inside `c`.  In `A(B_G)`,
`Pi_phi=0` for every forbidden `phi`.  Identify `phi` with a point of
`F_2^c`.

## Step 1. Degrees

Put `u_x=Phi(z_x)`.  Then `u_x^2=1`, so `u_x` is invertible, hence nonzero.
Let `u_x` lie in `D_(d(x))`.  Then `1=u_x^2` lies in `D_(d(x)^2)`, and
`1 != 0` lies in `D_e`.  Since the sum `(GCB1)` is direct, `d(x)^2=e`.

For `x,y` in one context, `u_xu_y=u_yu_x` is nonzero.  It lies in both
`D_(d(x)d(y))` and `D_(d(y)d(x))`, so the two degrees commute.  Hence

```text
d_c: F_2^c -> H,   S |-> prod_(x in S) d(x)                            (P1)
```

is a group homomorphism, and `Phi(z_S)` lies in `D_(d_c(S))`.

Let `W_0=ker d_c`.  For `S` in `W_0`, `Phi(z_S)` lies in `D_e=C1`.  Its
square is `1`, so `Phi(z_S)=s(S)1` with `s(S)=+-1`, and `s` is a homomorphism
on `W_0`.

## Step 2. Nonzero atoms form a coset

**Claim.**  `Phi(Pi_phi) != 0` if and only if `phi(S)=s(S)` for all `S` in
`W_0`.

- **Mismatch.**  Suppose `phi(S) != s(S)` for some `S` in `W_0`.  Apply
  `Phi` to `(P0)`: `s(S)Phi(Pi_phi) = phi(S)Phi(Pi_phi)`.  So
  `2Phi(Pi_phi)=0`, and `Phi(Pi_phi)=0`.
- **Match.**  Suppose `phi|W_0 = s`.  By `(P0)` and Step 1, the `D_e`
  component of `Phi(Pi_phi)` is
  `2^(-k) sum_(S in W_0) phi(S)s(S) 1 = 2^(-k)|W_0| 1`, which is nonzero.
  Every other `S` contributes only to components of degree `!= e`.  So
  `Phi(Pi_phi) != 0`.

The characters of `F_2^c` that restrict to `s` on `W_0` form a coset of
`W_0^perp`.  So

```text
N_c = {phi : Phi(Pi_phi) != 0}                                          (P2)
```

is an affine subspace of `F_2^c`.  Since `Phi` kills forbidden atoms,
`N_c` is contained in the allowed set.  By `(P0)` it is nonempty.

## Step 3. At most two active answers

Take the exactly-one context of question `i`.  Its allowed set is the set of
one-hot vectors `e_a`.  An affine subspace containing distinct `e_a, e_b, e_c`
also contains `e_a+e_b+e_c`, which has weight three.  So `|N_i| <= 2`.

For each answer `a`, `T_(x_(i,a))` is the sum of the atoms with `x_(i,a)`
true.  In `A(B_G)` the only allowed such atom is `e_a`, so
`T_(x_(i,a)) = Pi_(e_a)`.  Put

```text
P_(i,a) = Phi(T_(x_(i,a))),
```

and call `a` active if `P_(i,a) != 0`, that is, if `e_a` is in `N_i`.  The
active `P_(i,a)` are pairwise orthogonal idempotents, and by `(P0)` they sum
to `1`.

## Step 4. 2-SAT collapse (algebraic, no trace)

**Order.**  For commuting idempotents write `E <= F` when `E=EF=FE`.  This
relation is transitive.  If `E=EF=FE` and `F=FG=GF`, then

```text
EG = EFG = EF = E,        GE = GFE = FE = E.
```

**Forbidden pairs.**  Consider a losing pair `(i,a),(j,b)`.  Its context
kills the true/true atom, so `P_(i,a)P_(j,b)=0`, and the two idempotents
commute.  Suppose both are active.

- If question `j` has only one active answer, then `P_(j,b)=1`, so
  `P_(i,a)=0`.  That is impossible, so this case does not occur.
- Otherwise `j` has exactly two active answers `b` and `b'`, and
  `P_(j,b')=1-P_(j,b)`.  Then

  ```text
  P_(i,a) = P_(i,a)(1-P_(j,b)) = (1-P_(j,b))P_(i,a),
  so   P_(i,a) <= P_(j,b').                                            (P3)
  ```

**The 2-CNF.**  Take one Boolean variable `y_i` for each question with two
active answers.  Questions with one active answer are constants.  For each
losing pair of active answers, add the clause
`not(y_i=a) or not(y_j=b)`.  Its implication-graph arrows are
`(y_i=a) -> (y_j=b')` and `(y_j=b) -> (y_i=a')`.  By `(P3)`, each arrow is an
order relation between the corresponding `P`.

If the 2-CNF were unsatisfiable, then by Aspvall--Plass--Tarjan (1979) some
literal `ell` would have a directed path to its negation.  By transitivity,
`P_ell <= P_(not ell) = 1-P_ell`.  This gives `P_ell = P_ell(1-P_ell) = 0`,
which contradicts `ell` being active.

## Step 5. Classical strategy

Choose a satisfying assignment `y`.  Give each question `i` the answer
`y_i`, or its unique active answer if it has only one.

- **Exactly-one constraints hold.**  Set `x_(i,a)=1` exactly for the chosen
  answer.
- **Forbidden pairs hold.**  Chosen answers are active.  If two chosen
  answers were a losing pair, their clause would be violated.

So the answer function wins every question pair, and `G` has a perfect
deterministic strategy.  This proves the Theorem.

## Corollary

**The grading.**  Let `C=C_Gamma(z)`.  For `h` in `C`, `P_z h = (h-zh)/2`
commutes with `P_z`, is supported on the coset `h<z>`, and is nonzero because
`z != 1`.  Also `P_z zh = -P_z h`, and `(P_z h)(P_z h') = P_z hh'`.

So `D = P_z C[C]` is a unital subalgebra of `P_z C[Gamma] P_z`, with unit
`P_z`.  It is graded by `H=C/<z>`, with one-dimensional components
`C P_z h`, because distinct cosets have disjoint supports.  Its identity
component is `C P_z`.

**The conclusion.**  Images as in `(GCB2)` are homogeneous in `D`.  The
Theorem then gives a perfect classical strategy for `G_loop`.  But
`lin-explicit-fixed-bcs-gap-via-generic-conversion` gives
`omega_q^s(B_loop) <= 1-delta_loop < 1`, and a classical strategy is a
quantum one.  This contradiction proves the Corollary.

**Other targets.**

- *Twisted group algebra.*  `C^alpha[H]` with basis `u_h` is graded by `H`,
  and its identity component is `C u_e`.
- *Central sign.*  For `J` central of order two, `C[Gamma']/(J+1)` is a
  twisted group algebra of `Gamma'/<J>`.  The images of group elements are
  homogeneous there.
