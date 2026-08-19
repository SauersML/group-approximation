# Effective witness rank is the exact weak-MF-to-FALSE profile

Date: 2026-08-12

## 1. Outcome

Let `K` be countable and let

```text
1!=q in Rad_sof(K).
```

Suppose `phi_n:K->U(d_n)` are operator-norm almost representations on
exhausting multiplication windows.  Let `epsilon_n` bound their
operator-norm multiplicative defect and put

```text
A_n=phi_n(q)-1.
```

Use the unnormalized Frobenius norm `||.||_F` and define the stable/effective
rank

```text
r_eff(A_n)=||A_n||_F^2/||A_n||_op^2.                 (ERP1)
```

The phase-cancelled tensor amplifier gives the exact sufficient condition

```text
epsilon_n^2 d_n/||A_n||_F^2 ->0.                    (ERP2)
```

If the norm models retain a fixed operator wall

```text
||A_n||_op>=alpha>0,                                 (ERP3)
```

then the transparent stronger condition

```text
epsilon_n sqrt(d_n/r_eff(A_n))->0                    (ERP4)
```

suffices.  Thus the old square-root profile
`epsilon_n sqrt(d_n)->0` is only the rank-one worst case.  A witness spread
over effective rank comparable to `d_n` needs no quantitative rate beyond
`epsilon_n->0`.

## 2. Proof

The normalized trace gap is exactly

```text
kappa_n=1-Re tr_(d_n)(phi_n(q))
       =(1/(2d_n))||A_n||_F^2.                       (ERP5)
```

Operator norm dominates normalized Hilbert--Schmidt norm, so the
multiplicative defect `eta_n` used in the trace-gap amplifier satisfies

```text
eta_n<=epsilon_n.                                     (ERP6)
```

Therefore `(ERP2)` gives

```text
eta_n^2/kappa_n
 <=2 epsilon_n^2 d_n/||A_n||_F^2
 ->0.                                                 (ERP7)
```

Lemma 1 of `FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md` produces a
hyperlinear image retaining `q`, and the full-sofic-radical property makes
that image nonsofic.

Under `(ERP3)`, equation `(ERP1)` gives

```text
||A_n||_F^2>=alpha^2 r_eff(A_n),
```

so `(ERP4)` implies `(ERP2)`.  End proof.

The same statement may be phrased with a threshold rank.  If at least
`r_n` singular values of `A_n` are at least `alpha`, then

```text
||A_n||_F^2>=alpha^2 r_n,
```

and

```text
epsilon_n sqrt(d_n/r_n)->0                            (ERP8)
```

is sufficient.

## 3. Application to the banked weak-MF nonsofic double

Shulman's symmetric-amalgam theorem supplies operator-norm models of the
Kun--Thom free-lamp group which keep its radical witness visible in operator
norm.  For those models, define `r_eff` by `(ERP1)`.  The remaining analytic
target is now the single measurable profile `(ERP4)`.

This strictly refines the previously recorded rank-blind condition:

* a rank-one witness requires `epsilon_n sqrt(d_n)->0`;
* rank `d_n^beta` requires
  `epsilon_n d_n^((1-beta)/2)->0`;
* positive effective-rank density requires only `epsilon_n->0`.

No exterior/Fock functor is needed once `(ERP2)` is verified.  The
conjugate-and-identity tensor amplifier both spreads the marked trace and
keeps relation accumulation quadratic.

## 4. Exact ambient representations cannot realize the profile

The finite-representation matching theorem explains where the effective
rank must come from.  If the ambient `G`-letters are an exact
finite-dimensional representation and `V_n` is the almost-central lamp,
property `(T)` gives, for the radical witness `q`,

```text
||phi_n(q)-1||_(2,d_n)<=C epsilon_n.                  (ERP9)
```

Equivalently,

```text
||A_n||_F^2<=C^2 epsilon_n^2 d_n.                    (ERP10)
```

Thus the left side of `(ERP2)` is bounded below by `1/C^2`; it cannot tend
to zero.  The effective-rank profile can only be obtained by spending
defect inside the ambient `G`-sector itself.  In the terminology already
used in the repository, it forces a concrete unnormalized-Frobenius
instability sequence for `G`.

## 5. What a computation must report

A norm optimizer or lift audit which reports only operator separation is
not informative enough.  For every candidate coordinate it must report

```text
epsilon_n,
d_n,
||phi_n(q)-1||_F^2,
r_eff(phi_n(q)-1),
epsilon_n^2 d_n/||phi_n(q)-1||_F^2.                  (ERP11)
```

The last number is the stopping statistic.  A subsequence on which it tends
to zero proves the desired hyperlinear-nonsofic separation.  A uniform
positive lower bound for a structurally complete model family is a genuine
no-go for that family.
