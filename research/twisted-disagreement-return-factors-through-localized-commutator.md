---
rg: 2
id: twisted-disagreement-return-factors-through-localized-commutator
kind: claim
title: A matrix-only twisted disagreement return already contains a localized commutator return
distinct_from:
  deleted-large-row-phase-return-is-finite-clock-saturated: that assumes the transported and shared involutions commute in the abstract group and proves that the phase-corrected word is only an order-two clock; here they do not commute in the group, so both the commutator and phase-corrected words are Britton-wandering, but the proposed phase correction adds no analytic leverage.
  hnn-compressed-row-is-unnamed-fixed-carrier: that starts from a small heterogeneous intertwining row on a positive projection; here a large disagreement row plus a small localized commutator is converted to a soft return carrier and then shown to contain the simpler commutator carrier already.
---

Let

```text
Gamma=<H,t | t K t^(-1)=L>
```

be an HNN extension.  Let `a,b,J in H` be involutions, suppose `J` is
central in `Gamma`, and assume

```text
a notin L,                 b notin K.                    (TDR1)
```

Put

```text
c=t^(-1) a t,
g=c b c b,
u=a t (Jb)^(-1)t^(-1).                                 (TDR2)
```

Then `g` has infinite order.  If also `J in K` (as is automatic in the
usual central-sign HNN construction), then `Jb notin K`, so `u` has
infinite order as well.

Now evaluate the letters by exact involutions `A,B,J` and a unitary `T` in
a finite tracial algebra, with `J` central.  Write

```text
C=T^* A T.
```

Let `Q` be an arbitrary, possibly model-dependent projection which reduces
`C` and `B` and satisfies `JQ=-Q`.  Define the soft disagreement carrier

```text
X=Q(1-CB)/2,                  Y=T X.                    (TDR3)
```

Then `X` is a contraction and the following identities are exact:

```text
||X||_2^2 = (1/4)||Q(C-B)||_2^2,                       (TDR4)

||(u-1)Y||_2 = (1/2)||Q(CB-BC)||_2,                    (TDR5)

||(g-1)Q||_2 = ||Q(CB-BC)||_2.                         (TDR6)
```

Here `(TDR5)` denotes the displayed matrix evaluation
`A T (JB)^(-1)T^*` of `u`, and `(TDR6)` the evaluation `CBCB` of `g`.
If corrected exact letters lie at normalized-HS distances
`epsilon_A,epsilon_B,epsilon_J,epsilon_T` from the actual word evaluations,
then the right side of `(TDR5)` acquires at most

```text
epsilon_A+epsilon_B+epsilon_J+2 epsilon_T              (TDR7)
```

and the analogous word-length telescoping error applies to `(TDR6)`.

Consequently, for a fixed finite menu of such rows, any matrix-only estimate

```text
sum_i ||Q_i(C_i-B_i)||_2^2 >= Delta-o(1),
max_i ||Q_i(C_iB_i-B_iC_i)||_2=o(1)                    (TDR8)
```

does yield an unnamed positive-mass return: some `X_i` has squared mass at
least `Delta/(4m)-o(1)` and is returned by the corresponding infinite-order
word `u_i`.  However the sign twist is redundant.  Since

```text
||Q_i(C_i-B_i)||_2^2 <= 4 tau(Q_i),                    (TDR9)
```

the same selected `Q_i` has trace at least `Delta/(4m)-o(1)`, and `(TDR6)`
makes it an approximate fixed carrier for the simpler infinite-order
commutator `g_i`.  The finite-menu Fejer theorem therefore closes already
from localized cross-commutation; neither disagreement nor `J` is needed
after positive carrier mass is known.

This identifies the exact surviving gate.  The cross-commutation must be a
finite-matrix-only statement on an **unnamed** positive-density reducing
corner.  If it is imposed as an abstract group relator, Britton wandering is
lost as in `deleted-large-row-phase-return-is-finite-clock-saturated`.  If
the corner is a fixed group-algebra projection, convergence of its localized
group-algebra norm contradicts the canonical character directly.  Thus the
phase-corrected deleted-row idea does not evade the existing localization
compiler: it repackages that compiler as positive-density localized
cross-commutation.

## Audit of existing sources

- The current Fanizza/private--shared cells expose exact local commuting
  context packets, but no established claim transfers that commutation to a
  common positive-density **unnamed** carrier while leaving the abstract
  cross-commutator unreduced.  The common modular swap establishes exact
  completeness only; exposing it in finite ordinary-word microstates is the
  open `common-partial-isometry-swap-game-compiler`/heterogeneous-row gate.
- The two-field matching theorem propagates commutators only for tables
  whose sampled matching commutators are already small; making those sampled
  rows matrix-only rather than relators is exactly the missing native-gap
  input, and its quantitative constant grows with rank.
- The arithmetic relative-commutant lane does produce the right *form* of
  an unnamed positive-density projection, but proving cross-commutation on
  it is precisely `canonical-iwahori-projection-commutant-transfer`.  The
  present calculation does not weaken that transfer theorem.

In particular, selecting an affine or local anticorrelation row does not
avoid predicate energy by itself.  Affine packet relations can enforce the
commutation as an ordinary tracial consequence, in which case the regular
representation enforces it too and the wandering word collapses.  What is
needed is still a finite-only localization theorem; once that theorem gives
positive-density cross-commutation, the direct word `g` is already the
shortest terminal.
