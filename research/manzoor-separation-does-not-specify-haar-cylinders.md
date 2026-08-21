---
rg: 2
id: manzoor-separation-does-not-specify-haar-cylinders
kind: claim
title: Manzoor's separation proof does not specify a Haar-testable IRS cylinder law
distinct_from:
  manzoor-irs-quantum-value-gap: that establishes existence of an IRS/quantum value gap; this audits what finite stabilizer probabilities the proof actually identifies and shows that it does not name the witness law.
  explicit-zpc-irs-gap-game-witness: that asks to name a concrete separated tailored game; this shows why such an additional witness is prerequisite to a cylinder-by-cylinder Haar-linearity test of the published IRS.
  haar-algebraic-actions-have-permutation-koopman-spectrum: that supplies the reciprocal-index test once an IRS law is known; this proves that the Manzoor construction does not provide the joint cylinder values needed to run that test.
---

The proof of Manzoor's non-cohyperlinear IRS theorem does **not** define one
canonical IRS with a computable stabilizer-cylinder law.

For a game with answer length `m`, its IRS correlation uses only the one-word
membership probabilities

```text
t(w)=Pr[w in H].                                         (MHC1)
```

Indeed, writing `u_(x,I)=product_(i in I) u_(x,i)`, one has exactly

```text
p(a,b|x,y)
 = 2^(-2m) sum_(I,L subset [m])
     (-1)^(sum_(i in I)a_i + sum_(j in L)b_j)
     ( t(u_(x,I)u_(y,L)) - t(Ju_(x,I)u_(y,L)) ).        (MHC2)
```

Thus the game functional does not determine joint cylinders

```text
Pr[w_1,...,w_k in H],                                   (MHC3)
```

which are the quantities constrained to `0` or `p^(-r)` for stabilizers of a
Haar `F_p`-linear action.

This loss is intrinsic, not merely caused by the game using finitely many
words.  `irs-character-does-not-determine-haar-cylinders` gives two explicit
IRSs on `S_3` (and hence, by pullback, on `F_2`) with identical values of
`t(w)` for **every** word but different two-word cylinders.  Thus even a full
oracle for Manzoor's GNS trace would not identify the measure-level data
needed for a direct Haar-stabilizer test.

The only explicit cylinder values imposed in the paper are the strategy
axioms:

```text
Pr[J in H]=0,
Pr[u^2 in H]=1,
Pr[[u,J] in H]=1,
Pr[[u,v] in H]=1       for u,v in one question.         (MHC4)
```

Finite intersections of the probability-one events in `(MHC4)` still have
probability one.  Every displayed value is compatible with the Haar
reciprocal-index screen, so none is a violating cylinder.

At the existence step, Manzoor argues by contradiction that *some* game has
`omega_IRS>omega*`; no machine/game is selected.  The proof then chooses an
unspecified above-gap IRS strategy, and the final ergodic conclusion chooses
an unspecified extreme non-cohyperlinear IRS by convex separation.  Hence
the source supplies neither a named finite game nor an oracle for `(MHC1)` or
`(MHC3)`.  A numerical finite-cylinder Haar audit of "the Manzoor IRS" cannot
be performed from the published construction.

There is a trivial distinction worth making precise.  Read literally as a
measure on subgroup indicator configurations in `{0,1}^F`, no IRS is Haar
measure on a linear subshift: the identity coordinate is identically `1` on
every subgroup, whereas a linear subshift contains its zero configuration
and a Haar character coordinate is either identically `0` or uniform, never
identically `1`.  The nontrivial surviving question is instead whether a
p.m.p. realization of the IRS is a **stabilizer pushforward or measurable
factor** of some Haar algebraic action.  Neither `(MHC2)` nor the
non-cohyperlinearity conclusion decides that question.

Primary source: Manzoor,
[*There is an equivalence relation whose von Neumann algebra is not Connes
embeddable*](https://arxiv.org/html/2502.06697v2), Definition 3.4 and the
correlation formula preceding Theorem 3.5, the finite-word expansion in
Section 3.2, Definition 3.11, and Theorem 3.13 plus the proof of Theorems
1.1--1.2.
