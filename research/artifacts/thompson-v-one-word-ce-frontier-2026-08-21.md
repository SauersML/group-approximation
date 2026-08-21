# Bare Thompson V as a one-word Connes-embeddability test

**Date:** 2026-08-21

This note isolates a nonduplicate Thompson-group lane. It does not use the
repository's Thompson-addressed Clifford tape, a central phase, a BCS
decoder, or a multiplicity return.

## Exact reduction

Let `V=G_(2,1)`, fix `w!=1`, and put

```text
q_w=(1-w)^*(1-w).
```

Dudko--Medynets classify the indecomposable characters of `G_(n,r)` as the
regular character and scalar characters coming from the abelianization
(*Finite factor representations of Higman--Thompson groups*, Groups Geom.
Dyn. 8 (2014), Corollary 3.6(2)). For even `n` the relevant abelianization is
trivial. Hence every trace of `V` is

```text
tau_t=t tau_reg+(1-t)tau_triv,       0<=t<=1,
```

and `tau_t(q_w)=2t`.

If a trace with `t>0` is Connes embeddable, its GNS algebra contains the
regular central summand `L(V)` with nonzero trace. Connes embeddability passes
to corners, so `V` is hyperlinear. Conversely, hyperlinearity of `V` makes
all mixtures Connes embeddable. Therefore

```text
{tau(q_w): tau is a CE trace of V}={0} or [0,2].
```

Every exact finite-dimensional representation of `V` is trivial: a
nontrivial representation would be faithful by simplicity, and its finitely
generated linear image would be residually finite by Mal'cev, contradicting
the absence of nontrivial finite quotients. Thus the exact finite-dimensional
ceiling of `q_w` is zero.

## The precise open estimate

For one finite presentation of `V`, it suffices to prove constants
`delta,epsilon>0` such that

```text
def_R(U)<delta  =>  ||w(U)-I||_2^2<=2-epsilon
```

in every matrix dimension. Character rigidity then upgrades this strict
ceiling to zero at the CE-trace level. This estimate is equivalent to
nonhyperlinearity of `V`, but concentrates the problem into one scalar moment
and removes the need for a full correction theorem.

## Literature boundary

Fournier-Facio--Rangarajan, *Ulam stability of lamplighters and Thompson
groups*, Math. Ann. 389 (2024), Theorem 1.2, prove uniform stability with a
linear estimate for submultiplicative matrix norms. Their theorem covers the
operator norm and unnormalized Frobenius/Schatten norms. It does not cover
normalized Hilbert--Schmidt norm with dimension-free constants; Section 7
explicitly leaves Hilbert--Schmidt approximability of Thompson groups open.
The published proof architecture is therefore a possible source of ideas,
not evidence that the displayed estimate already holds.

## Duplication boundary

The generic character/corner maneuver and its use for a Thompson subgroup of
the Leavitt construction already occur in `notes/NOTEPAD.md`. The Cairn graph
did not previously package the bare-`V` binary support value. The generic
one-positive-element framework is `cyclic-carrier-energy-stability`; this
artifact records the special fact that for `V` merely obtaining a strict
bound below the regular value forces equality with the finite-dimensional
ceiling.

No formal positivity or sum-of-squares inequality valid in every tracial
representation can establish the strict ceiling: the exact regular
representation itself has energy `2`. Any successful proof must distinguish
matricial/Connes-embeddable traces from arbitrary tracial representations.
