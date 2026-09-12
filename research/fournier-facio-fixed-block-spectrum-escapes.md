---
rg: 2
id: fournier-facio-fixed-block-spectrum-escapes
kind: claim
title: A Fournier--Facio block witness needs spectral complexity at infinity on a positive fixed sector
invalidates:
  - fournier-facio-bounded-spectral-type-block-witness
distinct_from:
  fournier-facio-block-dimension-escapes-every-charge-cutoff: That forces the ambient block dimensions to infinity; this forces the number of distinct eigenphases of one internal actor to infinity on a positive-charge fixed-block sector.
  fournier-facio-bounded-block-near-witness-impossible: That uses compactness of all of `U(d)` under a dimension bound; this permits arbitrarily large multiplicities and only bounds the spectral type of one fixed-block actor.
  finite-spectrum-unitary-power-recurrence: That is the abstract recurrence lemma; this combines it with nonsoficity, torsion-freeness, and essential freeness to locate a positive-charge sector where every bounded spectral cutoff vanishes.
---

**ESTABLISHED INTERNAL-DYNAMICS FENCE.**  Consider any common finite-block
candidate for the Fournier--Facio Kahl--Schneider witness, after removing
charged-null errors as in
`fournier-facio-bounded-block-near-witness-impossible`.  Write its
block-monomial actors as

```text
B_g: ell^2(X_y) -> ell^2(X_(alpha_g y)),
nu(A)=mu(union_(y in A) X_y).                          (FFSE1)
```

Then the block permutations `alpha_g` form a `nu`-preserving near action.
Since the Fournier--Facio group is nonsofic, this near action cannot be
essentially free.  Hence there are `g!=1` and a fixed-block set

```text
F_g={y:alpha_g y=y},              nu(F_g)>0.            (FFSE2)
```

Let `U_(g,y)` be the internal unitary of `B_g` on a block in `F_g`.  For
every finite `m`,

```text
nu({y in F_g : U_(g,y) has at most m distinct eigenvalues})=0.   (FFSE3)
```

More strongly, for every finite `N`, the set

```text
{y in F_g : exists 1<=n<=N,
              ||U_(g,y)^n-I||_op < 1/4}               (FFSE4)
```

has `nu`-charge zero.  Thus large spectator multiplicity does not evade the
recurrence argument.  On a positive-charge fixed sector, the actual spectral
type—and not only the block dimension—must escape every finite cutoff.

The proof uses the regular character at every nonzero power.  If `(FFSE4)`
had positive charge, finite additivity would choose one `n<=N` on a positive
subsector.  Charged near multiplicativity identifies `B_(g^n)` with `B_g^n`
there modulo a null set, so `B_(g^n)` would have diagonal coefficient bounded
away from zero on positive basis charge.  The group is torsion-free, hence
`g^n!=1`, contradicting essential freeness.  Finally the simultaneous
eigenphase recurrence theorem gives a bound `N=N(m)` for every unitary with
at most `m` distinct eigenvalues, independently of their multiplicities;
this proves `(FFSE3)`.

Consequently a surviving dimension-at-infinity construction cannot use
large amplifications of a bounded list of scalar phases, bounded-order
internal actors, or any fixed finite-dimensional commutative coefficient
algebra on the positive fixed sector.  It needs genuinely increasing
spectral entropy (or it must abandon the common-block architecture entirely).

Proof: `fournier-facio-fixed-block-spectrum-escape-proof`.
