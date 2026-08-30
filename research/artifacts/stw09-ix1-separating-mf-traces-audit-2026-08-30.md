# STW Problem IX(1): jointly faithful MF traces audit (2026-08-30)

## Status and source boundary

The current author-hosted version of Schafhauser--Tikuisis--White,
[Nuclear C*-algebras: 99 problems](https://mysite.science.uottawa.ca/atikuisis/STW.pdf),
was checked on 2026-08-30.  Problem IX(1) still asks whether every separable
nuclear C-star algebra with a faithful trace is quasidiagonal.  Its recorded
general positive result assumes the UCT.  The theorem added here does not
claim to remove the faithful trace or to settle the unrestricted problem.

## Existing proof-graph routes checked

The direct IX(1) graph previously had two routes:

- `stw99-vii-implies-ix1` observes that a faithful trace forces stable
  finiteness and then invokes the still-open Problem VII;
- `stw99-x1-implies-ix1` would make the faithful nuclear trace
  quasidiagonal from the still-open amenable-trace Problem X(1), then use
  faithfulness to obtain an MF embedding.

The nearby established theorem
`faithful-mf-models-realize-all-mf-traces` was also checked.  It starts with
an algebra already known to be MF and shows that any prescribed MF trace can
be realized by faithful norm-corona coordinates after direct-sum
reweighting.  It cannot prove that an algebra is MF in the first place.

The new theorem runs in the opposite direction.  A family of possibly
nonfaithful MF traces is allowed.  Their square-null sets must have zero
intersection.  The trace coordinates then jointly separate points in a
product of matrix norm coronas, and a finite selection/direct-sum argument
turns that product separation into the sequential finite-packet models
required for MF.  This is not the active Problem VII lane: stable finiteness
alone supplies no MF trace models and is not used in the proof.

## Proof audit

There are three points at which an informal proof could overstate the result.

1. An MF trace need not have faithful support.  The proof uses only the exact
   implication

   ```text
   Phi_sigma(a)=0  =>  sigma(a* a)=0,
   ```

   which follows from operator-norm asymptotic multiplicativity and trace
   convergence.  It never asserts the converse for one trace.

2. An embedding into an uncountable product of coronas is not silently called
   an MF sequence.  On each finite packet, only finitely many traces are
   selected, one nearly norming each test element.  Far-out coordinates from
   those finitely many models are block-summed.  Defects are maxima across
   blocks, and separability provides the final diagonal sequence.

3. A faithful trace in the weak-star closed convex hull of MF traces is only
   used to verify joint faithfulness.  It is not asserted to be an MF trace:
   weak-star limits need not come with a single operator-norm microstate
   sequence.  If all MF traces vanished on a nonzero `a* a`, however, every
   convex combination and its weak-star closure would vanish there, contrary
   to faithfulness.

After the internal MF conclusion, nuclearity is used exactly once through
the standard Blackadar--Kirchberg nuclear-MF/NF characterization.  The
unrestricted IX(1) root remains open because a general faithful nuclear
trace is not known to lie in the weak-star closed convex hull of MF traces.
