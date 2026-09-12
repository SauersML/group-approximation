# Differential audit: what the non-MF breakthrough contributes to the hyperlinear problem

Date: 2026-08-13

## Outcome

The proof in `non_mf_groups_exist.tex` cannot be transferred by changing
operator norm to normalized Hilbert--Schmidt norm.  This is not merely an
estimate that has not yet been sharpened: the literal marked word has an
explicit Connes-embeddable Clifford-tower representation in which it is
`-1`.  Any universal tracial kill theorem for that word is false.

The non-MF work nevertheless contributes the correct architecture for a
nonhyperlinearity theorem.  The reusable pieces are:

1. isolate one nontrivial marked element in a finite presentation;
2. make finite-dimensional representations kill it;
3. use a central finite-order sector so the marked part can be compressed
   and its trace renormalized; and
4. reduce the analytic contradiction to one finite-multiplicity matrix
   identity.

For normalized Hilbert--Schmidt models the replacement for the MF radical is
the **hyperlinear residual**.  The final target is therefore

```text
1 != x in Rad_hyp(G).                                  (DHA1)
```

The formal implication `(DHA1) => G is nonhyperlinear` is now Lean-checked
as `not_isHyperlinear_of_mem_hyperlinearResidual` in
`GroupApproximation/Sofic/RadicalSeparation.lean`.

## 1. Layer-by-layer comparison

| Non-MF ingredient | Tracial status | Evidence |
| --- | --- | --- |
| Finite marked presentation and external witness `w != 1` | survives exactly | `LiteralNonMFPresentation`, `LiteralNonMFLinearWitness` |
| Functorial radical propagation and normal-generation implantation | survives for any target class closed under composition | `NormMFResidualFunctorial`; the same kernel argument defines `hyperlinearResidual` |
| Cutting a central involution to its negative spectral sector | survives | a detecting model has a nonzero negative cut; after compression its trace is renormalized |
| Adjoint multiplicativity | survives in normalized `2`-norm | `Ad U=U tensor conjugate(U)` and `||Ad U-Ad V||_2 <= sqrt(2)||U-V||_2` |
| Kazhdan fixed-space projection on the adjoint Hilbert ultraproduct | survives | ordinary property `(T)` applies to the resulting Hilbert-space representation |
| Coordinate projection recovery with operator-norm control | fails | normalized `2`-norm permits exceptional adjoint sectors of rank `o(d^2)` |
| Stable-finite/equal-rank pinning of the distinguished vector | fails after the preceding loss | equality in the tracial matrix quotient does not control a vector concentrated in a null-rank sector |

The last two rows are the exact dividing line.  The finite tracial identity

```text
||(1-P) W P||_2^2 = ||P W (1-P)||_2^2                (DHA2)
```

is valid and Lean-checked in `Sofic/UnitaryProjectionBalance.lean`.  What is
missing is a canonical projection `P` in the same finite multiplicity
coordinates as the marked transport.  Abstract von Neumann algebra
projections do not provide those coordinates.

## 2. Why the literal non-MF group is the wrong tracial candidate

`TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` constructs a
Connes-embeddable representation of the literal group in which

```text
w |-> -1.                                              (DHA3)
```

Consequently

```text
w in Rad_MF(E),        w notin Rad_hyp(E).             (DHA4)
```

This rules out all proposals whose conclusion is that every tracial matrix
model of the literal presentation kills `w`, including an unrestricted
tracial analogue of the non-MF commutant argument.  The eight-lamp
`M_16` spin packet and its positive central corner remain useful structural
information, but they cannot reverse `(DHA3)`.

## 3. The direct descendant: the Leavitt--Steinberg fork

The non-MF development already produced a better tracial candidate:

```text
U = St_5(L_(F_2)(1,2)),
Q = EL_4(L_(F_2)(1,2)).                                (DHA5)
```

The repository has established the following conditional fork.

```text
U normalized-HS stable   => U is nonhyperlinear,
U normalized-HS unstable => Q is hyperlinear and nonsofic. (DHA6)
```

The reason is unusually sharp.  Every finite-dimensional unitary
representation of `U` is trivial, while `U` is quasisimple and `Q` is its
simple nonsofic central quotient.  Thus stability would collapse every
hyperlinear model, whereas instability itself supplies a nontrivial tracial
ultraproduct image and hence a hyperlinear central quotient.  See
`ATLAS_HS_CRITERION.md` and the stability-fork section of `NOTEPAD.md`.

This is the strongest current way to build directly on the non-MF advances:
the same finite-versus-infinite compression geometry now yields a genuine
win--win theorem, and only selection of the branch remains.

## 4. First live theorem not already proved or disproved

The existing atlas work has already closed the following shortcuts:

- ring-first finite-trace models, by the Leavitt trace floor;
- separate Reynolds/Kazhdan recovery of the two charts;
- common finite-subgroup alignment;
- type-only Hall deficiency; and
- compact/Bogoljubov or exact finite-image constructions.

The earliest live matrix statement is narrower:

> **Finite-multiplicity coefficient extraction.**  In an exact
> finite-dimensional representation of the virtually free atlas source whose
> fixed quotient relators have normalized-HS defect tending to zero, place one
> comb-transported coefficient cut asymptotically in the raw four-character
> coefficient space, in the same finite multiplicity coordinates.

The endpoint has a strict numerical gap.  The transported cut has squared
distance

```text
15/128                                                     (DHA7)
```

from that raw coefficient space in the exact regular model.  Thus genuine
finite-coordinate membership would contradict the fixed moments.  See
`TRUE_COEFFICIENT_EXPECTATION_GAP.md` and
`FALSE_EXISTING_REYNOLDS_DOES_NOT_ALIGN_COEFFICIENT_C4.md`.

This extraction theorem is the first unproved step that is neither a restatement
of the goal nor already refuted by an exact countermodel.  It must use finite
matrix multiplicities; a purely algebraic or finite-von-Neumann-algebra proof
would also apply to the regular representation and is therefore impossible.

## 5. Formal endpoint now available

The Lean library now contains both radical directions needed by the two
active programs:

```text
sofic-invisible + one hyperlinear detector
  => a hyperlinear nonsofic range,

nontrivial hyperlinear-invisible element
  => the source group is nonhyperlinear.               (DHA8)
```

The second implication is supplied by:

```text
hyperlinearResidual_eq_bot_of_isHyperlinear
not_isHyperlinear_of_hyperlinearInvisible
not_isHyperlinear_of_mem_hyperlinearResidual
```

in `Sofic/RadicalSeparation.lean`.  Therefore a successful atlas extraction
can terminate directly in the requested universal-hyperlinearity
counterexample; no further semantic bridge will be needed.

## Research rule

Before starting a proposed repair, search `notes/AGENDA.md`,
`notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`, and the `TRUE_`/`FALSE_` notes
for the same mechanism.  In particular, do not retry compact Bogoljubov
approximation, separate Reynolds alignment, or a universal tracial kill of
the literal non-MF mark.
