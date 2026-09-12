---
rg: 2
id: multi-mover-block-amplification-repair
kind: route
title: Amplify the finite mover family into stagewise separation, then take the argmax
target: multi-mover-collapse-criterion
requires: []
artifacts:
  - GroupApproximation/Sofic/MaxDisplacement.lean
  - GroupApproximation/Sofic/MoverGeneration.lean
  - GroupApproximation/Sofic/CoronaSubsequence.lean
  - GroupApproximation/Sofic/BlockAmplificationRepair.lean
  - GroupApproximation/Sofic/BlockingFamilyRadical.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

## Why sufficient

Three layers, of which only the middle one is new relative to the 2026-08-15
sketch.

**Estimate layer — survives verbatim.**  Property (T) gives finite generation,
so with `K = Stab_Gamma(x_0)` the full stabilizer there are finitely many
moving generators `gamma_1, ..., gamma_m` with
`Gamma = <K, gamma_1, ..., gamma_m>` (`MoverGeneration.closure_stabilizer_union_movers`,
`movers_finite`).  Setting `k_n = max_i d_n(x_0, gamma_i x_0)`, every letter of
a word costs zero (stabilizer letters) or at most `k_n` (mover letters, and
their inverses by symmetry of the pseudometric), so
`delta_n(g) <= C_g (k_n + e_n)` for every fixed `g`
(`MaxDisplacement.dist_inv_smul_le`, `dist_smul_le_of_mem_closure`), and the
argmax mover has normalized displacement exactly one
(`exists_infinite_constant_argmax`).

**Corona layer — the repair.**  The step "pass to the argmax subsequence, so
the corresponding defect dies" is invalid in
`Q = prod M_{d_n} / sum M_{d_n}`: vanishing along a subsequence is not
vanishing there
(`CoronaSubsequence.exists_vanishing_on_subsequence_not_tendsto_zero`).  The
fix does not repair the inference; it removes the need for it.  Given a
homomorphism into the corona and a finite set `b_1, ..., b_m` of nonidentity
images, each has `limsup_n ||U_{b_i,n} - 1|| = c_i > 0`.  Build a new model
whose stage `k` is the block sum over `i` of stage `n_i(k)`, choosing
`n_i(k)` beyond stage `k` so that `||U_{b_i,n_i(k)} - 1|| >= c_i/2` and all
multiplication defects among the first `k` group elements are below `1/k`.
Block-diagonal operator norm is the maximum over blocks, so asymptotic
multiplicativity survives while **every** tested element keeps its own block
and its own lower bound at **every** stage
(`BlockAmplificationRepair.exists_stagewise_separated`).

**Contradiction.**  In the amplified model the normalization scale is positive
at all late stages — otherwise the zero-scale branch would drive every mover
defect to the identity along arbitrarily late stages, against the uniform
lower bounds just installed — so one may divide by `k_n`, fix the argmax index
on an infinite set, and run the unchanged analytic core.  It forces the
corresponding defect to the identity along that set, contradicting a bound
that now holds at every stage.  Hence no injective corona representation
exists: the ambient lamp-action group is not MF, with no distinguished-mover
hypothesis.  `BlockAmplificationRepair.not_isOperatorMF_of_no_multiMarked`
states exactly this, with the analytic core as its only hypothesis and
everything else unconditional.

## Scope

What is established is the non-MF conclusion from a finite mover family.  What
is **not** established, and is not claimed, is that a predetermined
`a_{gamma_i x_0} a_{x_0}` lies in `Rad_MF`: the bad index may vary with the
representation.  Pinning a named element still needs condition (iii), a
symmetry permuting the candidates, or the compression form, which gives
pointwise radical membership universally over the Kazhdan subgroup.

**Strengthened 2026-08-16, without contradicting the above.**  The blocking
conclusion is not merely existential per representation: *some* member of the
family lies in the radical outright.  Feed the blocking hypothesis the
universal corona representation of
`ActualCoronaMFRadical.exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual`,
whose kernel is exactly the radical, and the member it kills is in the radical.
No finiteness of the family is needed.  `Sofic/BlockingFamilyRadical.lean`.

The caution above stands as written: that argument names *a* member, not a
*predetermined* one, which is what the sentence denies.  The second route it
lists is also now exact rather than heuristic — the radical is fully invariant,
so an element inside the fully invariant closure of every member is in the
radical, and if endomorphisms act transitively on the family then every member
is.  That criterion is optimal given only full invariance plus meeting the
family.

`Sofic/BlockingFamilyRadical.lean` is kernel-checked as of 2026-08-16 and
root-imported; the first version of it did not elaborate.  It also carries the
conclusion in the form the multi-mover argument is used in
(`not_isCDEOperatorMF`: a blocking family avoiding the identity rules out an
injective corona representation) and the automorphism specialization of the
transitive case.

One earlier note is superseded rather than refined.  The docstring of
`Sofic/MultiMoverUniversalUpgrade` asserted that a transitively permuting
automorphism family does *not* give the upgrade, reasoning that precomposing a
fixed representation `Θ` by `σ` yields `(Θ ∘ σ)(w i₀) = 1` and so constrains
the composite rather than `Θ`.  That is a correct warning about that route and
a wrong verdict on the question: full invariance is a property of the radical,
which is an intersection over *all* representations, so the symmetry is applied
after the intersection and no representation is moved.  The upgrade does go
through, and for endomorphisms rather than only automorphisms.  That docstring
now records the failure as a failure of one route and points at this one; the
inner-conjugation case it proves is unaffected.

The ambient group in the conclusion is the whole lamp-action semidirect
product, not the lamp subgroup alone — for finite lamps the lamp subgroup is
locally finite, hence amenable and MF, so a non-MF statement about it would be
false.
