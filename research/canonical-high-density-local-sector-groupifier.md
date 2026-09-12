---
rg: 2
id: canonical-high-density-local-sector-groupifier
kind: claim
title: Groupify one finite BCS on local sectors below the total Plancherel-deficit threshold
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for a literal homomorphism of the whole BCS algebra into one common corner; this permits different noncommuting local sectors and asks only for small total canonical codimension plus state-dependent local rows.
  common-partial-isometry-swap-game-compiler: that authenticates one common source partial isometry and all Gram rows on it; this asks the weaker geometric task of making the meet large by canonical density, after which no source word or partial isometry is needed.
  finite-product-selected-type-mark-does-not-align-carriers: that refutes inference of a meet from product moments; this explicitly requires a sum-of-codimensions bound which forces the meet in every finite matrix model.
---

OPEN.
For a fixed finite BCS game of finite-dimensional gap `Delta>0` and a perfect
commuting strategy, construct a finitely presented group `Gamma` with:

1. finite-subgroup algebra projections `q_c` whose canonical Plancherel
   masses `alpha_c` satisfy

   ```text
   sum_c(1-alpha_c)<Delta/(1+Delta);                         (CHD1)
   ```

2. group-word packets which, after exactifying those finite subgroups in a
   canonical matrix microstate, produce context PVMs, context involutions and
   Bob involutions with

   ```text
   ||F_cq_c||_2=o(1),
   ||(A_(c,x)-B_x)q_c||_2=o(1);                              (CHD2)
   ```

3. one exact representation realizing the perfect commuting strategy and
   keeping a specified group-algebra mark nonzero.

By `high-density-local-sectors-force-one-bcs-gram`, `(CHD1)--(CHD2)` exclude
canonical finite-dimensional microstates.  The exact marked representation
ensures the presentation is nontrivial, so the resulting group is
nonhyperlinear.

The sum condition `(CHD1)` is sufficient but no longer the sharp analytic
target.  By `common-meet-local-sectors-pay-one-deficit`, it may be replaced
by the strictly weaker authenticated-meet condition

```text
1-tau_Gamma(meet_c q_c)<Delta/(1+Delta).                   (CHD3)
```

In particular a literal common accepting projection pays its deficit only
once.  However equal local Plancherel masses do not imply `(CHD3)`:
`plancherel-marginals-do-not-control-sector-meet` realizes both the shared
and disjoint extremes inside one finite abelian regular packet.

The rowwise Hecke-CRT target is a genuinely weaker bypass of this claim.
`independent-row-masks-transfer-bcs-gap-to-ambient-identity` permits private
predicate and incidence masks and never forms their meet; its exact threshold
is the weighted row deficit `D_row<Delta`.  Consequently
`rowwise-hecke-crt-certificate-for-nonce-bcs` does not need `(CHD1)` or
`(CHD3)`.  It still needs one global context PVM and one global involution per
shared variable, so it does not license incidencewise replacement of the
logical observables.

## Attempts

The common irreducible selected-type atlas does not meet `(CHD1)`: a central
type projection has canonical mass `dim(rho)^2/|K|`, and taking one private
type per context accumulates the complementary Plancherel masses rather than
the selected masses.  Tensoring the complete context packets can force a
large literal meet, but `tensor-context-types-classicalize-common-source`
then destroys the perfect nonclassical witness.  The live possibility is a
high-rank **accepting** sector (large sum of types, not one selected type)
whose rejected complement pays only the local verifier row while distinct
context algebras remain noncommuting in the exact infinite model.

A common one-ghost rejection atom would quantitatively solve the density
bookkeeping through `(CHD3)`, but only if its identity across contexts is
authenticated without placing all context observables in one common finite
abelian algebra.  Sharing the full context packet classicalizes the witness;
sharing only the rejection atom is the precise remaining group-theoretic
interface.  Literal equality of the natural rank-one assignment atoms does
not achieve that separation: `literal-common-ghost-atom-classicalizes-contexts`
shows that their full group-basis support forces the entire elementary
abelian context subgroups to coincide.  The shared object must therefore be
higher-rank or nonliteral.

The literal higher-rank option is now classified by
`common-higher-rank-context-projections-are-syndrome-cylinders`.  A common
projection in two elementary-abelian context algebras lies in the algebra of
their subgroup intersection, so its rejected assignments are a union of
complete fibers of the shared parity syndrome.  This preserves private
noncommuting extensions but cannot isolate the one ghost.  The remaining
positive options are therefore a cylinder-predicate gap construction, or a
genuinely nonliteral Hecke/Morita overlap whose actual meet is authenticated
without literal equality in both context group algebras.

There is now an explicit nonabelian outer-packet solution to the density
part.  `standard-type-thin-common-reflection-sector` uses the standard type
of `S_n`: one transposition has a rank-one negative projection `e` and a
common complement `q` of relative trace `(n-2)/(n-1)`.  Taking `n` large
makes `(CHD3)` automatic and does not identify the private context groups.
The route `high-density-via-standard-reflection-corner` leaves only
`standard-reflection-sector-bcs-groupifier`: enforce the BCS and overlap rows
on this noncentral common complement by a block-escaping algebraic corner
construction.

For the rowwise bypass, `affine-frobenius-group-has-almost-full-simple-block`
gives a stronger absolute-density packet: one primitive block has canonical
mass `1-1/p` and is the full algebra `M_(p-1)(C)`.  Hence
`affine-frobenius-packets-solve-local-row-mask-storage` realizes every
rational local context profile with arbitrarily small predicate deficit.
This does not solve the claim above or the shared-variable problem.  The
remaining operation is exactly
`affine-frobenius-hecke-crt-shared-involution-interpolation`: one global
group-algebra involution must agree with several fixed context marginals on
different large noncommuting right ideals.
