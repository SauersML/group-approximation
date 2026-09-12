# Spatial overgroups and the retained shell stabilizer, 2026-09-08

Boone--Higman remains open in this work. The terminated-digit
construction supplies a restricted simple overgroup, but cannot
be made universal merely by requiring arbitrary inputs to act
rationally. This audit studies overgroups without that restriction.

## Recover a spatial action from its marked presentation

For a Cantor group D containing the standard V, let V_U be its
finitely generated prefix subgroup supported in a clopen U.
The equation

    [g V_U g^-1, V_(C minus W)] = 1

detects exactly g(U) subset W. The finite generating sets reduce
this to finitely many group equations. The existing normal-kernel
discriminator gives decidable word problem from a recursive
presentation of D. Enumerating W and testing both inclusions then
computes g(U) exactly.

This is an effective reconstruction of the whole clopen action,
not only the previously computed shell enumeration. It also proves
uniqueness of a faithful action extending a fixed standard V marking.
When a computable point has a marked finitely generated stabilizer,
stabilizer membership is decidable by parallel equality and moved-point
searches. Existence of a spatial overgroup, and finite generation of
its point stabilizers, remain separate requirements.

## Retain the shell stabilizer in an abstract overgroup

For E=E_nu and H=E_p, core_E(H)=1 because the shell orbit is dense.
Hence core_Gamma(H)=1 in every abstract overgroup Gamma. The induced
Gamma/H action is faithful and all its stabilizers are finitely
generated. Its restriction to E/H is the original highly transitive
shell action.

If Gamma is finitely presented, the remaining condition for the
[type (A) embedding theorem](https://arxiv.org/pdf/2405.18354) is
exactly finiteness of H\Gamma/H. This allows E to remain non-finitely
presented. The new OPEN host claim weakens the previous requirement
that E itself have a finite presentation, since Gamma=E recovers
that earlier special case. No converse or universal host is claimed.

Choosing the effective free-near enumeration gives a decidable,
non-finitely-presented E for every infinite decidable input. Clapham
therefore supplies abstract finitely presented overgroups already.
This observation alone is not close to verifying type (A): even
a regular action of a finitely presented group satisfies its other
three conditions. Finite pair-orbit control is the substantive gap.

## A necessary intersection condition and a failed host choice

For any gamma, the H orbits meeting gamma E/H correspond exactly
to the orbits of E intersect gamma^-1 H gamma on E/H. Finite
bi-index therefore forces each of these intersection groups to
have finitely many orbits, and in particular to be infinite.
Thus E must have infinite intersection with every conjugate of
itself in a successful host.

[Wagner's malnormal Higman theorem](https://arxiv.org/pdf/2404.00841)
does supply finitely presented overgroups preserving decidable word
problem. But a proper malnormal embedding makes the displayed
intersection trivial for gamma outside E, creating infinitely many
pair orbits. More generally a proper almost malnormal embedding
fails. This excludes the induced action retaining H, not every
action or quotient of those overgroups.

The next construction must control these intersections and double
cosets, or extend the spatial action with a different finitely
generated stabilizer. Neither construction is provided here. All
arguments in this artifact are written proofs with the cited
imports; no Lean certificate or GPU result is asserted.

## The existing contracting host also fails the retained-stabilizer test

The terminated-digit model has a continuous equivariant collapse
pi onto the original binary Cantor space: each final infinite digit
block becomes an infinite binary zero tail. Let F_p be the fiber
over p and S the lifted original point stabilizer. Left and right
multiplication by S preserve the number of fibers met by gamma(F_p).

Partition F_p by its first L digits and root edge, giving r*h^L
pieces. Canonical prefix swaps move those pieces into distinct
fibers with binary labels 1*0^(n_j)*1*0^infinity. The swaps have
disjoint clopen domains and ranges, so they define explicit
involutions in H_(h,r). Their image-fiber counts r*h^L give
infinitely many S double cosets.

Thus H_(59,4) and every larger host containing it fail the new
criterion for the retained A5 shell stabilizer. This does not
conflict with the existing finitely presented simple embedding;
it demonstrates that the retained-stabilizer condition asks for
more structure than a simple overgroup alone.

## Remote validation

The reconstruction, induced-action, and intersection proofs were
committed in `92d4d0708`. The first integration
`1b34292123f1cf1172365da0c2e67d4c3f059d32` passed
[run 34303946953](https://github.com/SauersML/group-approximation/actions/runs/34303946953).
The additional fiber-count proof was committed in `c347e963e`.
The complete batch passed
[run 34304220316](https://github.com/SauersML/group-approximation/actions/runs/34304220316)
at exact head `7d52abdc9433fa5cde0fd879cedf6445955b760e`.

The downloaded exports in `.cairn/bh-spatial-overgroup-check-20260908/`
record the four new proved claims as `ESTABLISHED` through their
written routes. The finite-bi-index host hypothesis, its universal
Boone--Higman route, and the conjecture itself remain `OPEN`. The
earlier A5 simple-host claim remains `ESTABLISHED`.

The workflow checks source syntax, existing exact finite controls,
and the Cairn graph. Its success is structural validation, not
independent verification of these mathematical arguments. Lean
preflight was skipped; no GPU computation was run.
