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
