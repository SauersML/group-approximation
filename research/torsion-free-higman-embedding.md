---
rg: 2
id: torsion-free-higman-embedding
kind: claim
title: Torsion-free Higman embedding
---

Every recursively presented torsion-free group embeds into a finitely
presented torsion-free group.

A weaker statement is available and is enough for many purposes: there is a
**universal finitely presented torsion-free group**, one that contains a
copy of every finitely presented torsion-free group.  Fournier-Facio uses
exactly this as the first input of arXiv:2608.02025 Section 2, citing
Higman 1961, Belegradek--Szczepanski 2008, and Chiodo 2014; the repository
carries `GroupApproximation/Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean`
for the countable payload.  Verified at usage level (Fournier-Facio's text
read in full this session), not at the level of the three cited sources.
That form absorbs finitely presented torsion-free groups only, so it does
not by itself discharge the claim below, which is about recursively
presented ones.

Status of the full statement: **literature-plausible, not verified at
theorem level in this repository.**  The standard Higman construction proceeds by iterated HNN
extensions and amalgamated free products over free groups, and torsion
elements of an HNN extension are conjugate into the base while torsion
elements of an amalgam are conjugate into a factor; so torsion-freeness is
formally preserved by every step, provided the auxiliary groups are chosen
torsion-free.  Verified at abstract level only: Chiodo--Hill,
*Preserving torsion orders when embedding into groups with "small" finite
presentations*, states that the Boone--Collins embedding of a **finitely
presented** group into an 8-generator 26-relator group preserves the set of
orders of torsion elements, and in particular torsion-freeness, and that
there is a universal finitely presented torsion-free group.  That is the
finitely-presented-to-finitely-presented statement, not the recursively
presented one.  Belegradek is cited in the secondary literature for the
torsion-free universal group; his theorem statement was **not** read in
this session and must not be cited until it is.

Do not treat this claim as established, and do not let a route depend on it
silently: if it is only needed to shed finite presentation, say so.
