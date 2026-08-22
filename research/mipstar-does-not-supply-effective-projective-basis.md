---
rg: 2
id: mipstar-does-not-supply-effective-projective-basis
kind: claim
title: The known MIP-star and BCS sources do not supply an effective projective regular trace
distinct_from:
  cdi-input-projective-word-law-remains-a-group-factor-gate: that claim concerns whether the CDI input factor admits some abstract projective basis; this claim audits the effective game-algebra source and the native BCS/RACG generators required by the recursive twisted-factor compiler.
  twisted-group-basis-forces-affine-context-support: that theorem proves the affine-support restriction for native basis observables; the present claim applies it to the fixed non-CE BCS source and records the remaining unrelated-basis/effectivity gap.
---

Neither currently cited `MIP*=RE` output closes
`effective-nonce-twisted-factor-exists`.

1. JNVWY Theorem 12.13 constructs an explicit finite game with commuting
   value one and entangled value at most one half, but gives no group,
   multiplier, projective unitary basis, or recursively enumerable scalar
   word kernel.  Its proof of commuting value one is indirect through the NPA
   hierarchy.
2. Paddock--Slofstra Example 4.2 supplies a finite tracial non-`R^U` BCS
   algebra.  Pullback to the explicit RACG gives a non-CE **character**, not
   its canonical trace; the RACG itself is residually finite and sofic.
3. No occupied affine slice of every context is produced.  If the native
   commuting involutions were elements of a projective group basis, the
   theorem `twisted-group-basis-forces-affine-context-support` would produce
   exactly such slices and reduce the source to an LCS instance.
   Paddock--Slofstra Proposition 5.8 identifies a tracial/non-`R^U`
   separation in that linear language with the nonhyperlinear-group problem;
   thus proving this native-basis assertion would itself close the problem,
   rather than read off data already present in the BCS construction.

This does not prove that the BCS GNS factor has no unrelated projective basis.
It proves the precise source audit needed here: no such basis, no finite
projective presentation, and no r.e. scalar kernel is constructed by the
known MIP/BCS reductions.  Establishing any of those would be new
groupification content, not extraction of an already present solution group.
