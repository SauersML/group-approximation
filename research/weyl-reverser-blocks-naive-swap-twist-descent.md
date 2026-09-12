---
rg: 2
id: weyl-reverser-blocks-naive-swap-twist-descent
kind: claim
title: An explicit Weyl involution in the S-arithmetic group inverts the swap twist word, refuting the naive enemy descent
distinct_from:
  swap-twist-centralizer-is-the-congruence-core: that computes the CENTRALIZER of the twist word, which is the congruence core exactly; this computes the NORMALIZER of the cyclic group it generates, which is strictly larger by one involutive coset, and draws the moment-pattern consequence that kills the naive descent.
  odd-congruence-lambda-exact-sector-collapses: that uses the Weyl relation w_13 h w_13^(-1) = h^(-1) to force the corrector to 1 and close the coprime sector; this uses the SAME relation on the enemy side, showing it simultaneously blocks the regeneration of enemies over the deeper congruence core -- one rigidity, two jobs, on both sides of the ledger.
  hnn-stable-letter-rounds-to-finite-order: that transfers Haar enemies to finite-order enemies over the same pair, and recorded the descent to a deeper pair as an unverified direction; this settles that direction NEGATIVELY in its naive form, and corrects the record: the sample cancellations checked there missed the Weyl-conjugated four-letter word.
---

Work in `E = Gamma *_Lambda (Lambda x <s>)`, `Lambda = SL_3(Z) <=
Gamma = SL_3(Z[1/p])`, `h = diag(p, 1, 1/p)`, `z = s (h s h^(-1))`,
`C_0 = Lambda cap h Lambda h^(-1)`, and let `w_13 in Lambda` be the
signed permutation `[[0,0,1],[0,-1,0],[1,0,0]]`, so
`w_13 h w_13^(-1) = h^(-1)` and `w_13^2 = 1`.

**THEOREM (established here; proof in
`weyl-reverser-computation-proof`).**  Put `x_0 = h w_13 in Gamma`.
Then:

```text
x_0^2 = e,   x_0 notin Lambda  (a fortiori  x_0 notin C_0),
x_0 s x_0 = h s h^(-1),   x_0 (h s h^(-1)) x_0 = s,
x_0 z x_0 = z^(-1),   x_0 C_0 x_0 = C_0,
N_Gamma(<z>) = C_0 cup x_0 C_0,   C_Gamma(z) = C_0.        (WR1)
```

**Consequence: the naive descent is refuted everywhere.**  In every
tracial model of `E` whatsoever, the four-letter word evaluates to

```text
tau(pi(x_0) z pi(x_0)^(-1) z) = tau(z^(-1) z) = 1,
```

while amalgamated freeness of `(W*(pi(Gamma)), W*(L(C_0), z))` over
`L(C_0)` would force this moment to vanish (`x_0 in Gamma - C_0` is
`E_(L(C_0))`-centered, `z` is centered).  So the statement "the swap
twist word is an amalgamated-free Haar letter over the depth-one
congruence core" is FALSE -- not merely unprovable: false in every
model, by one exact group identity.  An involution enemy over
`(Lambda, Gamma)` therefore does NOT manufacture a naive HNN enemy over
`(C_0, Gamma)`; the descent direction recorded in
`hnn-stable-letter-rounds-to-finite-order` is closed in that form.

**The unification.**  The relation `w_13 h w_13^(-1) = h^(-1)` is
exactly the first Weyl-orbit relation by which
`odd-congruence-lambda-exact-sector-collapses` forces the corrector to
`1` on the exact face.  The present theorem is the enemy-side face of
the same rigidity: rank-two Weyl symmetry both closes the exact face
AND prevents enemies from regenerating one congruence floor down.  A
rank-one pair (`SL_2`) has no `w_13`, which is consistent with the
graph's finding that the `SL_2` collapse mechanisms are weaker on both
sides.

## Attempts

- **What descent survives: the dihedral form.**  `x_0` normalizes both
  `C_0` and `<z>`, with `D_0 = C_0 rtimes <x_0>` acting on `<z>` by
  inversion.  The surviving question is whether `<Gamma, z>` is the
  amalgam `Gamma *_(D_0) (D_0 ltimes <z>)` (an HNN letter WITH
  inversion) -- every canonical `E`-model does realize `z` as a Haar
  unitary commuting with `L(C_0)` and inverted by `pi(x_0)`, so the
  dihedral moment pattern is achievable; whether it is FREE in the
  dihedral sense is the corrected open direction, and any further
  obstruction would again have to be an exact identity in `E` like
  `(WR1)`.  Not pursued past the normalizer computation, which shows
  `(WR1)` lists ALL relations of normalizer type.
- **Why the earlier samples missed it.**  The cascade checks in
  `hnn-stable-letter-rounds-to-finite-order` tried letters
  `x in Lambda` and `x in h Lambda` with generic congruence parts; the
  reverser needs the letter to swap the two fixed vertices of the
  involutions, which forces the Weyl coset `h w_13 C_0` exactly -- a
  measure-zero family the generic samples never hit.  The Bass--Serre
  overlap analysis detects it cleanly: `x_0` maps the axis to itself
  reversing orientation, the one case the bounded-overlap ping-pong
  cannot exclude.
