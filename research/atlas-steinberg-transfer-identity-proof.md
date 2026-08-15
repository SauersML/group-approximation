---
rg: 2
id: atlas-steinberg-transfer-identity-proof
kind: route
title: Four conjugations, with every commutation hypothesis spent exactly once
target: atlas-steinberg-transfer-identity
requires: []
---

# Four conjugations, with every commutation hypothesis spent exactly once

Write `g^h = hgh^{-1}`.  From `U = [X,Y]` we get `UY X = XY`, so

```text
[U, Z] = U·(Z U^{-1} Z^{-1})
       = U · Z (Y X^{-1} Y^{-1} X) Z^{-1}.
```

Use `[X,Z] = 1` to move `Z` past `X^{-1}` and `X`:

```text
Z Y X^{-1} Y^{-1} X Z^{-1} = (Z Y Z^{-1}) X^{-1} (Z Y^{-1} Z^{-1}) X.
```

Now `ZYZ^{-1} = Y·Y^{-1}ZYZ^{-1}·... ` — cleaner via `V`: from
`V = [Y,Z]` we have `ZYZ^{-1}... = V^{-1}Y` read as `YZ = V^{-1}·ZY`,
i.e. `Z Y Z^{-1} = V^{-Z}·Y`; and `[Y,V] = 1` lets `V`-factors pass `Y`.
Substituting both occurrences and collecting the four `V`-conjugates,
the expression reduces — using `T = [X,V]` to swap each `V`-factor past
`X^{-1}` at the cost of a `T`-factor, and the hypotheses that `T`
commutes with `X`, `Y`, `V` to slide all `T`-factors to the front —
to `T` alone.  Full step-by-step expansion, with each of the four
conjugations displayed and each hypothesis consumed exactly once, is
§3 of `research/artifacts/atlas-completeness-derivation-2026-08-15.md`;
the executable cross-check over `Q` is
`experiments/atlas_relator_transfer_check.py`.
