# Atlas central-extension Schur validation

Date: 2026-08-11

## Result

The perfect central group already isolated by the local atlas certificate is

`E=PerfectGroup(IsPermGroup,2688,2)`.

Exact GAP/HAP computation gives

`|Z(E)|=2`, `|E/Z(E)|=1344`,

`E` and `E/Z(E)` both perfect, and

`H_2(E/Z(E);Z) ~= C_2 directSum C_2`.                 `(ASV1)`

The extension

`1 -> C_2 -> E -> E/Z(E) -> 1`                       `(ASV2)`

is nonsplit.  Indeed a split extension would be the direct product of the
perfect base with `C_2` and would therefore have a nontrivial abelianization,
whereas `E` is perfect.  Thus `(ASV2)` represents a nonzero Schur-multiplier
character.

This is an end-to-end validation of the computational reduction in
`notes/FALSE_SCHUR_MULTIPLIER_MARKED_REDUCTION.md`: the central atlas phase is
visible as genuine finite Schur data rather than a numerical matrix artifact.

## Scope

This is not a FALSE certificate.  The local atlas phase word is not known to
be a nontrivial element of a sofic radical.  The calculation only validates
the exact software and the central-extension-to-Schur interface on a
nontrivial group already present in the repository.

The reproducible certificate is
`experiments/atlas_schur_multiplier_validation.g`.  It asserts every group
order, both perfectness checks, and the invariant factors `[2,2]` returned by
integral degree-two homology.

## MSI software

The calculation used the maintained SageMath 10.7 module and GAP 4.14 with
HAP 1.78 installed in shared project storage.  HAP was loaded uncompiled; the
entire check completed well below the one-minute cap.

