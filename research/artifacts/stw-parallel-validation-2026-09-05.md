# Validation of the September 5 STW contributions

The reviewed dependency closure passed `cairn check --changed` and
`cairn preview` on MSI using the repository's Python CLI with Python 3.11.
The closure contains 41 claims and 36 routes, including the original
proof routes for all prerequisites. No prerequisites were replaced by
unproved leaf assertions to obtain a passing check.

The new claims checked are the rational AF-extension index criterion,
the two Berend quotient-obstruction claims, the finite twisted-unitary
test, finite-graph and one-dimensional Cu regularity, and the scalar
unstable-homotopy vanishing theorem. Full-snapshot duplicate checks found
no unresolved duplicate findings for these seven claims. The scalar
vanishing theorem refutes the former scalar S6 witness and invalidates
its proposed route, as intended.

The full imported repository snapshot still has **37 source errors** in
other lanes. Thus this is a clean check of the stated dependency closure,
not a passing repository-wide check. Cairn validates graph structure,
dependencies and duplicate declarations; its derived `ESTABLISHED`
status is not an independent verification of mathematical proofs.

The MSI check directory is
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/reviewed-scope-20260905`.
Its `check.log` and `preview.log` record the successful commands; the
parent directory's `reviewed-global-audit-20260905.json` records the
full-snapshot errors, six initial duplicate checks and derived statuses.
The scalar vanishing claim received an additional full-snapshot duplicate
check, also returning an empty list.

The subsequent candidate simple K1-injectivity counterexample is outside
this validation record and requires its own proof review and graph check.
