# Vertex images of GHB(7) in GL4(F7): model tests (lane kh-cckw)

Model tests behind `Kazhdan/GHBQuotientVertexFamilies`, `Kazhdan/GHBQuotientVertexForms`,
`Kazhdan/CCKWLinkRelations` and `Kazhdan/CCKWLinkGirthTyped`, for the quotient
`psi : GHB(7) -> GL4(F7)` of CCKW Proposition 7.15 (`experiments/kms_ghb7_quotient/`). Each
script runs in seconds with plain Python 3 and prints `True` for every check.

- `ghb7_model.py`: relators; orders 343, 2401, 2401 of the three vertex images; pairwise
  intersections of the images are the edge images; no alternating relation of length 2, 4 in
  `<a,b>` or of length 2, 4, 6 in `<c,b>`, `<c,a>`; orders of `ab`, `bc`, `ac` (7) and `abc` (42).
- `ghb7_readout.py`: polynomial fits of the matrix entries of the commutator normal forms.
- `ghb7_lean_formulas.py`: the readouts of the first vertex-forms draft.
- `ghb7_families.py`: the parameter families `matAB`, `matCB`, `matCA`, their laws, generators,
  seventh powers and the words reaching every parameter, as used in `GHBQuotientVertexFamilies`.
- `ghb7_typed_girth.py`: the parameter-level statements of `CCKWLinkGirthTyped` (lengths 2 and 6,
  with the reduction of the last two parameters).
