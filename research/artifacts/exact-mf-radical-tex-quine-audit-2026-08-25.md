# Exact MF-radical TeX quine audit

Date: 2026-08-25

The audit has three independent layers:

1. `scripts/check_mf_radical_tex_quine.py` regenerates the fixed point,
   executes the program extracted from the physical TeX listing in isolated
   Python mode, and compares both byte streams with `mf_radical_tex_quine.tex`.
2. The same checker parses the natural-number list in
   `MFRadicalQuineSource.lean` and compares it cell-for-cell with the TeX.
3. The MSI Lean build checks the output-sensitive radical theorem and the
   concrete computable-source instantiation with the kernel.  A TeX Live 2025
   pass checks that the exact source also typesets as a manuscript.

All computation and builds were run on MSI `acn112` from the warm checkout in
`/projects/standard`; no local build was used.  The final exact-source check
reported

```text
23213 bytes
sha256 = bb0333c08ab2b224f6e24bfc8ec1f19eb94d430b69a0a5ca2e4b948c921d0880
embedded program output, canonical generator, and Lean ledger all match
```

TeX Live 2025 produced a seven-page PDF with no warning, overfull-box, or
underfull-box diagnostic.  The focused MSI kernel build of
`GroupApproximation.Computability.MFRadicalQuineSource` completed successfully;
the root import also includes both quine modules.
