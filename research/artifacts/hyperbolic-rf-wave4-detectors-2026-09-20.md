# Wave four: full mod-five homology of the specified square kernel

Date:2026-09-20. Hyperbolic residual finiteness remains open.

The exact kernel `M=ker(Λ→PSL_2(19)²)` from wave two has
`H_1(M;F_5)=0`. All three nonzero central twist directions were
already shown to survive `M` in wave three. Together these exclude
all finite five-group refinements over this specified quotient,
including refinements of the twisted group that might detect its
central generator. They do not imply integral perfectness or exclude
mixed-prime solvable kernels.

The full written proof is
[[wave4-detector-psl19-square-kernel-mod-five-proof]]. The full mathematical
argument and scripts received independent review PASS. The reviewer
replayed all32 intertwining identities, the285-dimensional direct-sum
certificate, all64 tensor sectors, and the generator-rank sequence
ending at3420. The bounded preliminary Borel-times-A4 computation
also received independent source review and full replay PASS.

## From one invariant sector to the whole module

First, the degree5700 cover from `B×A4≤PSL_2(19)²` has nine vertices,
3420edges,5700faces. Its first mod-five homology is zero; its second
has dimension2288. Exact elimination uses2912 sparse pivots and a
remaining500-by2788 matrix of rank500. This proves only that the
`B×A4` invariant sector of `H¹(M;F_5)` vanishes. The independently
reviewed bounded statement is
[[wave4-detector-psl19-borel-a4-sector-vanishes]].

The stronger computation uses the285-dimensional projective
permutation module `P=F_5[Q/A4]`, where `Q=PSL_2(19)`. GAP proposes
eight invariant summands with dimensions
`60,45,20,20,20,20,45,55`. Their explicit bases and generator matrices
are stored. Python independently checks the full285-by285 basis
rank and all32 exact intertwining identities; indecomposability
is neither needed nor trusted for the conclusion.

For each of the64 tensor pairs, fixed subspaces of the three edge
actions give the cohomology dimension through four finite-field
span ranks. All64 dimensions are zero. The largest tensor has
only3600 coordinates, avoiding the full cover's11,696,400 faces.
The total tensor calculation completed in46.7seconds locally.

A separate exact closure calculation proves that the A4 averaging
idempotent generates the whole3420-dimensional group algebra as a
two-sided ideal. The intermediate ranks are
`285,853,1969,3012,3420`. Thus `P` is a projective generator, and
`P⊗P` detects the entire square-kernel cohomology module. The regular
`F_5[Q²]` module is a direct summand of copies of `P⊗P`; Shapiro then
proves full first mod-five homology vanishing for `M`.

## Reproducibility and environment

All scripts/data are under
`experiments/hrf-wave4-detectors-2026-09-20/`.

- `borel_a4_homology.py`: exact preliminary cover construction/rank.
- `projective_summands.json`: explicit summand bases/generator matrices.
- `tensor_homology.py`: independent certificate validation and64 ranks.
- `tensor_homology_result.json`: complete per-pair rank output.
- `a4_generator.py`: independent two-sided ideal closure calculation.
- `a4_generator_result.json`: complete closure-rank sequence.
- `projective_decomposition.py`, `decompose.g`: regenerate the GAP input
  and proposed decomposition; not required to verify stored summands.

Recompute the substantive result with:

```
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave4-detectors-2026-09-20/tensor_homology.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave4-detectors-2026-09-20/a4_generator.py
```

Python3.13.13, python-flint0.9.0, NumPy2.5.3 were used. All ranks and
identities are exact mod5. NumPy uses int64 only for intermediate
integer operations whose maximum size is explicitly bounded below
overflow: the largest fourth-power entry is at most60³·4⁴, and each
tensor orbit sum is at most5·4² before reduction.

GAP core was built locally under `/tmp/gap-4.15.1` from the official
v4.15.1 GitHub source archive; `GAPInfo.Version` reports4.15dev for
this source build. It runs with `--bare`, using built-in MeatAxe.
Homebrew's full GAP installation attempt was blocked by old Command
Line Tools. That attempt auto-updated Homebrew and tapped GAP;
subsequently only autoconf2.73 was installed to compile the local core.
No compiler toolchain was replaced. NumPy was added only to the
existing temporary Python environment.

## Remaining obstruction

`H_1(M;F_5)=0` rules out finite five-group images of `M`. It does not
rule out a solvable image whose initial abelian quotient has order
prime to five and whose deeper normal factors involve five, nor an
additional nonsolvable quotient. A proof of integral perfectness or
control after all relevant prime-to-five detours would be stronger
and has not been obtained here. No finite central detector and no
counterexample to hyperbolic residual finiteness is asserted.
