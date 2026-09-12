# A bounded structured pilot and independent replay of the retained packet

2026-09-08. One numerical trajectory and one independent replay on MSI
acn112. These computations do not establish a dimension-uniform gap.

The [exact eight-row reduction](leavitt-eight-word-exact-reduction-2026-09-08.md)
proves equality of normal closures and
`delta_8 <= delta_9 <= 2 delta_8`. The pilot still optimizes the original
nine-row smooth maximum; their critical points need not agree. The replay
also reports the eight-row defect and squared-sum energy.

## Inputs, resource bounds, and what was measured

The script `experiments/leavitt_nine_word_structured_pilot.py` starts from
the exact parity-reflection control

```text
U(a,x)=((-1)^parity(x) a,x),        a in Z/3, x in F_2^3.
```

It changes the relative unitary by a deterministic tangent perturbation
of normalized-HS size `0.01`, with seed `20260908`. Every update uses
the tangent to the unitary group and a phase-corrected QR retraction.
The three order-two factors remain simultaneous conjugates of the same
frozen commuting triple. There is one start, no restart, and no dimension
sweep. The update uses the shared 103-multiplication word graph.

The run was capped at 200 iterations, ten optimization seconds, and
eight Armijo trials per iteration. It reached the iteration cap after
`1.700897578` optimization seconds. It used one CPU thread in the
existing warm Python/Torch environment, on shared `/projects/standard`
storage. There was no build, GPU allocation, or local code execution.

At the unperturbed control the computed feasible tangent gradient is
zero. Its compiled `A,B,D` are all `C^2`; only `rho_1,rho_3,rho_5`
fail, taking values `C,C,C^2`. This explains the use of a perturbation
before descent. The original four-word packet is exactly satisfied there.

The selected best point has the smallest observed maximum nine-row
defect among the control, perturbed start, and every evaluated trial.
A selected trial need not have been accepted by the smooth-objective
line search. This is selection of a saved tuple, not a claim of local
or global optimality.

## Observed defects and independent authentication

| Quantity | Exact control | Selected best |
|---|---:|---:|
| Maximum nine-row HS defect | `1.4142135624` | `1.1588990133` |
| Maximum original four-row HS defect | `0` | `0.9708527213` |
| Computed feasible tangent-gradient Frobenius norm | `0` | `5.0200925668` |

The selected best point occurred at iteration 199. Its largest row is
`rho_1=j^2`, equivalently `d^2`; its other eight defects are between
`0.8191` and `1.0632`. The best tuple is not stationary. The run also
leaves the exact four-word control locus, so it does not reveal a
deformation satisfying those four words while improving the new rows.

The independent script `experiments/leavitt_packet_checkpoint_replay.py`
transcribes signed words without using the DAG parser and evaluates
their 31,864 letters directly on the saved control and best point.
It compares full matrices with a fresh DAG evaluation, replays all
thirteen monitored residuals, and checks

```text
rho_4=[L,r_*],
j^2=(a c)d^2(a c)^(-1),
E_9=E_8+||rho_4-I||_2^2.
```

The replay passed in `0.449190226` seconds, excluding Torch startup,
under a ten-second internal timer and a 25-second outer timeout.
The recorded identities have written proofs; this replay additionally
checks their transcription on saved matrices. Neither floating-point
replay nor a positive observed residual certifies a lower bound.

The authoritative records are
[the pilot](leavitt-nine-word-structured-pilot-2026-09-08.json) and
[the independent replay](leavitt-packet-independent-replay-2026-09-08.json).
They retain source hashes, the checkpoint hash, all residuals, spectra,
unitarity checks, and actual timings. The checkpoint remains at
`/projects/standard/hsiehph/sauer354/cairn-goal-20260908/leavitt-nine-word-structured-pilot-2026-09-08.pt`.

## The next mathematical distinction

The [coarse receiver proof](frozen-cycle-coarse-prefix-receiver-2026-09-08.md)
now supplies an auxiliary exact `S_3` pair while preserving `C`, together
with a three-cell projection system. Its authenticated 672-dimensional
source model satisfies all retained rows except `rho_5,rho_8`; these
evaluate to `D,c`, each of defect `sqrt(2)`. Thus those two rows and
their interaction with the other six are an explicit place to seek the
missing fine projection transports. The example does not establish that
either failing row alone supplies such transports.

The fixed positive obstruction to the two desired child transports
is already proved. Deriving those transports from small full-packet
defect is still missing. The present numerical point has errors too
large to settle that inference, and it supplies no asymptotic sequence.
