# One bounded dimension-24 packet pilot

2026-09-08. Exploratory computation on MSI acn112. This is neither
a feasibility certificate nor a lower-bound proof.

The pilot evaluates the four explicitly authenticated kernel words
in `leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md` using
the frozen `C_3` and `C_2^3` regular factors at `k=1`. Its only
variable is a relative unitary `U in U(24)`. The implementation is
`experiments/leavitt_24k_packet_pilot.py`; the complete numerical
record is `research/artifacts/leavitt-24k-packet-pilot-2026-09-08.json`.

Execution used the existing warm interpreter
`/projects/standard/hsiehph/sauer354/params-venv/bin/python`, with
PyTorch `2.13.0+cpu`, complex128 matrices, and one intra-op and
one inter-op thread. The system Python lacked PyTorch; no packages
were installed and no build was performed. The single run used a
deterministic Haar start with seed `20260908`, 200 iterations,
QR retractions, and at most eight Armijo trials per iteration.
A 15-second optimization timer and a 30-second outer process
timeout bounded the run. No additional starts or sweeps were run.

The maximum row residual decreased from `1.430195998137113` to
`1.0013819310220697`. The best evaluated unitary occurred at
iteration 199, with normalized-HS residuals:

| Word | Residual |
|---|---:|
| `r_*` | 0.9356692943976771 |
| `R_v` | 1.0013819310220697 |
| `R_0` | 0.9485822988984242 |
| `R_sum` | 0.9618145595390948 |

All 200 iterations were accepted, with 468 objective evaluations
including the initial value. The optimization took about 1.03
seconds; setup took 8.34 seconds and elapsed time through checkpoint
writing was 9.43 seconds, excluding imports. It stopped at its
iteration cap. It did not stop on a convergence or stationarity
criterion: the final recorded tangent-gradient Frobenius norm was
about `0.0849`.

The frozen-factor identities and traces were exact in the recorded
arithmetic. The largest final relative-unitary defect was below
`6e-16`; the largest final packet-word unitarity defect was below
`1.2e-14`. The commuting-involution and regular-trace checks also
passed their `1e-9` tolerance. Re-evaluation of the saved best
unitary reproduced the four residuals with zero recorded difference.
These are numerical consistency checks, not symbolic certificates.

Initial and best unitaries, together with the frozen factors, were
saved on shared storage at
`/projects/standard/hsiehph/sauer354/cairn-goal-20260908/leavitt-packet-pilot.pt`.
Its SHA256 is
`5441299c1bc5aaed211b610eac79207a9d64bb97bb80685b13b3877ea1b9b7b0`.
The JSON also records the exact script hash, every accepted iterate's
scalar diagnostics, the timer scope, and the checkpoint hash.

This run found no near-zero solution. A positive residual at one
finite iterate does not bound the optimum at dimension 24, much
less uniformly over every `24k`. The finite-coefficient rank theorem
is logically independent of this unrestricted complex-unitary
pilot. Both global feasibility alternatives remain open.

An exact construction now resolves the optimum for these four rows:
`leavitt-four-word-packet-24-point-countermodel-2026-09-08.md`
gives the relative permutation
`U=(9 17)(10 18)(12 20)(15 23)` in zero-based coordinates.
All four residuals are exactly zero at dimension 24. Thus the
positive residual above reflects this bounded optimization run,
not an obstruction of the packet. The exact control was verified
separately by integer permutation calculations and literal-word
replay; the original numerical history is retained unchanged.
