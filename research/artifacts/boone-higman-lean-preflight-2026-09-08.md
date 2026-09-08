# Boone–Higman checker calibration, September 8, 2026

The first successful positive replay of the proposed GPU pipeline's fixed
Lean statements used assistant-authored proofs on a GitHub Actions CPU.
No GPU ran. New Civo spending remains $0; the provider's provisioning
restriction is unresolved. Boone–Higman remains open.

## Evidence

[Run 34282924692](https://github.com/SauersML/group-approximation/actions/runs/34282924692)
checked commit `2eb1b4670cdf49735546c3402d2d1d8e2de3db5b` successfully.
Its `boone-higman-lean-preflight` artifact contains the exact authored
inputs, generated Lean sources, compiler logs, results and finite witness.
The [retained results](boone-higman-lean-preflight-2026-09-08.json) report:

| Control | Result | Seconds |
| --- | --- | ---: |
| Commuting subgroups, trivial intersection | Accepted | 1.197 |
| Normalizing subgroup, trivial intersection | Accepted | 1.159 |
| False S3 statement with malformed tactic | Rejected by Lean | 1.078 |
| Explicit `sorry` | Rejected by source filter | <0.001 |
| True statement with malformed tactic | Rejected by Lean | 1.093 |
| Added axiom | Rejected by source filter | <0.001 |

Both accepted proofs depend only on `propext` and `Quot.sound`.
The malformed tactics return exit code 1 and expose `sorryAx` in Lean's
error-recovery theorem; the checker rejects them. The independently checked
S3 witness, rather than a failed proof search, establishes falsity of the
third statement.

The job restored exact existing Lean 4.32.0 and dependency cache keys.
There was no dependency build, local computation, Lake invocation or
neural inference. Restore-only caches fail on a miss. The job took about
one minute, including cache transfer; actual control replay took about
three seconds with at most two single-thread Lean processes, 2 GB each
and a 20-second deadline per invocation. The workflow has a five-minute
job limit and runs this calibration only when explicitly dispatched with
`lean_preflight=true`.

## Mathematical integration

`normalizing-subgroups-separate-double-cosets` records the normalization
version and its elementary proof. It is now a prerequisite used by
`ck-quotient-corner-bi-index-proof`. This formalizes the separation step;
it does not formally verify the surrounding matrix, ring-level or covering
kernel arguments, which remain prose proofs in Cairn.

The implication proved by Lean is: if H intersect K is trivial, K
normalizes H, x,y belong to K and y=a*x*b for a,b in H, then x=y.
The connection to injectivity into the double-coset set is the usual
definition of equality of double cosets. No claim of mathematical novelty
is made for this elementary lemma.

## Remaining limits

This resolves positive calibration on the cached GitHub runner. It does
not diagnose or repair MSI authentication or the earlier MSI timeouts.
Nor does it validate GPU provisioning, inference, transfer or successful
instance deletion. Those paths have not run. No maximal normal subgroup
has been shown finitely normally generated, and no finitely presented
simple envelope has been constructed for the general input.
