# Boone–Higman GPU pilot, 2026-09-08

## Status and budget

The user authorized at most **$20 total** of new Civo spending and requested
a workload with a substantive use for a GPU. No GPU inference has run, no
Boone–Higman result has been proved, and no billable instance was created.

Civo rejected creation of one `g4g.40.small` A100 40 GB in `lon1` with HTTP
403 and the diagnostic:

> gpu_count_exceeded: The requested number of GPU units exceeds the maximum
> provisionable GPU counts available in the region

The diagnostic attempt is recorded in
[the sanitized API outcome](boone-higman-gpu-pilot-2026-09-08-civo.json).
Both attempted pilots reconciled the instance list and deleted their own
temporary Civo SSH-key records. A subsequent read found zero London instances.
Neither attempt created a GPU instance. New Civo spending is **$0**.
The API credential is absent from the source files and artifacts.

The London A100 shape advertises 8 vCPUs, 57,344 MB RAM and 200 GB disk,
within the account's observed ordinary compute limits. GPU provisioning is
separately blocked. New York's smallest advertised GPU shape requires
98,304 MB RAM, exceeding the current 64,512 MB RAM quota.

Sources checked: [Civo pricing](https://www.civo.com/pricing),
[GPU setup](https://www.civo.com/docs/compute/gpu-instances),
[API](https://www.civo.com/api/instances), and
[billing](https://www.civo.com/docs/account/billing).
The A100 40 GB on-demand rate is $1.09/hour before applicable tax. Billing
rounds up; stopped instances remain billable, so the controller deletes them.

## What the GPU would do

The bounded experiment uses dense BF16 inference of
[DeepSeek-Prover-V2-7B](https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B),
pinned to revision `a8d9e14432b2e8dd9df2a4d4e70f1ba9bc8d9b7b`.
Eight candidate proofs are generated together; six batches produce at most
48 proposals with a 2,048-token limit per proposal. This is a practical GPU
workload because of the neural model's matrix operations. It does **not**
establish that this model will help with the conjecture. No GPU throughput or
GPU-versus-CPU speedup has yet been measured.

The first experiment is calibration on a construction filter, not a claim
that an elementary group lemma intrinsically requires GPU computation:

1. A known true double-coset separation lemma for commuting subgroups with
   trivial intersection.
2. Its expected-true extension replacing centralization by normalization.
3. A known false version dropping both hypotheses. In `S3`, the standard
   `C2` and `C3` subgroups have trivial intersection, but conjugation by the
   involution interchanges the two nonidentity `C3` elements. Their double
   cosets coincide.

Each positive statement is fixed before generation. Candidate text may
provide only a tactic body. The checker rejects admissions and declarations,
invokes Lean independently, and inspects the resulting theorem's axioms.
The finite false-control witness is checked exactly on the CPU.
Failure to prove a false claim is not itself a mathematical refutation; the
explicit `S3` witness supplies that refutation.

These filters relate to the repository's
[direct-corner obstruction](boone-higman-direct-ck-double-coset-no-go-2026-08-31.md).
They do not remove the finite-normal-generation obstruction documented in
[the prior audit](boone-higman-2026-08-30-literature-and-level-audit.md).
Passing calibration would justify considering a more difficult, precisely
stated construction lemma; it would not justify extrapolating to the full
conjecture or automatically spending the remaining budget.

## Implementation and operational limits

- `experiments/bh_gpu_pilot.py`: GPU-only proposal generation and timing.
- `experiments/bh_civo_pilot.py`: one London A100, a 43-minute controller
  limit, independent deletion watchdog at 45 minutes, no replacement GPU,
  no resizing, and reconciliation by this run's unique hostname.
- `experiments/bh_gpu_verify.py`: fixed-statement Lean checking, at most two
  single-thread checks, 2 GB per check and 20 seconds per attempt. It reads
  the existing compiled libraries and does not build the project.

Run orchestration and verification on MSI with **Python 3.11**. Store runs
under `/projects/standard`, outside the source checkout. The API key is
supplied on stdin to the controller and retained only in process memory.
Never put it in the command's arguments, repository, or a run manifest.
When sending stdin through the MSI wrapper, pin the compute node; its
automatic node-selection probe can otherwise consume stdin.

The provider rejection and cleanup paths have been exercised. GPU setup,
inference, transfer of model proposals, and deletion of a successfully
provisioned instance have **not** been exercised. These remain operational
limitations, not completed validation.

The verifier preflight uses explicitly labeled assistant-authored inputs,
not invented GPU results. Its initial full-library and narrower-library
checks hit the 20-second deadline. Admissions were rejected by the source
filter, and the exact `S3` witness passed. Successful positive Lean replay
must be established before treating the prover pipeline as ready.

MSI's SSH master subsequently expired. The wrapper's automatic password/TOTP
authentication failed, including its own retry, and it enabled its breaker.
No further authentication attempts were made. The final import-only timing
diagnostic therefore did not execute. The wrapper connection must also be
restored before further remote verification.

## Required next step

The [subsequent provisioning diagnosis and prepared quota request](boone-higman-civo-unblock-2026-09-08.md)
confirm that the key authenticates, neither accessible GPU region currently
offers a verified provisioning path within the account limits, and no
additional creation attempts or spending occurred. The precise account-GPU
restriction versus regional-capacity cause requires Civo confirmation.

Enable a quota permitting **one A100 40 GB in Civo London (`lon1`)**. No
support message or quota request was sent on the user's behalf. Preserve
the $20 session cap. Before retrying provisioning, finish the short Lean
preflight and recheck the current price and account availability.

## Integration with the continuing Cairn goal

This artifact is attached to `boone-higman-conjecture`, now explicitly
marked `goal: true`. The dedicated `Boone-Higman research checks` workflow
checks the three scripts' syntax, verifies the exact finite negative
control, and exports Cairn's current goal and quotient-obstruction state.
It does not run neural inference or claim a successful Lean preflight.

Subsequent algebraic work established the stronger
[quotient-and-cover obstruction](ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md)
without GPU computation. The proposed neural experiment remains calibration
of a tool; it must not be reported as the source of that theorem or as
evidence that additional GPU spending will solve Boone–Higman.
