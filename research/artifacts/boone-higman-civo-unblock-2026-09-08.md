# Civo GPU provisioning diagnosis, 2026-09-08

## Verified account state

The supplied credential successfully authenticated read-only requests to the
Civo API. No credential is included in this record. The regions endpoint
reports GPU support in `lon1` and `nyc1`; the other two accessible regions,
`fra1` and `mum1`, report no GPU support.

Both GPU regions report limits of 16 CPU cores, 64,512 MB RAM, and 400 GB
disk, with zero instance usage. Both instance lists are empty. No new create
request was made during this diagnosis, and this task's Civo spending remains
$0.

London advertises the selectable `g4g.40.small` instance: one A100 40 GB,
8 CPU cores, 57,344 MB RAM, and 200 GB disk. It fits the ordinary quota.
However, the preceding two create attempts returned HTTP 403
`gpu_count_exceeded`. The quota response exposes no GPU limit or usage
field. A selectable size therefore does not establish permission or capacity
to provision that GPU. Whether the provider rejection reflects an account
GPU restriction or regional provisionable capacity needs Civo confirmation.

New York's smallest selectable GPU instance is `an.g1.l40s.x1`: one L40S,
12 CPU cores, 98,304 MB RAM, and 200 GB disk. It exceeds this account's RAM
quota. Switching regions does not currently provide a verified solution.

## Available remedy

[Civo's quota instructions](https://www.civo.com/docs/account/quota) direct
customers to the [account quota panel](https://dashboard.civo.com/quota)
and its **Request quota increase** button. The
[public API documentation](https://www.civo.com/api/quota) documents reading
quota, and the [official Go SDK](https://github.com/civo/civogo/blob/master/quota.go)
provides `GetQuota`, without a quota-increase method.

No authenticated dashboard automation is available in this session. No
support message or quota request has been submitted. The following request
is prepared for the dashboard; it must not be described as already sent.

## Prepared request

Subject: Enable one A100 40 GB instance in London

Please enable provisioning of exactly one `g4g.40.small` GPU instance in
`lon1`, or confirm if regional capacity is preventing provisioning.
Creation currently returns HTTP 403 `gpu_count_exceeded`: "The requested
number of GPU units exceeds the maximum provisionable GPU counts available
in the region."

The instance requires 8 vCPUs, 57,344 MB RAM, and 200 GB disk, within our
current limits of 16 vCPUs, 64,512 MB RAM, and 400 GB disk. There are no
existing instances. The size is advertised as selectable, but the quota API
does not expose the GPU allowance.

This is a brief academic mathematical proof-search experiment using a
7-billion-parameter model. We plan one instance, with deletion after at most
45 minutes. Our total authorized spending for this experiment is $20; please
do not provision resources or add a paid commitment on our behalf. We need
only the permission/capacity to start this single on-demand instance.

## Validation of the research tooling

The [remote research check](https://github.com/SauersML/group-approximation/actions/runs/34277484216)
passed source syntax, the exact finite negative-control witness, and Cairn
graph validation for commit `db368800ac1bc5994913a7d7c6ed61689013e925`.
These checks did not run CUDA or establish a successful Lean positive
control. A [subsequent cached CPU preflight](boone-higman-lean-preflight-2026-09-08.md)
accepted both authored positive controls and rejected all four negative
inputs. Provisioning and neural inference still have not run; the full
neural prover pipeline cannot yet be reported as working.
