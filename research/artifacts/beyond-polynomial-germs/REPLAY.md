# Beyond-polynomial arithmetic replay

The supplied script is `check_beyond_polynomial_germs.py`, and the separately
preserved supplied output is `supplied-check-results.json`. The fresh
`check_results.json` was produced on MSI and downloaded to this directory.

The fresh run passed all **5,678 checks**. All 20 category counts, the status,
arithmetic description, scope warning, and script hash match the supplied
results. A direct file comparison shows that **only `note_sha256` differs**.
This is expected: the checked note is the edited repository integration index,
not the unavailable original manuscript. It is not a reproduction of the
original note's bytes.

| File | Supplied original SHA-256 | Fresh SHA-256 |
| --- | --- | --- |
| Script | `8f3e5ec302758e1a85a5db3dc4c5dd0a8b473da85c24ecd615295a672c6f04c7` | `8f3e5ec302758e1a85a5db3dc4c5dd0a8b473da85c24ecd615295a672c6f04c7` |
| Note | `7111186a218d0be00cc163e794ef9d67b315aeef6d3fb3e893c02188b2c42687` | `c952abde0fb150b5c1014582df9121b1d29b7fdb5de8210622e5c79533304325` |

The fresh script hash was obtained both independently with `sha256sum` on MSI
and by the script's own `hashlib.sha256` calculation. It does match the
user-supplied original script hash. The fresh note hash identifies the exact
bytes of `beyond_polynomial_germs.md` at replay time; it does not hash the linked
proof artifacts or certify their content.

## Environment and command

- Host: MSI `acn112`.
- Start: `2026-09-20T18:17:51Z` (UTC).
- Interpreter: `/usr/bin/python3.12`, Python `3.12.13`; standard library only.
- Working directory:
  `/projects/standard/hsiehph/sauer354/bh-finalize-20260920/beyond-polynomial-germs`.
- Limits: one CPU (affinity 63), nice level 10, 60-second wall timeout,
  1 GiB virtual-memory cap.
- Result: exit 0; status `passed`; 0.87 seconds elapsed;
  maximum RSS 17,180 KiB; empty stderr.

Executed remotely through `/Users/user/msi-node/msi -n acn112`:

```sh
cd /projects/standard/hsiehph/sauer354/bh-finalize-20260920/beyond-polynomial-germs
ulimit -v 1048576
/usr/bin/time -f 'elapsed_seconds=%e max_rss_kib=%M exit_status=%x' \
  -o timing.txt timeout 60s nice -n 10 taskset -c 63 \
  /usr/bin/python3.12 check_beyond_polynomial_germs.py \
  > check.stdout 2> check.stderr
```

The script writes `check_results.json` itself. The remote directory retains
the source, checked integration index, generated JSON, `environment.txt`,
`timing.txt`, `check.stdout`, and `check.stderr`. No code ran locally; no
dependency installation or build was needed. The process completed and left
no running job.

## Scope

The script checks finitely many exact integer, rational-matrix, and finite
permutation calculations. Its noncommutative observation example is `S_3`
with an inner automorphism; this does not test separation for an infinite
group. The shell tests check finite words against the displayed prefix table.
The recurrence and matrix checks cover the bounded inputs in the source.

These results do not prove the compact-core stabilizer theorem, finite germ
extension axioms, all finite-forest restriction assertions, type `F_k` or
`F_infinity`, finite presentation, simplicity, nonlinearity, or any
infinite-group embedding. In particular, neither a matching source hash nor
passing arithmetic checks discharge the manuscript's OPEN mathematical gates.
