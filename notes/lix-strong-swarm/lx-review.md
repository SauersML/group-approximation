# lx-review — lane report (2026-09-12)

Adversarial review of the named Props on the LIX-strong chain.  Findings in full:
`notes/lix-strong-swarm/review-chain-props-2026-09-12.md`.

## GREEN
- No Lean authored; no probes.
- `notes/lix-strong-swarm/tools/review_constants.py` on MSI: 16 odd primes, 3712 checks, 0 failures.  It checks
  ν(q) = (−1)^{m q(q−1)/2}(m!)^q against c_1, c_2, c_{2k} and κ_top.

## FINDINGS
- Round 1 (origin c3b58d90c): every named Prop on the D1 chain is true at the real objects, stage 0 included.
  - F1–F2: `P⁰ = id` and odd-class Cartan are over-asks.
  - F3: `htop` covered every W (fixed by lx-endpoint).
  - F4: `LocalClassesAgree` is true (rotation route checked).
  - F5: challenge docstring overclaim (fixed).
  - F6: stale seam note.
- Round 2 (origin c1b23d84a): the odd-p narrowing is complete as interfaces, but D1's real path is not routed through it.
  - R1: `RealTorusModP` still asks for `PN_zero` and unconditional `cartan`, and uses the strong `ModPStepDData`.
  - R2: red at tip, unwired: `LIXStepDGenTorusPModel.ofEven`, `LIXStepDGenBundleP`, `LIXStepDGenBundlePLix`.
  - R3: the bundle path still uses the strong `HasSplittingP`; `realWu_of_splittingN` does not exist.
  - R4: produce `pH_z_mul_zero` from `mul_single`, not from Cartan.

## NEEDS
- none.  Re-review after lx-torusP, lx-bundleP and lx-slice2 land the routing (resume by SendMessage).

## TRAPS
- `git grep -E` has no `\b`, so an anchored `(def|structure) Name\b` matches nothing; use `-P`.
- The first MSI call died at the ssh mux (broken pipe, port 22 timeout); `msi up`, then retry.
- A design note's "landed spellings" is a claim about main, not evidence: compare blob md5s.
