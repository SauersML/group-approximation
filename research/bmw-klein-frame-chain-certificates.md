---
rg: 2
id: bmw-klein-frame-chain-certificates
kind: claim
title: Conjugate-frame Klein chains certify three more transposed-letter parity kernels, and every Klein pair of 31_30 #26 and 31_31 #12 is conjugate only to long pure pairs
distinct_from:
  bmw-census-klein-power-chain-certificates: that certifies 171 classes with chains of pure words of length at most 6 (8 for #470) and proves Theorem 4; this searches Γ-conjugates of pure pairs, adds 41_30 #80, #113 and 52_30 #158, and bounds the Klein pairs of #26 and #12 from below
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that refutes left orders on these parity kernels by positive-cone SAT; this gives solver-free certificates for three of them and a length bound for two others
  bmw-degree-44-53-parity-kernels-not-left-orderable: that is the SAT census of degrees (4,4) to (5,3); this gives a solver-free certificate for 52_30 #158
artifacts:
  - experiments/bmw-klein-frames-2026-09-18/README.md
  - experiments/bmw-klein-frames-2026-09-18/kframe.py
  - experiments/bmw-klein-frames-2026-09-18/run_frames.sh
  - experiments/bmw-klein-frames-2026-09-18/kbottle.py
  - experiments/bmw-klein-frames-2026-09-18/kbottleB.py
  - experiments/bmw-klein-frames-2026-09-18/chains_41_30.json
  - experiments/bmw-klein-frames-2026-09-18/chains_52_30.json
  - experiments/bmw-klein-frames-2026-09-18/verify_41_30.log
  - experiments/bmw-klein-frames-2026-09-18/verify_52_30.log
  - experiments/bmw-klein-frames-2026-09-18/kbottle_31_30_26.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottle_31_31_12.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottleB_31_30_26.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottleB_31_31_12.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_41_30.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_41_31.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_42_30.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_42_31.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_42_42.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_52_30.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kf_p1_52_31.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_klein2.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/crosscheck2.py
---

**ESTABLISHED (computer-certified).**
- Part (a) consists of explicit group identities. `verify_klein2.py` checks each one by rewriting with
  the census squares and logs the full trace. `crosscheck2.py` re-checks each one with an independent
  normal-form algorithm.
- Part (b) is a complete finite search combined with Theorem 4 of
  `bmw-census-klein-power-chain-certificates-proof`.
- No SAT solver is used.

Proof: `bmw-klein-frame-chain-certificates-proof`.

**Setting.** The setting is that of `bmw-census-klein-power-chain-certificates`.
- A class `c` of `census_X.json` in `experiments/bmw-census-left-orders-2026-09-17/` gives a BMW group
  `Γ_c` with horizontal letters `h` and vertical letters `v`, and some letter pairs may be transposed.
- `Γ_c^+` is its parity kernel, of index 4.
- A *Klein pair* is `(a, b)` in `Γ_c^+` with `b ≠ 1` and `a b a^{-1} = b^{-1}`.
- A *pure pair* is a Klein pair in which one of `a, b` is a pure `h`-word and the other is a pure
  `v`-word.

**Claim.**
- **(a) Certificates.** For `41_30` #80, `41_30` #113 and `52_30` #158, `Γ_c^+` contains elements
  `x_0, …, x_{k-1}` forming a cycle of (K) and (R) steps with at least one (K) step, as in
  `bmw-census-klein-power-chain-certificates`. So `Γ_c^+` is not left-orderable.
  - #80 and #113 share the same 8-element chain, with 4 (K) steps:
    `v010210, v01020210, v02·h0320, h132320, v020120·h00, v02010120, v01·h32, h2323`.
    The mixed elements `v02·h0320` and `v020120·h00` are not pure words, so the pure scans of
    `bmw-census-klein-power-chain-certificates` cannot find this chain.
  - #158 has a 10-element chain with 4 (K) steps and 6 power steps, through `v`-words up to length 16:
    `r, r², r⁴, r⁶, h24, t, t², t⁴, t⁶, h22` with `r = v2012` and `t = v120121` (here `r^k = v2(01)^k2` and
    `t^k = v12(01)^k21`).
- **(b) Obstruction for `31_30` #26 and `31_31` #12.** For both classes, every pure pair `(A, B)` with
  `A B A^{-1} = B^{-1}` has `|A| ≥ 18` and `|B| ≥ 16`, in both orientations (`A` an `h`-word and `B` a
  `v`-word, or the reverse). By Theorem 4, every Klein pair of `Γ_c^+` is `Γ`-conjugate to such a pair.
  - So any Klein-chain certificate for these two classes needs a (K) step whose pure frame has an
    inverter of length at least 18 and an inverted word of length at least 16.
  - The two parity kernels are already known not to be left-orderable, by positive-cone SAT at
    radius 4.
  - Neither class is proved left-orderable here. Neither is proved to need certificates other than
    Klein chains.

**Scope of the search.**
- The frame search `kframe.py` ran with pure inverters of length at most 6, seeds of length at most 6
  and nodes of normal-form length at most 16. It covered the transposed-letter candidates without a
  chain in the first patterns of `run_frames.sh`. The per-class logs are the `kf_p1_X.jsonl` files of
  the experiment.
- Most searched classes exhaust their frame graph without finding a cycle. Many have no pure inverting
  pair with inverter length at most 6 at all.
- There are 512 transposed-letter candidates without a chain. The other 509 remain open for
  solver-free certificates.

## Attempts

- A conjugate search over whole balls of conjugators ran out of memory at radius 4. The frame search
  replaces the balls: its conjugators are products of prefixes of pure words, which fix a vertex of one
  tree.
- Sign and ribbon invariants were tried as proofs that #26 and #12 have no Klein pairs at all. They
  failed, and so did the level groups of the `h`-action on `T_v`, whose orders grow without a visible
  invariant.
