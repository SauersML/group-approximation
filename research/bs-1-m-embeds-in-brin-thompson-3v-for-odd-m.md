---
rg: 2
id: bs-1-m-embeds-in-brin-thompson-3v-for-odd-m
kind: claim
title: For every odd m >= 3 the Baumslag-Solitar group BS(1,m) embeds in the Brin-Thompson group 3V
distinct_from:
  bs13-embeds-in-brin-thompson-3v: that is the single case m = 3, from SMART; this is every odd m, from the machines SMART_m.
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) in some nV and stays OPEN; this covers only odd m, and the one-head crossing machines used here cannot branch evenly (crossing-move-hierarchies-have-odd-branching).
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that puts every Baumslag-Solitar group in some finitely presented simple group through twisted Brin-Thompson hosts; this is an embedding into the untwisted group 3V itself.
---

**ESTABLISHED** (lane bh-free-18, lane proof, not reviewed) through
`bs-1-m-in-3v-via-odd-smart-renormalization`.

**Checks.**
- bh-refute hand-verified the chain: PASS (`research/artifacts/gq-bh-bh-refute-verify-bs1m-in-3v.md`,
  e28fb9446).
- For m = 3, 5, 7, 9, 11 every hypothesis of the renormalization criterion that is not a general
  theorem is decided by an exhaustive machine certificate
  (`research/artifacts/gq-bh-bh-free-18-odd-smart-certificate.md`).

For every odd `m >= 3` there are `s, u ∈ 3V` with `s` of
infinite order and `u s u^-1 = s^m`, so `BS(1,m) = ⟨a, t | t a t^-1 = a^m⟩ ≅ ⟨s, u⟩ ≤ 3V`.

**Credit and scope.**
- No priority claimed. Two bounded arXiv API queries (09-18) found no embedding of any `BS(1,n)`,
  `|n| >= 2`, into an untwisted `nV`, and no generalization of SMART. The `m = 3` case is
  `bs13-embeds-in-brin-thompson-3v` (09-18 swarm). The new input is the machine family `SMART_m`
  (`odd-smart-machines-have-exact-m-fold-moves`).
- Even `m`, in particular `BS(1,2)`, is not reached: every move of `SMART_m` is a crossing, and one-head
  crossing hierarchies branch an odd number of times.
- Negative `m` is not claimed.

**What it gives.**
- **Logarithmic distortion for every odd base.** `u^n s u^-n = s^{m^n}`, so `|s^{m^n}| <= 2n + 1` in `3V`.
- **All odd `BS(1,m)` in one finitely presented simple group.** Each `BS(1,m)` lies in `3V`, and
  `one-fp-simple-group-contains-every-brin-thompson-subgroup` (lane proof, not reviewed) gives one finitely
  presented simple group containing every `nV`. So a single finitely presented simple group contains
  every `BS(1,m)` with `m` odd (the host `DV_F` is Belk--Zaremsky's; no priority for the host). Adding
  `BS(1,2)` is possible through `odometer-2v-is-fp-simple-and-contains-bs12` (a finitely presented full
  clopen-transitive Cantor group, hence permutational by `permutational-boone-higman-iff-full-cantor-hosts`)
  and closure of the permutational class under finite direct products; `BS(1,2m')` for odd `m' > 1` is
  still not covered.
- **Stepping-stone gates.** The Baumslag--Solitar gate of `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`
  is passable at every odd prime separately. The gate at 2 stays open.
- **Subgroups.** `Z[1/m] ≤ 3V` for every odd `m`: it is the normal closure of `a` in `BS(1,m)`.

**Calibration.** At `m = 3` every step specializes to the refereed SMART route
(`bs13-in-3v-via-smart-renormalization`).
