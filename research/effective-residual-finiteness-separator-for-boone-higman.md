---
rg: 2
id: effective-residual-finiteness-separator-for-boone-higman
kind: claim
title: The class of groups whose finitely generated residually finite subgroups are all effectively residually finite separates Boone–Higman iff every finitely presented simple group is in it; Rauzy's decidable lamplighter amalgams lie outside it
requires:
  - hereditary-approximation-disproofs-of-boone-higman
  - bh-separators-must-omit-nested-decidable-hosts
  - rf-decidable-groups-embed-in-decidable-fg-branch-groups
  - fp-simple-group-containing-a-non-efrf-residually-finite-group
distinct_from:
  rf-decidable-groups-embed-in-decidable-fg-branch-groups: that is Bishop–Schesler's question, about branch hosts; its lesson says Rauzy-type inputs are "no obstruction" for Boone–Higman because simple hosts are never residually finite. This corrects that at the level of subgroups: non-effective residual finiteness is a live hereditary separator even though the hosts are simple.
  central-kazhdan-residual-separator-for-boone-higman: that separator is about Kazhdan subgroups whose centres die in finite quotients; this one is about residually finite subgroups whose finite quotients cannot be found. Both are residual-type and both are invisible to simple groups themselves.
  folner-separators-of-boone-higman: that is a growth-bound separator scale killed below towers; this separator is not a bound on any function of the subgroups' multiplication, and no tower-type kill applies to it.
  bh-separators-must-omit-nested-decidable-hosts: that asks for "a genuinely new invariant" beyond decision problems, complexity bounds and approximation properties; this is one, since its witness has solvable word problem.
---

**ESTABLISHED** (lane proof, elementary; Rauzy's theorem was read at source, arXiv:2002.02540 TeX, md5 daf6a587…, copy in `gq/src/bh-invent-11/rauzy.tex`; no priority claimed). The separating side is `fp-simple-group-containing-a-non-efrf-residually-finite-group`.

**Settled 2026-09-18: P_eff does not separate Boone–Higman.** (S1_eff) below is false. `nv-machines-realize-linear-time-lamp-centralizers` puts the Dyson group `L(A)` in `B_A` for the set `A` of `linear-time-rauzy-sets-exist`, which is closed but not effectively closed. So a finitely presented simple group contains a residually finite group that is not effectively residually finite. The theorem below is unchanged: it now shows that `P_eff` is a class that every Boone–Higman host must leave.

## Definition

- A finitely generated group `H` is **effectively residually finite (EFRF)** if some algorithm, given a word `w ≠ 1`, produces a homomorphism from `H` to a finite group that does not kill `w` (Rauzy, TeX l.78–81).
- `P_eff` is the class of groups `G` such that every finitely generated residually finite subgroup of `G` is EFRF.

## Theorem

1. **Hereditary.** `P_eff` is closed under isomorphism and subgroups. The condition quantifies over finitely generated subgroups, and those of a subgroup are among those of `G`.
2. **(S2) holds.** Rauzy's Theorem 2 (TeX l.83–87) gives a finitely generated residually finite group with solvable word problem that is not EFRF. Explicitly:
   - It is `L(A) = L *_{U_A} L`, two copies of the lamplighter `Z/2 ≀ Z` amalgamated along the lamps `u_i` with `i ∈ A` (l.125–146).
   - `A ⊂ Z` is recursive and closed in the profinite topology, but not effectively closed (Lemma, l.248–357).
   - By Proposition 1 (l.200–210): `L(A)` has solvable word problem because `A` is recursive, and is residually finite because `A` is closed. It is not EFRF, because EFRF would make `A` effectively closed (proof, l.215–232).

   So `L(A) ∉ P_eff`.
3. **So `P_eff` separates Boone–Higman iff (S1_eff) holds:** every finitely generated residually finite subgroup of every finitely presented simple group is EFRF.
   - If (S1_eff) holds, Boone–Higman fails at `L(A)`.
   - Boone–Higman implies `fp-simple-group-containing-a-non-efrf-residually-finite-group`.
   - By Rauzy §3 (l.365–413) that group then contains a finitely generated residually finite subgroup whose depth function is not bounded by any recursive function.
4. **Why the known kills do not reach it.**
   - **Not a decision problem of Kuznetsov type.** `L(A)`'s word problem is as easy as membership in `A`. What fails is the ability to find finite quotients, and those are not part of any finitely presented simple overgroup (which has none). So the §3 reduction of `bh-separators-must-omit-nested-decidable-hosts` to Kuznetsov profiles does not apply.
   - **Not an approximation property.** Every group in sight is residually finite or simple, so soficity-type arguments say nothing.
   - **Not refuted by any known host.** No finitely presented simple group is known to contain a non-EFRF residually finite group. The natural candidates are `V`, `2V`, `nV`, Röver–Nekrashevych groups and `W`. It is not known whether any of them has a non-EFRF residually finite finitely generated subgroup.
5. **Host transfer is consistent.** The simple Kazhdan host `K ⊇ L(A)` and its finitely presented overgroup `C` both contain `L(A)`, so both lie outside `P_eff`.

## What a kill would take

A finitely presented simple group containing `L(A)` for one Rauzy set `A`. Two facts constrain the shape (recorded in `fp-simple-group-containing-a-non-efrf-residually-finite-group`; the machine construction there is consistent with both):
- In any host, the amalgamated lamps must be separated from the rest of the base by a condition as complex as `A`. Neither a clopen stabilizer nor a virtual retract can do that.
- The double `L(A)` has index 2 in `L *_{U_A} (U_A × Z/2)`. So `L(A) ∈ B_A` iff `U_A` is the intersection of `L` with a centralizer in some `B_A` overgroup (`pbh-coset-wreaths-iff-identity-edge-hnns`).

## Lesson for general BH

A universal host cannot keep its residually finite subgroups effectively residually finite. It must contain subgroups whose finite quotients are hidden, at a depth that is not recursive, even though the host has no finite quotients at all.
- **What this rules out.** Any construction that places the input through a computable profinite, tree or level structure (Bishop–Schesler-type branch hosts, self-similar hosts, finite-level codings) produces only EFRF residually finite subgroups. Such a construction must therefore escape through non-effective placement, i.e. through the finite presentation of the host rather than through its dynamics.
- **Status.** This is a heuristic reading, not proved for every such host class.
