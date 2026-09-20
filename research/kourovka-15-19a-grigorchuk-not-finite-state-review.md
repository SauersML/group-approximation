---
rg: 2
id: kourovka-15-19a-grigorchuk-not-finite-state-review
kind: claim
title: Referee review of 1e285c3457 (Kourovka 15.19(a), "some" form, p = 2 — a computable non-periodic ω with WP(G_ω) outside E) — the proof PASSES (detector length ≤ K·3^k, the dihedral left-section lift, the compactness list, the triple-exponential diagonalization, finite-state ⇒ WP in E); but priority is UNRESOLVED — Garzon–Zalcstein (TCS 88, 1991) studied exactly the Turing complexity of WP(G_ω), and the node must stay OPEN until that paper is read at source
distinct_from:
  kourovka-15-19a-some-grigorchuk-groups-are-not-finite-state: that is the lane node under review; this checks it step by step and records the priority question.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane node by bh-k1519, landed in
1e285c3457).**
- **On main:** read the node itself.
- **Web sources checked:**
  - the problem text, via the node's quotation of the LaTeX source;
  - the mathnet.ru abstract of Grigorchuk, Math. USSR-Sb. 54 (1986);
  - the bibliographic record and abstract of Garzon–Zalcstein, *The complexity of Grigorchuk groups with application
    to cryptography*, Theoret. Comput. Sci. 88 (1991) 83–98. The paper itself is paywalled and was not read.
- No code was run.

## 1. The problem text

- The quotation defines `F_p` in the problem's own words: "finitely generated groups acting faithfully on a
  `p`-regular rooted tree by finite automata". It includes the preamble, which says `F_p` groups have word problem
  "solvable in (at worst) exponential time".
- `E = ⋃_c DTIME(2^(cn))` and `F_d` (the same class for a `d`-regular tree) are the node's notation, not the
  problem's. That is fine, since the node proves more: `G_ω ∉ F_d` for every `d`.
- **The citation.** The problem cites "(R. I. Grigorchuk, Math. USSR–Sb., 54 (1986), 185–205)". That is *On the
  growth degrees of `p`-groups and torsion-free groups*. Its mathnet abstract says only "For each prime `p`,
  continuously many finitely generated `p`-groups that have intermediate growth are constructed". So it does not
  settle whether the `p = 2` family is the 1984 `G_ω`. The node's scope caveat stands as a flagged recollection.

## 2. The proof

- **Step 1: correct.**
  - `C_ℓ = [ℓ, aℓa]` equals `([a, ℓ′], [ℓ′, a])` when `u_ℓ = a`, and it is trivial otherwise.
  - `[a, ℓ′] = (ℓ″u′, u′ℓ″) ≠ 1`, because `ℓ″ ≠ 1` (every symbol recurs) and `a ∉ Stab(1)`.
- **Steps 2–3: correct, given the recalled inputs.**
  - Two recalled facts are used. `G_η` is branch when every symbol recurs. Every nontrivial normal subgroup of a branch
    group contains some `Rist(n)′` (Grigorchuk, *Just infinite branch groups*, 2000).
  - If `Rist(n)′` were abelian, `G_η` would be virtually solvable. An infinite finitely generated torsion group
    cannot be.
  - So the normal closure of `C_ℓ` is non-abelian, and two conjugates fail to commute.
- **Step 3′: correct.**
  - Nontriviality of a fixed word is witnessed at a finite level, so it depends on finitely many `η_i` and is open.
  - `{η ∈ Ω_8 : u_ℓ(η_1) = a}` is compact, so a finite list `Γ_ℓ` exists.
  - Its non-constructivity is harmless: the diagonalization defeats every machine, including one with `Γ_ℓ` hardwired.
- **Step 4 (the lift): correct.** With `z = (a, z′)`:
  - `L(a) = aza = (z′, a)` and `L(ℓ) = (u_ℓ, ℓ′)`. So `L(w) = (τ(w), w|_{G_{sη}})`, with `τ(w) ∈ ⟨a, z′⟩`.
  - `⟨a, z′⟩` is dihedral, so `τ(F″) = 1`, and `L(w) = 1` iff `w = 1` in `G_{sη}`.
  - `L` is an endomorphism with `|L(x)| ≤ 3`, so `L(F″) ⊆ F″` and `|L(w)| ≤ 3|w|`.
- **Step 5 (the crux, detector length): correct.**
  - `W_k` is the composite of `k − 1` maps `L`, built from `ω_1 … ω_(k−1)`, applied to one of finitely many fixed
    words `D_(ℓ,g)`. So `|W_k| ≤ 3^(k−1) · max|D| = K · 3^k`.
  - Iterating step 4 keeps every stage in `F″`. So `W_k = 1` in `G_ω` iff `D = 1` in `G_(s^(k−1)ω)`, which reads
    `ω_k`.
- **Step 6: correct.** Deciding `ω_k` takes `O(1)` word-problem calls on words of length `≤ K·3^k`, after the `ω_j`,
  `j < k`, are known. The total time is `2^(c′ 3^k)`. Changing the generating set costs a linear factor in `E`.
- **Step 7: correct.**
  - Each aligned block of four supplies `0, 1, 2`, so every window of eight contains a full block, and every shift of
    `ω` lies in `Ω_8`.
  - The diagonal choice `x_m = v + 1 mod 3` defeats every machine that computes `ω_k` within `t(k) = 2^(2^(2^k))`
    at infinitely many of its stages.
  - `2^(c′ 3^k) < t(k)` eventually. So `WP(G_ω) ∉ E`, and `ω` is computable and not eventually periodic.
- **Step 8: correct.** The product automaton of a word of length `n` has at most `s^n` states, so triviality is a
  reachability check in time `2^(O(n))`. The bound is invariant under isomorphism up to change of generators. So
  `G_ω` is in no `F_d`.

**Minor repair.** `G_ω` has solvable word problem for computable `ω` (Grigorchuk 1984). This is needed for the
"residually-2 with solvable word problem" sentence. It is recalled and should be marked so.

## 3. Priority: unresolved, and it decides the grade

- **What Garzon–Zalcstein claim.** Their paper (TCS 88 (1991) 83–98) studies "the Turing complexity of the word
  problems of a class of groups introduced by Grigorchuk". Its abstract, as indexed, says these word problems "yield
  natural complete sets that separate time and space complexity classes if they are distinct".
- **Why it matters.** That strongly suggests they already show that `WP(G_ω)` can be made complete for, or at least
  as hard as, prescribed complexity classes by choosing computable `ω`. That is the content of steps 5–7.
- **The consequence.** If so, the "some" form of 15.19(a) for `p = 2` follows from Garzon–Zalcstein together with the
  problem's own preamble. The node's contribution would then be the self-contained detector proof, and the grade would
  be **attribution**.
- The node does not cite Garzon–Zalcstein. It must, and the paper must be read at source first. This should go
  through the MSI library route, not a local PDF read by a lane.
- Kourovka v46 still lists 15.19(a) with no comment, per the node, and I found no printed answer. But
  Garzon–Zalcstein would have to be checked before anyone calls the answer new.

## Verdict

- **Mathematics: PASS.** Steps 1–8 are correct. The detector bound `|W_k| ≤ K·3^k` holds, the dihedral lift is right,
  and the triple-exponential diagonalization puts `WP(G_ω)` outside `E`.
- **The two recalled inputs are low-risk but unverified here:** the branch property of `G_ω` and the rigid-stabilizer
  lemma; and that the `p = 2` case of the 1986 family is the 1984 `G_ω`.
- **Status: keep OPEN** ("proof claimed, refereed PASS; priority pending"). Read Garzon–Zalcstein 1991 at source, and
  the 1986 paper's construction for the scope caveat. If Garzon–Zalcstein prove arbitrary complexity for computable
  `ω`, grade it as attribution to them.
