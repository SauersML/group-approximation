---
rg: 2
id: bartholdi-mitrofanov-proposition-2-4-gap-and-repair
kind: claim
title: In the arXiv versions of Bartholdi–Mitrofanov's construction the commutator [g,u] of Proposition 2.4 is nontrivial for every Minsky machine, so the printed proofs of Theorems A and A″ have a gap; replacing u by a partner p supported on 0*1A^ω restores Proposition 2.4 and both theorems for the modified table
distinct_from:
  bartholdi-mitrofanov-prop-2-4-gap-review: that is the referee's check at source of this gap and repair; this is the claim it checks, stated once for citation.
  finite-recursion-gives-no-computable-depth-bound: that imports Theorem A″; this supplies the repaired table that import now relies on.
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that uses the word encoding for hardness (its item (a)); this repairs the encoding.
---

## Route comparison record

The following comparison was formerly misplaced in `distinct_from`,
which accepts claim ids, not route ids. Its text is preserved without
adding a proof dependency or accepting a route:

- [nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups](nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups.md): that uses a Bartholdi–Mitrofanov recursion with non-recursive kernel; this supplies the repaired recursion it now uses.

**ESTABLISHED** (lane bh-birget, 2026-09-19; referee bh-ref-f PASS in both directions, 6747a7e43d, with the gap
confirmed in the arXiv LaTeX sources of 1710.10109v1 and v4).

**Source.** L. Bartholdi and I. Mitrofanov, *The word and order problems for self-similar and automata groups*,
arXiv:1710.10109 (v1 and v4), published in Groups Geom. Dyn. (2020).
- **Not checked:** the published version, which is paywalled. It may already correct what is described here.
- **Credit:** the construction, the Minsky-machine encoding, Proposition 2.3 and Theorem A′ are entirely theirs.
  This node concerns one step, the passage from Proposition 2.3 to a word-problem statement.

## The step in question

- **The setting.** `M` is a two-counter Minsky machine and `⟨Φ_M⟩` its functionally recursive group (§2.1).
  The action is on the right. Put `h = s_* x y` and `g = h t h^(-1)`.
- **Proposition 2.3,** unaffected: `M` does not halt iff `g` fixes `0^∞`.
- **Proposition 2.4,** as printed: "The Minsky machine 𝐌 halts if and only if [(s*xy)t(s*xy)^-1,u]≠1 in
  ⟨Φ𝐌⟩".
- **Its proof** describes `u` as follows: "it scans X∈A^ω for its longest prefix in {0,1}*, and exchanges all 0
  and 1 in that prefix". For the non-halting case it says: "then g in fact also fixes {0,1}^∞, so the supports of
  g and u are disjoint and [g,u]=1".

## The gap

The support of `u` is every sequence whose first letter is `0` or `1`, not just `{0,1}^∞`. It is not disjoint
from the support of `g`.

**Witness** (bh-ref-f's form). Take `X = 0 †₁ w`, and let the first instruction be of type I, as in the paper's
(2.1).
- `h` sends `0` to `𝐢₁`, with section `s_j x² y`.
- That section passes `†₁`: the state has no rule at markers, so the default applies, and `x`, `y` stop there.
- `t` passes `𝐢₁` and turns `†₁` into `†₂`.
- The paper's reverse identity restores `0`.
- So `X^g = 0 †₂ w`.

The action of `u` then gives the other side.
- `X^u = 1 †₁ w`, and `g` fixes every word beginning with `1`: for every `g′ ≠ u`, `Φ(1,g′) = (ε,1)`.
- So `X^(gu) = 1 †₂ w`, while `X^(ug) = 1 †₁ w`.

The other first instructions, and machines that halt at once, behave the same way (review §2). So `[g, u] ≠ 1` for
**every** machine. The non-halting half of Proposition 2.4 fails, and every test word of the proofs of Theorems A
and A″ is nontrivial.

## The repair

**The partner.** Replace `u` by `p`, where `Φ(0,p) = (p,0)`, `Φ(1,p) = (p′,1)` and `Φ(a,p) = (ε,a)` otherwise.
Here `p′` exchanges `0` and `1` with trivial section and fixes the other letters. Both are finite-state
involutions, with `supp(p) ⊆ 0^* 1 A^ω`. Nothing else in the table changes, since `u` occurs in no other rule.
Call the modified family `G′_M = ⟨Φ_M, p, p′⟩`.

**Proposition 2.4′.** `M` halts from `(s_*, 0, n)` iff `[g_n, p] ≠ 1`, where
`g_n = (s_* x y^(2^n)) t (s_* x y^(2^n))^(-1)`.
- **Does not halt ⇒ `[g_n, p] = 1`.**
  - Every section of `g_n` is a word in generators other than `p`, and each of these fixes `1` with trivial
    section.
  - By Proposition 2.3, `g_n` fixes every `0^m`, so it fixes `0^* 1 A^ω` pointwise.
  - That set contains `supp(p)` and is `p`-invariant, so the two commute.
- **Halts ⇒ `[g_n, p] ≠ 1`.** Let `K` be the depth at which `s_†` acts. The paper's computation gives
  `(0^(K+1) Y)^(g_n) = 0^K †₂ Y` with trivial section afterwards. For `X = 0^m 1 0 Z` with `m ≥ K + 1`:
  - `p` fixes `X^(g_n)`, whose first non-`0` letter is `†₂`;
  - but `(X^p)^(g_n) = 0^K †₂ 0^(m−K−1) 1 1 Z`.

**Consequences for the modified table.**
- **Theorem A:** no algorithm, given `Φ` and `s`, decides whether `s = 1`.
- **Theorem A″:** a fixed functionally recursive group has a non-recursive word problem. It uses the universal
  machine and the words `[g_n, p]`, of length `O(2^n)`.
- Both hold with the same proofs.
- `G′_M` is faithful on the regular tree `A^*`, so it is residually `W_(|A|)`.

## Where it is used

- `finite-recursion-gives-no-computable-depth-bound` needs only some faithful functionally recursive group with
  non-recursive word problem, so the repaired table suffices.
- `nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups` and `some-a2-action-has-a-nonrecursive-kernel`
  use the repaired recursion, which includes `p` and `p′`.
- `birget-question-via-decidable-bartholdi-mitrofanov-hosts` uses it for item (a) and Test 3.

**Scope.** §3 of the paper, on the order problem for automata groups, uses a different construction and was not
checked.
