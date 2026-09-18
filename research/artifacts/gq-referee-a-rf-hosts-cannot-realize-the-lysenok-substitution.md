# Referee report (gq-referee-a, proof-gap lens): residually finite hosts cannot realize the Lysenok substitution

**Reviewed:** `rf-hosts-cannot-realize-the-lysenok-substitution` (lane bh-self-similar, de682dfb7), read on
origin/main, with its proof inline.

**Verdict: PASS.** There are two nits.
- For the citation lens:
  - injectivity of the Lysenok substitution;
  - the identification `Γ*_σ = Γ̃`;
  - Sapir–Wise's proof that `Γ̃` is not residually finite.

## The kernel argument (the author asked about this)
- **`K ∩ N = 1`.**
  - `K ∩ Γ = 1`, because `Γ ≤ P`.
  - `tΓt^(−1) = σ(Γ) ⊆ Γ`, so the `t^(−n)Γt^n` form an ascending chain with union `N`, the normal closure of `Γ`.
  - `K ∩ t^(−n)Γt^n = t^(−n)(K ∩ Γ)t^n = 1`, so `K ∩ N = 1`. Both subgroups are normal, so `[K,N] = 1`. ✓
- **The form `k = nt^m`.**
  - `Γ*_σ/N ≅ Z`, so `k = nt^m` with `m ≠ 0`.
  - `k^(−1) = (t^(−m)n^(−1)t^m)t^(−m)` gives the reduction to `m ≥ 1`.
  - `k` centralizes `Γ ⊆ N`, which gives `nσ^m(g)n^(−1) = g`.
  - With `n = t^(−j)ht^j` and conjugation by `t^j`: `σ^(m+j)(g) = h^(−1)σ^j(g)h`. Both sides lie in `Γ`, so this is an
    identity in `Γ`. ✓
- **The strict chain.**
  - On `Λ = σ^j(Γ)`, conjugation by `h` realizes `σ^m`. So `h^(−1)Λh = σ^(m+j)(Γ) = σ^j(σ^mΓ)`.
  - This is strictly contained in `Λ`, because `σ^j` is injective and `σ^m(Γ) ⊆ σ(Γ) ⊊ Γ`.
  - Conjugation preserves strict inclusions, so `h^(−i)Λh^i` is strictly decreasing. Taking `i = ord(h)` returns
    `Λ`, a contradiction. So `K = 1`. ✓
- **The contradiction uses nothing about `P`.** It needs only that `Γ` is torsion, `σ` is injective and proper, and
  `Γ ↪ P`.

## Item 2
- `σ(a) = aca`, and `b, c, d` lie in `St_Γ(1)`, so `σ(Γ) ⊆ St_Γ(1) ≠ Γ`.
- `Γ` is torsion.
- So any `P` realizing `σ` contains `Γ̃`. `Γ̃` is not residually finite, and subgroups of residually finite groups are
  residually finite, so `P` is not residually finite. ✓

## Nits
- **N1.** Say "a *locally finite* rooted tree", or "a finitely branching" one. Automorphism groups of rooted trees
  are residually finite only in that case. Automaton groups qualify.
- **N2.** Record that the contradiction lies entirely in `Γ`. The statement therefore extends verbatim to any
  torsion group with a proper injective endomorphism, as item 1 already says. So the Lesson's "incompatible with
  residual finiteness" rests only on the cited fact that `Γ*_σ` is not residually finite.
