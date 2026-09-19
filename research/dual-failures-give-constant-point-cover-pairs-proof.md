---
rg: 2
id: dual-failures-give-constant-point-cover-pairs-proof
kind: route
title: Extract a context-free erasable pair from a collision, pad it with a random unbordered context, forbid the padded pattern, and swap lifted occurrences out one at a time
target: dual-failures-give-constant-point-cover-pairs
requires:
  - capobianco-kari-taati-dual-surjunctivity-toolkit
artifacts:
  - research/artifacts/erasable-pattern-avoiding-cover-pairs-2026-09-19.md
  - experiments/erasable-pattern-avoidance-2026-09-19/check_unbordered_context.py
---

Full proof in `research/artifacts/erasable-pattern-avoiding-cover-pairs-2026-09-19.md`, §§0–4.

**Conventions.** `(g.x)(h) = x(g^-1 h)`, and `F(x)(g) = f((g^-1 x)|_M)` for a finite memory `M`. A pattern `p` on
`P` occurs at `g` in `x` if `x(gk) = p(k)` for `k ∈ P`. `Δ(x, y)` is the finite set where `x ~ y` differ.

**Import (verbatim, from `capobianco-kari-taati-dual-surjunctivity-toolkit`, Doucha–Gismatullin).** "A CA T:
A^G → A^G is post-surjective if and only if it is strongly post-surjective". Let `Φ` be the constant.

**Step 0 (finite `G`).** A post-surjective automaton over finite `G` is onto the finite set `A^G`, hence bijective,
hence pre-injective. So assume `G` is infinite and `|A| ≥ 2`.

**Step 1 (Lemma E, erasable pair).** Take `x_0 ≠ x_0'`, `x_0 ~ x_0'`, `F(x_0) = F(x_0')`. Put `K = Δ(x_0, x_0')`,
`L = KM^-1M`, `u = x_0|_L`, `u' = x_0'|_L`. If `u` or `u'` occurs at `g` in `y`, switching the values on `gK` to
the other pattern leaves `F(y)` unchanged. The only outputs that could change are at `h ∈ gKM^-1`, and they read
only inside `gL`, where the two configurations look like translates of `x_0` and `x_0'`.

**Step 2 (Lemma U, unbordered context).** For `L' ⊇ L` and `c : L' \ L → A`, put `w = u ∪ c` and `w' = u' ∪ c`. We
need `c` non-constant such that for no `h ∈ H = KL'^-1 \ {1}` does `w` at `1` agree with `w'` at `h` on
`L' ∩ hL'`. For a uniform `c` and fixed `h`, the forced equalities `c(k) = c(h^-1 k)` on
`C_h = (L' ∩ hL') \ (L ∪ hL)` form a graph of paths and cycles. So the failure probability is at most
`|A|^{-(|L' ∩ hL'| - 2|L|)/2}`. The union bound over `H` together with `P(c constant)` goes to `0`:
- *`G` not locally finite.* Let `L' = B_R` in an infinite finitely generated `Γ ⊇ L`. The midpoint of a geodesic
  for `h` gives `|B_R ∩ hB_R| ≥ |B_ρ|` with `ρ = R - ⌈(R+r)/2⌉`. Also `|H| ≤ |B_{R+r}| ≤ |B_ρ|^2 |B_{2r+2}|`.
- *`G` locally finite.* Let `L'` be a finite subgroup `Γ ⊇ L`. Then `hL' = L'` and `|H| < |Γ|`.

**Step 3 (no creation).** If `y` has `w` at `g`, then `w'` occurs at no `h` with `hL' ∩ gK ≠ ∅`. This follows from
Step 2 translated by `g`, together with `w ≠ w'` for `h = g`.

**Step 4 (Theorem D).** Let `X = X_{w'}`.
- `X` is proper, and it contains all constants because `w'` is non-constant.
- For `x ∈ X` and `z ~ F(x)`, lift to `x' ~ x` in `A^G` with `Δ(x, x') ⊆ Δ(F(x), z)Φ`.
- The occurrences of `w'` in `x'` lie in `Δ(x, x')L'^-1`, a finite set.
- Swap them one at a time from `u'` to `u` on `gK`. By Step 1 this preserves `F`. By Step 3 each swap removes
  its occurrence and creates none.
- The result lies in `X`, maps to `z`, and differs from `x` inside `Δ(F(x), z)(Φ ∪ ΦL'^-1K)`. ∎
