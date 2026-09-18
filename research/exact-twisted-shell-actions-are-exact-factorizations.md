---
rg: 2
id: exact-twisted-shell-actions-are-exact-factorizations
kind: claim
title: Exactly twisted genuine shell actions are the same as exact factorizations R = <t>H of an ascending HNN extension with the base inside all negative translates of H; Thompson's F has none
distinct_from:
  twisted-genuine-shell-actions-pass-both-germ-gates: that derives the germ gates from a twisted action; this translates the exact version into a subgroup condition, and excludes F.
  restriction-realizations-of-twisted-shells-are-trivial: that excludes realizations by restricted homeomorphism actions; this is a purely group-theoretic reformulation and one exclusion.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**ESTABLISHED** (lane proof below; elementary; not independently reviewed; no novelty claimed).

**Setting.** `G <= Sym(N)` is *exactly twisted* if `g^+ ∈ G` for all `g ∈ G`, where `g^+(0) = 0` and
`g^+(n) = g(n-1) + 1`. Equivalently `s rho(g) s^-1 = rho(g^+)` holds off the point `0`. This is the
`ε = -1` twist of `twisted-genuine-shell-actions-pass-both-germ-gates`, with `φ(g) = g^+`.

1. **Reformulation.** Let `P` be a group, `φ` an injective endomorphism, and `R = P *_φ = <P, t | t g t^-1 = φ(g)>`.
   The following are equivalent:
   - an action `rho` of `P` on `N` with `rho(φ(g)) = rho(g)^+` for all `g`;
   - an action of `R` on `Z` in which `t` acts as `n -> n+1` and `P` fixes every negative integer;
   - a subgroup `H <= R` with `R = <t> H` and `<t> ∩ H = 1` (an exact factorization) such that
     `P <= ∩_(k>=1) t^-k H t^k`.
   Here `H` is the stabilizer of `0`, and extending `rho` by the identity on the negatives gives the
   action on `Z`. So exactly twisted shells are classified by exact factorizations of `R` through `<t>`.
2. **Thompson's F.** Take `R = F`, `t = x_0^-1`, and `P = <x_1, x_2, ...> ≅ F` with
   `φ(x_n) = x_(n+1)`. Then no nontrivial `rho` exists: every action of `F` on `Z` with `x_0 -> n -> n-1`
   and `x_1` fixing all negatives has `x_1` acting trivially.

**Proof of 2.** Put `p = rho(x_1)` and `τ: n -> n+1`, and let `p_m = τ^m p τ^-m`. Then `rho(x_(m+1)) = p_m`.
In `F`, `x_0 x_1^-1` commutes with `x_n` for `n >= 2`, so `u := p τ` commutes with every `p_m`, `m >= 1`,
and therefore preserves `Fix(p_m)`. Let `A = supp(p) ⊆ N`. If `n ∉ A - 1`, then `u(n) = n+1`. Applying
this to `Fix(p_m)` gives `A ⊆ (A+1) ∪ (A-m)` for every `m >= 1`. So the minimum `a` of `A` satisfies
`a + m ∈ A` for all `m`, and `A = [a, ∞)`. Then `Fix(p_1) = (-∞, a]` is `u`-invariant, and
`u(a-1) = p(a) ∈ A`, which forces `p(a) = a`. This contradicts `a ∈ A`, so `A = ∅`.

**Proof of 1.** Given `rho`, the extended `rho(g)` fixes the negatives, and `τ rho(g) τ^-1 = rho(g)^+ = rho(φ(g))`,
which is the defining relation. Conversely, `P` fixes `-1`, so `P` preserves `N`, and conjugating by `τ`
gives the `+` relation. `t` is transitive and free on `Z`, which is the factorization with `H = Stab(0)`.
Finally, `P` fixes `-k` exactly when `P <= Stab(-k) = t^-k H t^k`.

**Scope.** Only the exact twist is treated. Near twists, with finitely many defects per generator, are
not covered, so item 2 does not exclude near realizations of `F`. The open target remains
`fp-ray-near-actions-with-the-shift-exist`.
