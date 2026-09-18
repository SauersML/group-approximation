---
rg: 2
id: coprime-baumslag-solitar-images-in-va-are-metabelian
kind: claim
title: Every homomorphic image of BS(m,n), gcd(m,n) = 1 and |m| ≠ |n|, inside the Thompson-like group VA (so inside F, T, V, T̄) is cyclic-by-cyclic; so no quotient of BS(2,3) keeping [tat^-1, a] lies in VA
requires:
  - gl-n-q-embeds-in-fp-simple-group
distinct_from:
  baumslag-solitar-groups-are-free-by-metabelian: that is structure of BS(m,n) itself; this constrains its quotients that live in VA.
  every-decidable-group-is-a-limit-of-isolated-groups: that is Cornulier--Guyot--Pitsch Question 1; this excludes one natural family of isolated quotients (finitely presented subgroups of V with a locally moving simple subgroup) for its test case BS(2,3).
---

**ESTABLISHED** (lane proof below, elementary modulo the cited theorem, not reviewed; no priority
claimed). It rests on Burillo--Felipe, arXiv:2605.09763v1, Theorem 1, as quoted in obstruction O4 of
`gl-n-q-embeds-in-fp-simple-group`: "Let f in VA have infinite order. Then ⟨f⟩ is undistorted in VA"
(unrefereed preprint; not re-read here).

**Statement.** Let `G = BS(m,n) = ⟨a, t | t a^m t^{-1} = a^n⟩` with `gcd(m,n) = 1`, and let
`ψ: G → VA` be a homomorphism with image `Γ = ⟨α, τ⟩`, `α = ψ(a)`, `τ = ψ(t)`.
1. If `|m| ≠ |n|`, then `α` has finite order.
2. In any group, if `α` has finite order `N` and `τ α^m τ^{-1} = α^n` with `gcd(m,n) = 1`, then
   `gcd(N, mn) = 1`, `⟨α⟩` is normal, and `Γ = ⟨α⟩⟨τ⟩` is cyclic-by-cyclic; in particular
   `[τ α τ^{-1}, α] = 1`.
3. So for `|m| ≠ |n|`, `gcd(m,n) = 1`, every image of `BS(m,n)` in `VA` is cyclic-by-cyclic. For
   `BS(2,3)` the commutator `c = [t a t^{-1}, a]`, which is nontrivial in `BS(2,3)`, dies in every
   image in `VA`, hence in `F`, `T`, `V` and `T̄`.

**Consequence for CGP Question 1.** Finitely presented subgroups of `V` that contain a locally moving
simple subgroup are isolated (`fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`). None of
them is a quotient of `BS(2,3)` in the basic neighbourhood where `c ≠ 1`. So Thompson-type hosts in
`VA` cannot supply the isolated quotients that `every-decidable-group-is-a-limit-of-isolated-groups`
needs at `BS(2,3)`.

**Proof.**
1. Swapping `t` with `t^{-1}` exchanges `m` and `n`, so assume `|m| < |n|`. Induction gives
   `t^k a^{m^k} t^{-k} = a^{n^k}` (each step conjugates `a^{m·(n^j m^{k-j-1})}` by `t`). Hence the word
   length of `α^{n^k}` in `Γ` is at most `2k + |m|^k`. `VA` is finitely generated, so lengths in `VA` are
   at most `C` times lengths in `Γ`. If `α` had infinite order, Burillo--Felipe would give
   `|α^{n^k}|_{VA} ≥ c|n|^k` for some `c > 0`, which contradicts `c|n|^k ≤ C(2k + |m|^k)` for large `k`.
2. `α^m` and `α^n` are conjugate, so they have the same order: `N/gcd(N,m) = N/gcd(N,n)`, so
   `gcd(N,m) = gcd(N,n)`, which divides `gcd(m,n) = 1`. So `α^m` and `α^n` both generate `⟨α⟩`, and
   `τ⟨α⟩τ^{-1} = ⟨τ α^m τ^{-1}⟩ = ⟨α^n⟩ = ⟨α⟩`. So `⟨α⟩` is normal in `Γ = ⟨α, τ⟩`, `Γ/⟨α⟩` is cyclic,
   and `τατ^{-1} ∈ ⟨α⟩` commutes with `α`.
3. Combine 1 and 2. `c ≠ 1` in `BS(2,3)` by Britton's lemma: `c = t a t^{-1} a t a^{-1} t^{-1} a^{-1}`
   contains no pinch `t a^{2k} t^{-1}` or `t^{-1} a^{3k} t`: its three `t`-segments are `t a t^{-1}`,
   `t^{-1} a t` and `t a^{-1} t^{-1}`, and `a^{±1} ∉ ⟨a^2⟩`, `a ∉ ⟨a^3⟩`.
