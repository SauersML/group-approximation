---
rg: 2
id: ascending-hnn-free-no-z-localized-proof
kind: route
title: A cyclic subgroup meets phi(F) with index at most the size of its Stallings graph, so each iterate adds a root exponent bounded by that size
target: ascending-hnn-extensions-of-free-groups-contain-no-z-localized
requires:
  - free-group-mapping-tori-contain-no-z-localized
---

**Imports (textbook, not re-read).**
- (R) In a free group every nontrivial element is `r^e` for a unique `r` that is not a proper power, with `e >= 1`.
  Also `y` is a `p`-th power if and only if `p | e(y)`, since centralizers are cyclic.
- (St) Stallings: a finitely generated `H ≤ F` has a finite folded graph `Γ_H` with a base vertex `o`. A reduced
  word lies in `H` if and only if it labels a closed path at `o`. Folded means each vertex has at most one edge with
  each label `a^(±1)`, so reading a word from a vertex is a deterministic, injective partial map.

**Lemma (bounded index in cyclic subgroups).** Let `H ≤ F` be finitely generated with `V = |V(Γ_H)|`, and let
`s ∈ F` have `s^j ∈ H` for some `j >= 1`. Then the least such `j` is at most `V`, and it divides every such `j`.
*Proof.*
- Write the reduced form `s = u s' u^(-1)` with `s'` cyclically reduced. Then `s^j = u s'^j u^(-1)` is reduced.
- By (St), `s^j ∈ H` if and only if reading `u` from `o` reaches a vertex `v`, and reading `s'^j` from `v` returns
  to `v`.
- Reading `s'` is an injective partial map `σ` on the finite vertex set. So `σ^j(v) = v` for some `j` exactly when
  `v` is `σ`-periodic, and then the valid `j` are the multiples of its period, which is at most `V`. ∎

**Part 1.**
- Let `H = φ(F)`, which is finitely generated because `F` is. Take `φ(r) = s^f` with `r` and `s` not proper powers.
  Then `s^f ∈ H`.
- Let `m` be the least `j` with `s^j ∈ H`. By the lemma `m | f` and `m <= V_φ`.
- Write `s^m = φ(w)`. Then `φ(w^(f/m)) = s^f = φ(r)`, and injectivity gives `w^(f/m) = r`.
- `r` is not a proper power, so `f/m = 1` and `f = m <= V_φ`. ∎

**Part 2.** Let `φ^k(x) = r_k^(e_k)` with `r_k` not a proper power, as in (R). Then
`φ^(k+1)(x) = φ(r_k)^(e_k) = r_(k+1)^(f_k e_k)`, where `φ(r_k) = r_(k+1)^(f_k)` and `r_(k+1)` is not a proper power.
- By uniqueness in (R), `e_(k+1) = f_k e_k`, so `e_k = e_0 f_0 ⋯ f_(k−1)`.
- By part 1 each `f_i <= V_φ`. By (R), `φ^k(x)` is a `p`-th power exactly when `p | e_k`.
- Hence `p | e_0`, or `p` divides some `f_i`, which forces `p <= V_φ`. ∎

**Part 3.**
- Suppose `A ≤ G_φ` with `A ≅ Z[1/P]` and `P` infinite. The element `1` is divisible in `A` by every `p ∈ P`.
- Part 1 of `free-group-mapping-tori-contain-no-z-localized`, a tree argument refereed by gq-referee-a, gives some
  `x ∈ F ∖ {1}` for which `φ^k(x)` is a `p`-th power for infinitely many primes `p`. Its proof goes through for
  every rank-one group whose element `1` is divisible by infinitely many primes.
- That contradicts part 2. ∎
