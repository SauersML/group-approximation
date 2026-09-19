---
rg: 2
id: no-nontrivial-germ-is-shift-conjugate-to-a-proper-power
kind: claim
title: If conjugating a germ x in Sym(N)/FSym(N) by the shift gives x^k with k ≠ -1 then x = 1; so Baumslag-Solitar near actions with t acting as the shift are trivial, and cyclic groups of germs cannot witness a non-strongly shift-similar group
distinct_from:
  fg-infinite-shift-similar-groups-are-strongly-shift-similar: that is the open finitely generated form of Mallery-Zaremsky Question 3.18; this rules out its simplest test case (a cyclic Γ with c(x) = x^k).
  infinite-shift-similar-groups-need-not-be-strongly-shift-similar: that builds a non-finitely-generated example from infinitely many sparse involutions; this shows no single element can play that role.
---

**ESTABLISHED** (lane proof, elementary, below; not independently reviewed; no priority claimed).

**Setting.** `N = {1, 2, ...}`, `φ(n) = n+1`, and `c(ḡ) = (φ^-1 g φ)‾` on `Sym(N)/FSym(N)`, i.e. `c(ḡ)` is the germ of
`n -> g(n+1) - 1`. By step 1 of `infinite-shift-similar-groups-need-not-be-strongly-shift-similar`, this is the
Mallery--Zaremsky germ shifting map `psi_infinity`.

**Statement.**
1. If `x ∈ Sym(N)/FSym(N)` and `c(x) = x^k` with `k ≠ -1`, then `x = 1`. For `k = 0` this holds because `c` is an automorphism. For `k = 1`: `f(n+1) = f(n) + 1` for large `n` makes `f` eventually a translation, which has index 0 only when it is the identity. The case `|k| >= 2` is proved below.
2. If `c(x) = x^-1` and `x ≠ 1`, then every representative `f` has all sufficiently large points on infinite
   orbits.
3. **Corollary.** If `Γ = <x>` is cyclic and `c(Γ) ⊆ Γ`, then `c(Γ) = Γ`. In particular there is no near action of
   `BS(1,k)`, `|k| >= 2`, on `N` in which `t` acts as the shift `φ` and `a` has nontrivial germ.

**Proof.** Let `f ∈ Sym(N)` represent `x`, with `m = |k|`. Fix `n_0` such that `f(n+1) = f^k(n) + 1` for all
`n >= n_0`, and put `D = [n_0, ∞)`. Then `φ ∘ f^k = f ∘ φ` on `D`, and by the same identity at `f^-k(a)`,
`φ ∘ f^-k = f^-1 ∘ φ` wherever `f^-k(a) ∈ D`. So for any set `A ⊆ D` that is invariant under `f^(±k)`, `φ` conjugates
`f^k|_A` onto `f|_(A+1)`. In particular `A+1` is `f`-invariant.

*Finite cycles.* Let `C ⊆ D` be a finite `f`-cycle containing `n`, and `A ⊆ C` the `f^k`-orbit of `n`, with
`|A| = |C| / gcd(|C|, m)`. Then `A + 1` is one `f`-cycle, contained in `D`, and it contains `n+1`. Inductively, the
cycles `C_j` of `n + j` are finite, lie in `D`, and have non-increasing sizes. So the size is eventually some
constant `L` with `gcd(L, m) = 1`, and then `C_(j+1) = C_j + 1`. The sets `S, S+1, S+2, ...` are then distinct
`f`-cycles, hence pairwise disjoint. That forces `|S| = 1`, since if `a < b` lie in `S` then `b ∈ S ∩ (S + (b-a))`.
So `f` fixes every point beyond some bound, and `x = 1`. Only finitely many cycles meet `[1, n_0)`. So if `f` has
infinitely many finite cycles, one lies in `D` and `x = 1`. The same argument for `m = 1` gives item 2's claim
about finite cycles.

*Infinite orbits: ends.* Let `z` be the number of infinite `f`-orbits. Each one is a `Z`-orbit with two ends.
`f^k` splits it into `m` infinite orbits, with `2m` ends in total. Every end of an `f^k`-orbit has a tail in `D`,
and `φ` maps that tail to a tail of an `f`-end (forward to forward, backward to backward). Distinct `f^k`-ends go
to distinct `f`-ends, because `φ` is injective and two rays define the same end iff they share a tail. So
`2mz <= 2z`, and for `m >= 2`, `z` is `0` or infinite.

*Infinite orbits: good orbits propagate.* Call an infinite `f`-orbit good if it lies in `D`. For a good orbit
`O ∋ n`, the `f^k`-orbit `A` of `n` lies in `D`. So `A + 1` is a single infinite `f`-orbit, contained in `D`, i.e.
good, and it contains `n+1`. Hence once some point is on a good orbit, so is every larger point. In that case no
infinite orbit meets `[1, n_0)`, since such an orbit contains arbitrarily large points.

*Infinite orbits: the parent map.* Suppose all points `>= K` lie on good orbits, and write `O(j)` for the orbit of
`j`. Then `O(j) = A_(j-1) + 1`, where `A_(j-1)` is the `f^k`-orbit of `j-1`. Its parent `P(O(j)) = O(j-1)` is
determined by `O(j)`, since `A + 1 = A' + 1` forces `A = A'`. Every infinite orbit contains infinitely many points
`>= K`, so it is visited at infinitely many times.
- If `O` is visited at times `j < j'`, the deterministic parents give `P^(j'-j)(O) = O`. So `O` lies on a finite
  cycle `Z_0` of `P`.
- The parent of a node on `Z_0` is on `Z_0`. So once the sequence `O(j)` leaves `Z_0` it never returns. But `O` is
  visited at arbitrarily late times, so from some time on the sequence stays on `Z_0`.
- Hence finitely many orbits cover a tail of `N`, and `z` is finite. By the end count `z = 0`, contradicting the
  existence of `O`.

*Conclusion, `m >= 2`.*
- If some point `>= n_0` lies on a good orbit, the last two paragraphs give a contradiction.
- Otherwise every point `>= n_0` lies on a finite cycle or on one of the finitely many infinite orbits meeting
  `[1, n_0)`. If there are infinitely many finite cycles, `x = 1`. If not, `z` is finite, so `z = 0` by the end count,
  and `N` would be a finite union of finite cycles, which is impossible.
- So `x = 1`, which is item 1.

*Item 2* is the finite-cycle paragraph with `m = 1`. *Item 3:* `c(x) ∈ <x>` means `c(x) = x^k`. By item 1, `x = 1`
or `k = -1`, and in both cases `c(<x>) = <x>`. ∎

**Calibration.** `k = -1` does occur. Take the slide `α` of `E_2`, which moves odd numbers up by 2 and even numbers
down by 2 (joined at the bottom). Then `n -> α(n+1) - 1` moves even numbers up by 2 and odd numbers down by 2, so
`c(α̅) = α̅^-1`. Its orbits are infinite, as item 2 requires.

**Lesson for general BH.** The shift at infinity is an index-one near-bijection. Conjugating by it preserves the
dynamics of germs at infinity: the number of infinite orbits, their ends, and cycle sizes along the ray. Taking a
`k`-th power multiplies ends by `k` and shrinks cycles, so the two cannot match. This end count is a cheap,
transferable obstruction to modelling an ascending HNN extension, `t^-1 B t ⊊ B`, inside a one-ray near action with
`t` acting as the shift. It explains why Mallery--Zaremsky found every natural shift-similar group strongly
shift-similar. It also warns that one-ray near-action hosts cannot be the mechanism for inputs that need `BS(1,k)`
relations with the shift as the stable letter.
