---
rg: 2
id: transition-digraph-capacity-lifts-give-nonsurjunctive-sizes
kind: claim
title: A strict automaton puts every capacity sum that is monotone along its letter-transition digraph in NS(G), so NS(G) contains all large multiples of the gcd of the digraph's class sizes
distinct_from:
  donor-covering-types-give-nonsurjunctive-size-progressions: that needs the relay conditions (D1)/(D2) and multiplies only the active count, giving z + bt; this needs no donor map, only the sitewise letter transitions, and gives every sum Σ n(a) with n monotone along transitions, hence all large multiples of a gcd that can be 1 when gcd(z, b) is not.
  collapse-lifts-with-unique-largest-fiber-are-surjective: that proves letter-collapse lifts with a unique largest fiber are surjective; this builds the strict letter-collapse lifts whose labels act sitewise, which always have tied largest fibers, and computes exactly which sizes they reach.
  strict-automata-reach-power-residue-donor-types: that reduces the bridge to power-residue donor types; this reduces it to a digraph gcd with no residue condition.
  passive-fixing-injective-automata-are-surjective: that kills padding by fixed reserved symbols; here the added letters are label copies that move with the base letter, and the lift is strict whenever the base is.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every size above a failing one; this gives all large multiples of g(τ), which is below k but not 1 in general.
artifacts:
  - experiments/transition-capacity-lift-2026-09-17/check.py
---

**ESTABLISHED** by `transition-capacity-label-lift-proof`. Elementary, plus one import used only for item 4.

**Setting.** `G` is any group, `A` a finite alphabet with `|A| = k`, and `τ(x)(g) = μ((g^(-1)x)|_M)` a cellular
automaton with `1 ∈ M`. It is *strict* if it is injective and not surjective. `NS(G)` is the set of alphabet sizes
carrying a strict automaton over `G`.
- The *transition digraph* is `R(τ) = {(u(1), μ(u)) : u ∈ A^M} = {(x(g), τ(x)(g)) : x ∈ A^G, g ∈ G}` on `A`.
- A *capacity* is `n : A -> Z_{>=1}` with `n(a) <= n(b)` for every `(a, b) ∈ R(τ)`.
- An *upset* is `U ⊆ A` closed under `R(τ)`. Equivalently `U` is *sitewise absorbing*: `x(g) ∈ U` implies
  `τ(x)(g) ∈ U`.
- The *classes* are the strongly connected components of `R(τ)`. Put `g(τ) = gcd` of the class sizes.

**Theorem.** Let `τ` be strict on `A^G`.
1. **Capacity lift.** For every capacity `n`, `Σ_{a ∈ A} n(a) ∈ NS(G)`.
2. **Two-level form.** If `U` is an upset with `b = |U|` and `z = k - b`, then `bm + zs ∈ NS(G)` for all
   `1 <= s <= m`.
3. **Gcd form.** `g(τ)` is also the gcd of all upset sizes. `NS(G)` contains every multiple `d·n'` of `d = g(τ)`
   above some bound. For one upset with `d = gcd(b, z)`, `b = d b'`, `z = d z'`, the bound is `n' >= b'(b' + z')`.
   So a strict `τ` with `g(τ)` a power of two gives `2^j ∈ NS(G)` for all large `j`. With `g(τ) = 1`, `NS(G)` is
   cofinite. Example: an upset with `(b, z) = (7, 3)` gives `64 = 7·7 + 3·5`, although the donor type
   `(z, b) = (3, 7)` is not power-residue (`3 + 7t ≡ 3 (mod 7)`, and `3` is not a power of two mod `7`).
4. **No singleton upset.** A strict `τ` has no upset of size `1`. That is, no letter `a` is sitewise
   indestructible.
5. **Equivalences.**
   - `every-group-is-surjunctive-over-binary-power-alphabets` holds iff no strict automaton over any group has
     `g(τ)` a power of two.
   - `some-nonsurjunctive-group-gives-a-binary-power-one` holds iff, whenever `NS_all ≠ ∅`, some group carries a
     strict `τ` with `g(τ)` a power of two. This is logically equivalent to
     `strict-automata-reach-power-residue-donor-types`, and it has no residue condition and no donor map.
   - The converse directions are trivial: the class sizes sum to `k`, so `g(τ) | k`, and a strict automaton on
     `2^j` symbols has `g(τ)` a power of two.
   - So the whole content of both holes is the odd part of `g(τ)`. Item 3 certifies powers of two from a strict
     automaton exactly when no odd prime divides every one of its class sizes.
6. **Exactness for sitewise labels.** The strict letter-collapse lifts `Φ` of `τ` (`r ∘ Φ = τ ∘ r`, `r` sitewise)
   in which the label written at `g` is an injective function of the label read at `g`, given the base
   configuration, have alphabet sizes that are exactly the capacity sums of item 1.

**Why it matters.**
- Both binary-power holes become one digraph invariant, readable from the local table: the odd part of `g(τ)`.
  The power-residue arithmetic and the relay condition (D1) of the donor-covering reduction drop out.
- *Where it stops.* Identity layers `τ × id_c` and capacity lifts keep every certified size in `g(τ)Z`. The
  moves that can lower `g` are powers `τ^p` (since `R(τ^p) ⊆ R(τ)^p` has finer classes), conjugation by bijective
  automata, and rules that are not products. None is known to split a class of odd size.
- *Target for counterexample search.* A strict automaton with a letter `c` whose class is `{c}`, meaning no
  transition cycle passes through `c` except `c -> c`, already makes `NS(G)` cofinite. Its `c`-sites may persist
  or dissolve, but no other letter can come back to `c`.
