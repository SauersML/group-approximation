---
rg: 2
id: branching-squares-are-the-only-operadic-escape-from-the-cap
kind: claim
title: A finite-spine operad with finite transformations is capped whenever its split-refinement function is uniformly recursive; unary squares make both Ore and the cap local, so a machine-simulating operad must have branching squares, where reconciliation is not well founded and Ore is a global statement, the halting theorem in a machine operad
requires:
  - bounded-propagation-operads-have-capped-word-problems
  - complexity-bounded-host-classes-are-not-universal
  - symmetric-ore-operads-containing-their-carrier-are-full-groups
distinct_from:
  bounded-propagation-operads-have-capped-word-problems: that caps operads with a finite propagation alphabet; this caps every class whose split-refinement functions are uniformly recursive, and shows that unary squares already give a finite alphabet and imply Ore, so the only uncapped candidates have branching squares.
  edge-split-ore-iff-synchronization-and-tree-domination: that reduces Ore for one branching-square operad to two global statements; this explains why Ore is global exactly when squares branch, and that the same feature is the only room for machine simulation.
---

**Parts 1–3 ESTABLISHED** (lane bh-typeA-universal, 2026-09-18). They are elementary lane proofs,
given below, not independently reviewed. **Part 4 is an OPEN candidate** (the operadic ¬CAP
target). No priority claimed.

## Setting

As in `bounded-propagation-operads-have-capped-word-problems`:
- `𝒪` is a planar or symmetric operad with transformations;
- it has finitely many colors and finitely many generators;
- the transformation groupoid `ℐ` is finite;
- it is cancellative, satisfies (FS), and in 2–3 satisfies Ore.

- **Split-refinement function.** `ρ_𝒪(N)` is the largest, over generators `s` and operations `t`
  with the output of `s` and `deg t ≤ N`, of the least degree of a common multiple of `s` and `t`.
  - It is a finite maximum, since there are finitely many `t` of each degree.
  - Under Ore it is finite and computable by search.
- **(U), unary squares.** For every ordered pair of generators `(s, t)` with the same output, some
  common multiple has the form `s∘(u_1, …, u_k)`, where each `u_i` is a transformation or a single
  generator composed with transformations.
- A square is **branching** if some `u_i` needs two or more generators.

## Statement

1. **Unary squares make Ore local and cap the host.** (U) implies (BP) with `𝒫` the generators
   and transformations under the finite `ℐ`-closure. Therefore:
   - any two operations with the same output have a common multiple, so Ore holds with no global
     hypothesis beyond (U);
   - `ρ_𝒪(N) ≤ D·N`, where `D` is the largest arity;
   - with cancellativity and (FS), every finitely generated subgroup of `π_1(𝒪, X)` has word
     problem in time `2^{2^{O(n)}}`, by `bounded-propagation-operads-have-capped-word-problems`.
2. **Recursive refinement caps the host.** Let `K` be a class of such operads, and suppose there
   is a monotone recursive `F` with `ρ_𝒪(N) ≤ F(k_𝒪, N)` for every `𝒪 ∈ K`. Here `k_𝒪` is the
   size of the finite data of `𝒪`; in the word bound it also counts the chosen generating
   fractions.
   - Then there is a fixed recursive `T` such that every finitely generated subgroup of every
     `π_1(𝒪, X)`, `𝒪 ∈ K`, has word problem in time `C·T(C·n) + C·n + C`.
   - So `K` is not universal (`complexity-bounded-host-classes-are-not-universal`), and neither
     is the class of full groups `[[Λ]]` it presents
     (`symmetric-ore-operads-containing-their-carrier-are-full-groups`).
   - Growth that is linear, polynomial, exponential or tower-type, with constants from the data,
     is capped.
3. **Where a machine can live.**
   - By 1 and 2, a class escaping every recursive cap has branching squares.
   - Its split-refinement functions `ρ_𝒪` must also escape every fixed recursive bound in
     `(k_𝒪, N)`.
   - This is necessary, not sufficient: 2 is an upper bound only.
4. **OPEN candidate: machine operads.** For each total machine `M`, find a finitely generated
   symmetric operad `𝒪_M` with the following properties:
   - finite `ℐ`, (FS), cancellative;
   - Ore;
   - branching squares, whose reconciliation of a split against a comb of degree `N` runs `M`
     on an input of size about `N`;
   - a carrier `Λ_M` acting by fractions whose word problem is at least as hard as `M`'s running
     time.

   Then `π_1(𝒪_M) = [[Λ_M]]` is a finite-spine operadic host outside any given recursive class.
   This is the operadic ¬CAP statement.

## Proofs

1. **(U) ⇒ (BP) and Ore.** Let `𝒫` consist of the transformations and the operations `α∘g∘β`
   (`g` a generator, `α, β` transformations). It is finite since `ℐ` is.
   - **`t = α∘g∘β` with `g` a generator.** `x ≥ t` iff `x ≥ α∘g`, since `β` is invertible on the
     leaves. The pull-through relation `α∘g = g'∘γ` makes this iff `x ≥ g'`. So (U) for `(s, g')`
     gives `s∘(u_i) ≥ t` with `u_i ∈ 𝒫`.
   - **`t = α` a transformation.** `s ≥ α` already, with every `u_i = id`.

   So (BP) holds. The propagation and growth lemmas of
   `bounded-propagation-operads-have-capped-word-problems` (its Proof, part 2) use only (BP), not
   Ore. They produce a common multiple of any `b` and any `c`, of degree at most
   `D_𝒫^{r(c)}·deg b`, and here `D_𝒫 ≤ D`. The word bound is that node's Statement 3.
2. **The growth recursion.**
   - Let `ρ̄` be the monotone envelope of `ρ_𝒪`.
   - For `b` of degree `N` and `c = t_1∘(c_1, …, c_l)` with `r` generators, take a common multiple
     `X = t_1∘(z_j)` of `t_1` and `b`, of degree at most `ρ̄(N)`.
   - Recurse on the pairs `(z_j, c_j)`. At most `D` components, each of degree at most `ρ̄(N)`,
     give a common multiple of degree at most `D^r·ρ̄^{(r)}(N)`.
   - **Group multiplication.**
     - Fix group generators whose numerators have at most `r` generators.
     - Each multiplication maps the degree `N` of the current fraction to at most
       `Φ(N) = D^r·ρ̄^{(r)}(N)`.
     - After `n` letters the degree is at most `Φ^{(n)}(deg X)`.
   - **Computation.** A common multiple within the bound is found by search: candidates of degree
     at most the bound, each tested by divisibility. Divisibility and the final test `a = b` use
     the (FS) presentation, in time `2^{O(M)}` at degree `M`.
   - **The cap.** The total time is a recursive function of `(k_𝒪, n)` built from `F`,
     monotone in `k_𝒪`. Put `T(m)` equal to its value at `(m, m)`. For `n ≥ k_𝒪` the time is at
     most `T(n)`, and it is bounded by a constant below that. This is the form required by
     `complexity-bounded-host-classes-are-not-universal`. ∎
3. This is the contrapositive of 1 and 2.

## Why branching squares are different

With unary squares, passing a move through a split leaves one move on each piece. The
reconciliation recursion then descends and terminates, and it proves Ore on its way.

With a branching square `s∘(u_i) = t∘(u'_j)`, some piece receives a tree `u_i` of two or more
moves. Reconciling `b` with `c` then requires reconciling pieces of an already-refined `b` with
the leftover cofactors `u'`. The recursion calls itself on arguments larger than its input, so
it is **not well founded**.
- Nothing in the finite square data bounds `ρ_𝒪`.
- Ore stops being a consequence of the squares and becomes a global theorem, namely that every
  such reconciliation terminates.

This is exactly the situation of the edge-split operad.
- Its first square is branching: splitting `AC` against a split of `AB` needs two moves on
  `cone(A, A+B, C)`.
- Its Ore condition is the open pair (Sync′) + (TD) of
  `edge-split-ore-iff-synchronization-and-tree-domination`.
- There the growth is presumably controlled by integer arithmetic; that is not proved.

## Test rungs (shared with the CAP lanes)

- **R-a.** A finite-spine operad with branching squares whose `ρ_𝒪` is provably super-polynomial.
  This separates branching from unary squares quantitatively. A comb whose cofactors double at
  each level is the natural attempt; cancellativity and Ore must be checked.
- **R-b.** A family `𝒪_M` realizing the halting times of total machines in `ρ`. Ore for `𝒪_M` would
  then amount to the statement that `M` halts on every input, which is provable for each fixed total `M`.
- **R-c.** A lower bound: a carrier `Λ_M ≤ π_1(𝒪_M)` with hard word problem. Without R-c, a large
  `ρ` only slows the naive algorithm.

## Lesson for general BH

**The operadic complexity cap and the hardness of Ore have one source: branching squares.**
- **Unary squares.** At most one move per piece in each square makes the operad finite-state. It
  also proves Ore locally and gives uniformly doubly exponential word problems.
- **Branching squares.** A square that puts two or more moves on one piece makes reconciliation
  a non-well-founded recursion. Ore is then a global theorem, as for the closed-MCG edge-split
  host.

A finite-spine operadic host can carry an arbitrary decidable word problem only if its
reconciliation of a single split against a tree runs a machine. Its Ore condition is then that
machine's halting theorem.

So the ¬CAP question for operads has a precise meaning: can a finite branching-square
presentation have an Ore condition that is equivalent to the totality of a prescribed machine,
with the machine's complexity visible in a carrier?
