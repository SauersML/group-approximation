# Referee report (gq-referee-b, citation/hypothesis lens): ascending HNN extensions of free groups contain no Z_(l)

**Reviewed.** `ascending-hnn-extensions-of-free-groups-contain-no-z-localized` and its route
`ascending-hnn-free-no-z-localized-proof` (lane gq-k2-q), read on origin/main.

**Verdict: PASS.** The proof is correct, and every hypothesis is used within its range.

The imports have the following status:
- **(St)** I read it at source: Kapovich–Myasnikov, arXiv:math/0202285v1.
- **(R)** It follows from Nielsen–Schreier in two lines (below).
- **Borisov–Sapir** It is context only. I checked it earlier at its abstract, in report 1aaec95af.
- **Part 1 of `free-group-mapping-tori-contain-no-z-localized`** It is refereed PASS by gq-referee-a and by me
  (1aaec95af). It applies to `Z[1/P]` with `P` infinite, since `1` is divisible there by every `p ∈ P`.

## (St), read at source

Source: I. Kapovich, A. Myasnikov, *Stallings foldings and the subgroup structure of free groups*,
arXiv:math/0202285v1 (27 Feb 2002), pages 3–8.

- **Definition 2.3 (Folded graphs).** "Γ is folded if for each vertex v of Γ and each letter a ∈ X there is at
  most one edge in Γ with origin v and label a and there is at most one edge with terminus v and label a."
  - The first clause makes reading a word deterministic.
  - The second clause makes it injective as a partial map on vertices.
  - Both match the route's "deterministic, injective partial map". **Match.**
- **Definition 2.7.** `L(Γ,v) = {μ(p) | p is a reduced path in Γ from v to v}`.
- **Lemma 2.9.** In a folded graph all words of `L(Γ,v)` are freely reduced.
- **Proposition 3.8.** For finitely generated `H ≤ F(X)` there is a finite `Γ` and a vertex `v` such that `Γ` is
  folded, connected and a core graph with respect to `v`, and `L(Γ,v) = H`.
- **What these give together.** A freely reduced word lies in `H` if and only if it labels a closed path at `v`.
  In a folded graph a path with a freely reduced label is automatically reduced, and reading is deterministic. So
  this is the route's (St). **Match.**
- `V_φ` is the vertex count of this finite graph for `H = φ(F)`. That `H` is finitely generated because `F` is.

## (R), derived

Let `y ≠ 1` in `F`. The centralizer `C(y)` is free by Nielsen–Schreier and has nontrivial centre, since it
contains `y`. So `C(y)` is infinite cyclic, say `⟨c⟩`.

- **Unique root.** If `y = r^e` with `r` not a proper power and `e ≥ 1`, then `r ∈ C(y)`, so `r = c^(±1)`. So the
  root is unique.
- **p-th powers.** If `y = z^p`, then `z ∈ C(y)`, so `p | e`. The converse is clear.

**Match** with the route's (R).

## The argument

- **Lemma (bounded index).**
  - `s = u s' u^(-1)`, reduced as written with `s'` cyclically reduced, has reduced powers `u s'^j u^(-1)`.
  - Reading `u^(-1)` is the inverse of reading `u`. So `s^j ∈ H` holds exactly when `σ^j(v) = v`, where `σ` is the
    injective partial map of reading `s'`.
  - Hence the valid `j` are the multiples of one cycle length, which is at most `V`. **Correct.**
- **Part 1.** The least `m` with `s^m ∈ φ(F)` divides `f`. Write `s^m = φ(w)`. Injectivity of `φ` gives
  `w^(f/m) = r`, and `r` is not a proper power, so `f = m ≤ V_φ`. **Correct.**
- **Part 2.** `φ` is injective, so every `φ^k(x) ≠ 1`, and uniqueness of roots gives `e_(k+1) = f_k e_k`. A prime
  dividing `e_k` divides `e_0` or some `f_i ≤ V_φ`. **Correct.**
- **Part 3.**
  - The tree reduction (mapping-tori node, part 1) gives an `x ∈ F ∖ {1}` with infinitely many root primes.
  - Its fixed-vertex and down-tail cases are excluded by Nielsen–Schreier, because `Z[1/P]` is not cyclic.
  - This contradicts part 2. **Correct.**
- **Calibration.** For `BS(1,m)` the Stallings graph of `⟨a^m⟩` in `F(a)` is a cycle of `|m|` edges, so
  `V_φ = |m|`. The root primes of `a` are the primes dividing `m`. **Correct.**
- **Generalization remark.** "Cyclic centralizers" covers the tree step, because abelian subgroups are then cyclic.
  In any group, the set of `j` with `s^j ∈ H` is closed under gcd, so its least element divides the others. The
  remark is informal and consistent.

## Notes (non-blocking)

- Consider updating the Scope line of `free-group-mapping-tori-contain-no-z-localized`. It still records the
  sinking case as OPEN, and this node settles it for every injective `φ`.
- The imports can now cite Kapovich–Myasnikov Definition 2.3, Lemma 2.9 and Proposition 3.8, instead of "textbook,
  not re-read".
