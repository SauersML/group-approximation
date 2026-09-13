# EX review, backlog, part 8: refill lanes, fourth batch (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`. Read at tip `e0b21d920` or later.

## 35. ex-weak-sofic-deep-wreath (322b216255): `simple-nonsofic-width-over-towers-with-symmetric-levels`: PASS

**Even permutations are commutators.**
- On `Z/L`, `i -> i+1` factors as `ρ_1 ρ_2`, with `ρ_1(i) = 1 - i` and `ρ_2(i) = -i`. It also factors as
  `ρ_a ρ_b`, with `ρ_a(i) = -i` and `ρ_b(i) = -1 - i`.
- Counting fixed points of `2i = 0` and `2i = ±1` gives the transposition counts:
  - for odd `L`, `((L-1)/2, (L-1)/2)`;
  - for even `L`, `(L/2, L/2 - 1)` and `(L/2 - 1, L/2)`.
- An even permutation has an even number of even-length cycles. Alternating the two factorizations
  equalizes the counts.
- So `σ = ι_1 ι_2` with `ι_2 = γ ι_1 γ^(-1)`, and then `σ = [ι_1, γ]`.

**Symmetric levels.**
- `τ in Alt(n)` is one commutator.
- The move takes `β = (1 ... n)` and `g_1 = (f_n ... f_2)^(-1)`. The cycle product is `1`, so `(g;1)` is a
  commutator by the base lemma of §31.
- The defect `z = f_n ... f_2 f_1` lies in `[H,H]`.
- Absorption at the `β`-adjacent coordinates `1, 2` then gives
  `c_W <= 2 + 2⌈c_H/3⌉ <= C = 3(m!+m+2)`.

**Relator width.**
- **Small root levels.** They lie in a copy of `Sym(N_1)`. Run the template argument of §34 there.
- **Large symmetric root levels.**
  - A balanced Rodgers block covers `Alt(Ω_0)`.
  - Hamiltonian-path dipoles in `2⌈2/ε_0⌉` rounds solve the base on `Ω_0`.
  - The defect in `[H,H]` costs `2C` pairs.
- **Recursion.** All conjugator tops lie in `Sym(Ω_0)` and fix the other coordinates, so the recursion
  happens inside the same pairs.

## 36. Dependency check: the coset-wreath hyperlinearity equivalence (tip `5bb164af6`)

**Why.** At d8cf5adad8, ex-nh-dyadic-pair demoted item 4 of
`nonamenable-relatively-kazhdan-infranormal-sofic-wreath` to a remark. The stated reason was that
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` "has its own route with open requirements".
Part 3 §§5.1, 5.3 and 5.5 and part 7 §24.2 consume that node.

**Graph state.**
- The node has one route, `tensor-gaussian-binary-wreath-equivalence-proof`, which requires three claims:
  - `binary-coset-lamp-coefficient-forces-relative-embedding`, through `tensor-lamp-expectation-relative-embedding-proof`
    with `requires: []`;
  - `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`, through
    `relatively-embeddable-pair-hnn-hyperlinear-proof` with `requires: []`;
  - `hnn-stable-letter-rounds-to-finite-order`, through `hnn-stable-letter-rounding-proof`, which requires
    `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`. That claim's route
    `hnn-amalgamated-free-haar-unitary-proof` has `requires: []`.
- No `invalidates` names any of these routes. A grep of `research/*.md` found none.

**Conclusion.**
- The equivalence computes established, so the part 3 and part 7 verdicts that consume it stand as recorded.
- The demotion does not follow from the graph, and I messaged the lane.
- I did not re-derive the equivalence itself (landed 09-07, 7f2fed8de). It is load-bearing for the RE/C slices,
  the difference-cocycle double theorem and the Kun--Thom Hecke necessity, so it is a candidate for a
  dedicated review.
