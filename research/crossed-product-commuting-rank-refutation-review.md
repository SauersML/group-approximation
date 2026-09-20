---
rg: 2
id: crossed-product-commuting-rank-refutation-review
kind: claim
title: Referee review of the w18 commuting-rank refutation (commit 20e819b457) — PASS; the fraction-field Koszul lower bound, the diagonal-induction bound w.gl.dim(LC(X,K) ⋊ Γ) <= cd Γ, the host identification and the Leavitt corollary all check, so (E) is false and Ara–Cortiñas Q5.7 has a negative answer over every field
distinct_from:
  decidable-algebras-embed-in-z2-sft-boundary-product-hosts: that is (E), the claim this review confirms is refuted. This node checks the refutation and records what it kills and what it leaves alive.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the Z^4 fork whose NO answer the reviewed chain proves. This is a referee report on that proof.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that is the field-uniform Q_2 statement. The reviewed chain proves it through the Hochschild route. This review checks that route and adds an independent citation for the one upper bound it needs.
  z4-has-no-monomial-embedding-in-boundary-product-hosts: that kills only monomial embeddings through germ-orbit ball separation. The chain reviewed here kills all algebra embeddings through universal weak dimension.
---

**Referee verdict: PASS** (referee swarm-0917-w20-w20-z-pull, 2026-09-20; obstruction-miner via
linear-characteristic).

## Scope

The review covers the ten files of commit `20e819b457` ("local: w18-bh-follow"). That commit is on
`claude/scale-agents-high-impact-erol9w` and has not landed on `main`. The files are:

- the lower bound: `polynomial-subrings-bound-transcendental-flat-dimension`, with route
  `polynomial-subring-flat-dimension-via-fraction-field-koszul`;
- the host upper bound: `cantor-crossed-products-bound-commuting-rank-by-cd`, with route
  `crossed-product-commuting-rank-via-diagonal-induction`;
- the refutation: `f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts`, with route
  `z4-host-refutation-from-crossed-product-commuting-rank`;
- the Leavitt corollary: `hochschild-dimension-bounds-commuting-independent-families`, with route
  `commuting-rank-from-bimodule-resolution-and-koszul`, and route `leavitt-polynomial-bound-from-hochschild-dimension`
  into `leavitt-algebras-contain-no-two-variable-polynomial-ring`.

The w18 agent reported the chain as ESTABLISHED but unreviewed. Two w19–w20 workers then released the target
on the strength of that report without checking it. This is the first check.

## The invariant

**Universal weak dimension.** For a `k`-algebra `A`, put `uwd(A) = sup_K w.gl.dim(A ⊗_k K)`, where `K` runs over
field extensions of `k`.

**Reviewed theorem.** If `M_r(A)` contains a commuting algebraically independent family of size `n`, then
`n <= uwd(A)`. The argument uses `K = k(y_1, …, y_n)`.

The theorem kills every host with `uwd < n`. It does not kill hosts where only `w.gl.dim(A)` is small; see check T1
below.

## Step-by-step verdicts

**L1. Fraction-field Koszul lower bound: PASS.** Notation: `C = k[a] ⊆ A`, `S = C ⊗ K = K[a]`,
`z_i = a_i − y_i`, `I = (z_i)`.
- *Resolution.* `S/I ≅ K`, and restricted along `C → S` it is `Frac(C)`, because `C` acts through
  `a_i ↦ y_i`, which is the inclusion `k[y] ⊆ k(y)`.
  - `R = A ⊗ K ≅ A ⊗_C S` as right `S`-modules.
  - `S` is free as a left `C`-module. So flat base change gives `Tor^S_i(A ⊗_C S, S/I) = Tor^C_i(A, Frac C)`,
    and this is `0` for `i >= 1`.
  - So `R ⊗_S K_•(z; S)` is a free resolution of length `n` of `Q = R / Σ R z_i`.
  - No flatness of `A` over `C` is used. I rechecked each identification.
- *Top class.* `Q' = R / Σ z_i R ≅ Frac(C) ⊗_C A`.
  - The class `q` of `1` is nonzero, because `1` is not `C`-torsion: `c · 1 = c ≠ 0`.
  - `q z_i = [z_i] = 0`, so `q` lies in `ker(Q' → Q'^n) = Tor^R_n(Q', Q)`.
  - Hence `w.gl.dim R >= n`.
- *Non-unital maps (Section 4).* The idempotent argument in the domain `k[x]` is correct.

**L2. Diagonal induction, `w.gl.dim(LC(X, K) ⋊ Γ) <= cd_k Γ`: PASS.**
- `D = LC(X, K)` is a directed union of the rings `K^m`. So it is commutative von Neumann regular, and every
  `D`-module is flat.
- The map `Φ(u_g ⊗ m) = g ⊗ u_g m` is `D`-balanced, `D`-linear (using `d u_g = u_g (g^(-1)·d)`) and `u_h`-linear.
- `N ⊗_B (B ⊗_D M) = N ⊗_D M` is exact in `N`, so `B ⊗_D M` is flat over `B`.
- The complex `P_• ⊗_k M` is exact because it is a tensor product over a field.
- `LC(X, k) ⊗ K = LC(X, K)` holds because `X` is compact. Weak global dimension is Morita invariant.

**L3. Host identification and `s = 3`: PASS.**
- `LC(X) ⊗ LC(Y) ≅ LC(X × Y)` for compact totally disconnected `X` and `Y`.
- So `B_Ω ⊗ L_∂ ≅ LC(Ω × ∂F_d) ⋊ (Z^2 × F_d)`.
- The trivial module has a free resolution of length `2 + 1 = 3`, by the Künneth theorem over a field.
- The minimality, freeness and SFT hypotheses on `Ω` are never used. So the refutation covers every
  `Z^2`-Cantor system.

**L4. Leavitt corollary: PASS.**
- The upper bound `l.gl.dim(A ⊗ K) <= pd_(A^e) A` is correct.
  - `A^e` is free as a right `A`-module, so the bimodule resolution splits over `A`.
  - `A^e ⊗_A M ≅ (A ⊗ K) ⊗_K M` is free.
- *Independent cross-check, which removes the one unverified theorem number in the route.* For a Leavitt path
  algebra over a commutative ring `R`, `gl.dim L_R(E) = gl.dim R + 1` when `E` has a cycle (arXiv:1605.03841,
  abstract).
  - So `gl.dim L_K(1,2) = 1` for every field `K`.
  - `L_k(1,2) ⊗_k K = L_K(1,2)`.
  - Therefore `uwd(L_k(1,2)) <= 1`, even without `leavitt-algebra-hochschild-dimension-at-most-one`.

## Adversarial checks (new here)

**T1. The base change is essential.** This check names the invariant.
- Let `A = k(x) ⊗_k k(y)`. It is the localization of `k[x, y]` at `(k[x]∖0)(k[y]∖0)`.
  - Every maximal ideal of `k[x, y]` meets `k[x]∖0`, so only primes of height `<= 1` survive.
  - Hence `A` is a regular Noetherian domain of dimension 1, so it is hereditary.
  - Yet `x ⊗ 1` and `1 ⊗ y` form a commuting independent pair.
- So "w.gl.dim `A <= n` implies commuting rank `<= n`" is **false**.
- The reviewed bound survives this example. In `A ⊗ k(y_1, y_2)` the prime `(x − y_1, y − y_2)` misses all three
  multiplicative sets and has height 2, so `uwd(A) >= 2`. That is the value the bound requires.
- **Consequence.** Every earlier homological attempt that bounded the rank by a dimension of the host alone dies
  exactly here, unless it also assumed that the host is flat over the embedded polynomial ring. The two base
  changes differ as follows:
  - The w17 attempt on the target inverted `Σ = k[a, b]∖0` inside an overring of `A`. It died at universally
    singular elements.
  - The w18 route inverts `Σ` only in the coefficient field `K`, through the graph `a_i ↦ y_i`. Zero divisors of
    `A` therefore never need to be inverted.
  - This is the single step that turns the 18 dead linear-characteristic attempts into a proof.

**T2. The bound concerns algebras, not unit groups.** Thompson's `V` sits in `U(L_2)` as permutation units and
contains `Z^n` for every `n`. So `Z^n` embeds in `U(L_2)` for all `n`, while `k[Z^n] → L_2` has a kernel for every
`n >= 2`.
- Explicit kernel element: `(g − 1)(h − 1)` for `g, h ∈ V` with disjoint supports.
- Consistency check: `h − 1 = p_W (h − 1)` where `p_W` is the support projection of `h`, and `(g − 1) p_W = 0`.
- So claims about group embeddings into units are untouched, for example
  `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`.

**T3. The bound is sharp.**
- `k[Z^m] ⊆ LC(X) ⋊ Z^m` through the canonical units, so `s = cd` is attained for `Z^m`.
- For `F_d` the bound is `s = 1`, attained by any `u_g`.
- No slack remains in the host bound.

## Consequences

1. **(E) is false.** `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` is refuted, because
   `F_2[Z^4] ⊇ F_2[x_1, …, x_4]` and `uwd(B_Ω ⊗ L_∂) <= 3`.
   - The route `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts` cannot close as stated.
   - When the w18 files land, the target should get `refuted_by: [f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts]`.
     That id is not present in this worktree, whose base predates the w18 commit. So it is recorded here and in
     the target's Attempts instead of in its frontmatter.
2. **Ara–Cortiñas Question 5.7 (arXiv:1108.0352v3: "Is there a unital homomorphism L_2 ⊗ L_2 → L_2?") has
   answer NO, over every field `k`.**
   - `x_1` is transcendental in `L_2`. Suppose `p(x_1) = 0` with `p` nonzero. Cancel powers using `y_1 x_1 = 1`
     to get `q(0) ≠ 0`. Then `x_1` is right invertible, hence invertible. But `x_1 y_1 ≠ 1`.
   - So `k[s, t] ≅ k[x_1] ⊗ k[x_1] ⊆ L_2 ⊗ L_2`.
   - `L_2` is central simple, so `L_2 ⊗ L_2` is simple, and a unital homomorphism from it is injective.
   - L1 together with `uwd(L_2) <= 1` then excludes it. The same argument excludes non-unital injective maps.
   - The literature has only the Brownlowe–Sørensen `*`-embedding obstruction over `Z`.
   - **This is a claimed answer to a published open problem. It needs a second referee with the
     "citation and hypothesis match" lens before anyone reports it outside the graph.**
3. **Nodes that become established when the chain lands:**
   - `leavitt-algebras-contain-no-two-variable-polynomial-ring`;
   - hence `leavitt-commuting-units-are-algebraically-dependent`, by the route
     `commuting-units-dependence-from-field-uniform-leavitt-rank` that the previous node's `distinct_from` names;
   - `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`.

   Mechanism (i) of the `Z^4` fork was the Q_2 firewall. It is now closed as a firewall, and it is closed
   negatively.
4. **What survives.** `decidable-group-algebras-have-fp-cantor-crossed-hosts` survives, but only with an acting
   group `P` that depends on `G`.
   - Any host `LC(X) ⋊ P` for `F_2[G]` needs `cd_(F_2) P >=` the commuting rank of `F_2[G]`. That rank is at
     least the largest rank of a free abelian subgroup of `G`.
   - So no single acting group of finite cohomological dimension hosts all decidable group algebras.
