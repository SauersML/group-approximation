---
rg: 2
id: self-similar-higman-krull-dimension-two-review
kind: claim
title: Referee review of ed3dbbb573 — Lemma 1 (conjugation in Aut(T_d) preserves level profiles) and its exclusion of Lysenok-type deepening substitutions are correct, the Kochloukova–Sidki and Kochloukova–Luiz citations check at source, and one-counter reachability is standard; repairs are needed on C_p wr Z^2 (degree p^2, due to Dantas–Sidki, not p+1), the Kochloukova–Luiz hypothesis list, and an overstated lesson
distinct_from:
  self-similar-higman-routes-meet-krull-dimension-two: that is the lane attempt record under review; this checks its lemma, its citations and its recalled claims.
  finite-recursion-depth-bound-review: that reviews the depth-bound node e6f7e2b3d7; this reviews the HNN and Nekrashevych routes in ed3dbbb573.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane attempt record ed3dbbb573 by bh-gate1-abstract).**
Verdict: **PASS with repairs.** The target `fp-self-similar-groups-with-arbitrarily-hard-word-problem` stays
OPEN, and the node correctly calls itself an attempt record.

Read at source:
- Kochloukova–Luiz, *Non self-similar metabelian groups*, arXiv:2509.05798 (abstract, main theorem, and their
  quotation of Kochloukova–Sidki 2020), from the arXiv HTML.
- Dantas–Sidki, *On state-closed representations of restricted wreath product of groups of type
  G_{p,d} = C_p wr C^d*, arXiv:1505.05165 (J. Algebra 2018), abstract.
- Kharlampovich–Myasnikov–Sapir, arXiv:1204.6506, abstract.

## Verdicts

| item | verdict |
|---|---|
| Route 1: `V_d(G)` is not residually finite and not a structure group | **PASS** |
| Route 1: reduction to (O4) of `decidable-residually-wd-groups-embed-in-lift-presented-hosts` | **PASS** (a reduction, as stated) |
| Lemma 1 (level profiles) | **PASS** |
| Lysenok's `σ` is not induced by conjugation in `Aut(T_d)` | **PASS** |
| Krull dimension 1 is self-similar (Kochloukova–Sidki, as quoted by K–L) | **PASS**; the quotation is complete, with no ellipsis |
| Baumslag's group meets those hypotheses | **PASS** |
| one-counter reachability is easy (*recalled*) | **PASS** as a standard result, cited below |
| "two counters ⇒ Krull dimension ≥ 2" (*heuristic*) | **PASS for the top factor**, which is already computed on main; heuristic for the configuration module |
| Kochloukova–Luiz hypotheses | **incomplete**: two of four hypotheses omitted |
| `C_p ≀ Z^2` self-similar "of degree `p + 1`", credited to Dantas–Santos–Sidki | **wrong degree and attribution**: degree `p^2`, Dantas–Sidki |
| Lesson: Krull dimension 2 "is exactly where fp metabelian self-similarity is known to fail in char 0" | **overstated** |

## Checks

**Route 1.** `V_d(G) ⊇ V_d`, and `V_d` has an infinite simple subgroup of index at most 2, so `V_d(G)` is not
residually finite. The PSPACE cap for finite-state `G` is item 4 of the target node, and (O4) is line-for-line the
lift-presented step of `decidable-residually-wd-groups-embed-in-lift-presented-hosts`. No new claim; correct.

**Lemma 1.** The level-`k` quotient `π_k : Aut(T_d) → Sym(level k)` is a homomorphism, so
`π_k(t^(-1) g t) = π_k(t)^(-1) π_k(g) π_k(t)`. That is conjugate to `π_k(g)`, and `g ∈ St(k) ⟺ ψ(g) ∈ St(k)`.
Correct and complete.

**Lysenok.** `σ(a) = aca`, and its level-1 permutation is `(swap)(id)(swap) = id`, while `a` swaps level 1. So no
`t ∈ Aut(T_2)` realizes `σ` by conjugation. Scope, which the node states correctly: this excludes only
conjugation extending the *given* action. An HNN overgroup could still act on a different tree, or through prefix
maps that are not tree automorphisms, but then it is not self-similar in the given tree.

**Krull dimension 1.** Kochloukova–Luiz write, verbatim: "In [18] Kochloukova and Sidki showed that for G=A⋊Q
where A is viewed as ℤQ-module via conjugation, if the Krull dimension of A as ℤQ-module is 1 and the centralizer
C_Q(A)={q∈Q | [q,A]=1} is trivial then G is transitive self-similar."
- The node's quotation, and its ellipsis, lose nothing. The hypotheses are exactly Krull dimension 1 and trivial
  centralizer; finite presentation is not among them as quoted.
- **Baumslag's group.** `A = F_2[x^(±1), (1+x)^(-1)]` is a localization of `F_2[x]`, so Krull dimension 1.
  `x^a (1+x)^b = 1` in `F_2(x)` forces `a = b = 0`, since `x` and `1 + x` are distinct primes, so the centralizer
  is trivial. The node's application is correct.

**Kochloukova–Luiz, Main Theorem, verbatim hypotheses.**
- `G = A ⋊ Q` with `A`, `Q` abelian and `Q ≅ ℤ^s`, `s ≥ 2`.
- (1) "A is a cyclic ℤQ-module, say A≃ℤQ/I, A is a ℤ-torsion-free integral domain and Krulldim(A)=2".
- (2) "for every prime number p the ring A/pA is an infinite integral domain".
- (3) "the image of a non-trivial element of Q in the field of fractions of A is not algebraic over ℚ. In
  particular C_Q(A)=1_Q".
- (4) "G is finitely presented".
- Conclusion: "Then G is not a self-similar group."

The node lists only the torsion-free and `A/pA` conditions. **Repair:** list all four, including cyclicity and the
transcendence condition (3).

**One-counter reachability (*recalled*).** A one-counter automaton, meaning a pushdown automaton with a single
stack symbol and a zero test, has NL-complete reachability for unary updates (Lafourcade–Lugiez–Treinen 2004, as
stated in the counter-automata literature). Nonempty ones accept a word of length `O(n^2)` (arXiv:1510.05460,
abstract). I did not read Lafourcade–Lugiez–Treinen itself. Two counters are Turing complete (Minsky 1967). So
the node's inference, that a hard KMS-type encoding needs `K ≥ 2` counters, is sound as a heuristic about the
encoding. **Repair:** replace *recalled* by these citations.

**Two counters ⇒ Krull dimension ≥ 2.**
- For the **top factor** the dimension is already computed on main. `two-counter-kms-top-has-no-affine-self-similar-action`
  sets `R_K = F_p[s_i^(±1), (1 − s_i)^(-1) : i ≤ K]`, a localization of `F_p[s_1, …, s_K]`, so Krull dimension `K`.
  **Repair:** cite this; it upgrades the heuristic for `B_0 = R_K ⋊ U_K`.
- For the configuration module the claim stays a heuristic, as the node says. A basis indexed by counter values
  bounds nothing until the action of the counter letters is written out.
- **Caveat on the comparison.** KMS groups are solvable of class 3 (KMS abstract), not metabelian. Neither
  subgroups nor quotients of self-similar groups need be self-similar, so Kochloukova–Luiz is only an *analogue*
  for them. (KD2_p) says "analogue", which is correct.

**`C_p ≀ Z^2`.** Dantas–Sidki (arXiv:1505.05165) prove, in their abstract: "for d ≥ 2 there are no fsc
representations of G_{p,d} on the p-adic tree", the degree of any faithful state-closed representation must be
composite, and "for d ≥ 2, we construct uniformly fsc representations of G_{p,d} on the p^{2}-adic tree".
**Repair:**
- Replace "of degree `p + 1`, Dantas–Santos–Sidki" with "on the `p^2`-adic tree, Dantas–Sidki (arXiv:1505.05165)".
- Note that `C_p ≀ Z^2` is not finitely presented, so it is only a starting point for (KD2_p), as the gate-1 state
  artifact says.
- This affects the "first test (b)" in `research/artifacts/gq-bh-gate1-abstract-gate1-state.md` and in
  `two-counter-kms-groups-are-self-similar` if they repeat the degree.

**Lesson.** "That is exactly where finitely presented metabelian self-similarity is known to fail in
characteristic 0" is overstated. Kochloukova–Luiz give *sufficient conditions*, (1)–(4), for failure.
- `C_p ≀ Z^2` has Krull dimension 2 and is self-similar, though in characteristic `p` and not finitely presented.
- **Repair:** "that is where Kochloukova–Luiz give finitely presented metabelian examples, under their
  hypotheses (1)–(4), that are not self-similar".

## Bottom line

The obstruction map is right. Conjugation in `Aut(T_d)` cannot deepen, so only depth-preserving
Baumslag–Remeslennikov tricks remain; Krull dimension 1 is fine, and hardness pushes to dimension at least 2.
(KD2_p) is correctly posed. None of the repairs changes a conclusion, but the `C_p ≀ Z^2` degree should be fixed
before the (KD2_p) lane uses it.
