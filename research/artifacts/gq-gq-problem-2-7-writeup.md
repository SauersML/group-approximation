# Problem 2.7 / Kourovka 14.10(c): write-up skeleton

Compiled by lane `gq-writeup` from the Cairn nodes on origin/main at `52b3743aa` (2026-09-17 23:47 local).
This is a skeleton for a write-up and makes **no claim beyond the nodes it cites**. Every statement below is
copied from, or is a direct consequence of, the named node, and the proof sketches compress the proofs
recorded there. Commits that establish the answer: `168fb13a2`, `5ff74da95`, `52b3743aa`
(root `gl-n-q-explicit-natural-fp-overgroup`).

## 0. The problem

- **BBMZ survey**, arXiv:2306.16356v3, Problem 2.7: "For n >= 2, find an explicit and natural example of a
  finitely presented group that contains GL_n(Q)." The survey says this part of Bridson and de la Harpe's
  question "remains open".
- **Kourovka notebook**, 14.10(c), credited there to P. de la Harpe. It is open in the 21st issue
  (arXiv:1401.0300v46), verbatim: "Find an explicit and "natural" finitely presented group Γn and an embedding
  of GLn(ℚ) in Γn." Parts (a) and (b), about Q, are in the Archive (Belk–Hyde–Matucci 2022; Mikaelian 2005).
  Source record: `research/artifacts/gq-gq-transfer-consequences.md` §1.
- **Working reading of "natural"** (root node). Γ_n counts if it is described uniformly, as a group of
  transformations of a named space or a matrix or automorphism group over a named ring or group, and not by
  running an embedding algorithm on a presentation of GL_n(Q). The root leaves the verdict to experts.

## 1. Main results (as stated in the nodes)

**Theorem A** (route `gl-n-q-all-n-in-st-10-of-resolvent-ring`). Let `R_L` be the ring of §2. The Steinberg
group `Γ = St_10(R_L)` is finitely presented, and it contains `GL_n(Q)` for every `n >= 1`, through the matrix
inclusions `GL_n(Q) ≤ SL_(n+1)(Q) ≤ SL_(3k)(Q)` with `3k >= n+1`. The route also records that `Γ` has
property (T). It is not simple.

**Theorem A′** (route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`). For each `n >= 2`,
`Γ_n = St_(6n+7)(R_L)` is finitely presented and contains `GL_n(Q)` via `g ↦ diag(g, det(g)^(-1))`.

A further route at rank 4 is also on main: `gl-n-q-explicit-via-st-4-of-resolvent-ring`, through
`one-steinberg-group-contains-every-gl-n-q`. It needs Krstić–McCool at rank 4 and a cited centrality input
(arXiv:2004.08551v2). It is outside this skeleton except as noted in §8.

## 2. The ring R_L

    R_L = Z< s_1, s_2, t_1, t_2, N, A |
             t_i s_j = δ_ij,  s_1 t_1 + s_2 t_2 = 1,
             N s_1 = s_1 (N + 1),  N s_2 = 0,  A (N+1) = 1 = (N+1) A >

It has 6 generators and 9 relations.

**Theorem B** (`leavitt-resolvent-ring-is-fp-and-contains-q`; route `-proof`, `requires: []`). `R_L` is
finitely presented and nonzero. Every integer `m >= 1` is a unit, so `Q ⊆ Z(R_L)` unitally. And
`(s_1, s_2, t_1, t_2)` is a Leavitt pair.

*Proof sketch.*
- Induction gives `N s_1^k = s_1^k (N+k)`. With `X = s_1^(m-1) s_2` and `N s_2 = 0`, this yields
  `(N+1)X = mX`. So `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`.
- `R_L ≠ 0`, by the module `Q^(X)` over the tail class `X` of `2^∞`:
  - `s_i` prepends the letter `i`, and `t_i` deletes a leading `i`;
  - `N` multiplies by the number of leading 1's, and `A = (N+1)^(-1)`.
- Checked by `gq-referee-b`. This part was split off at the referee's request (amendment A2), so the
  Problem 2.7 routes do not depend on simplicity.

**Theorem C** (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`; route
`leavitt-resolvent-ring-is-fp-simple-of-char-zero-proof`). `R_L` is simple. `R_L ≅ M_n(R_L)` for every
`n >= 1`. And `GL_n(Q)` lies in `[R_L^x, R_L^x]`.

Refereed **PASS** three times:
- `gq-referee-a`, proof gaps, 8f4edc918;
- `gq-referee-b`, citations and hypotheses, dfd8468b9;
- `gq-referee-c`, an independent proof avoiding the completion criterion, f7c7c3e04.

*Proof sketch.*
- Identify `R_L` with the Leavitt–Nekrashevych completion `O_ψ` over
  `B = Q[N][(N+c)^(-1) : c >= 1]`, with `ψ(f) = diag(f(N+1), f(0))`. The shifted resolvents
  `A_c = t_1 A_(c-1) s_1` invert `N + c`.
- ψ-minimality: `b ∈ I` forces `b(k) ∈ I` for all `k >= 0`, and a nonzero rational function has only finitely
  many zeros.
- Aperiodicity: `ψ_u(b) = b(a)` for `u = 1^a 2 x`.
- Then apply `leavitt-nekrashevych-completion-simplicity-criterion`. That criterion node is an unrefereed lane
  proof. Referee b checked the parts used, and referee c's proof does not use it.

Simplicity is **not** an input of Theorems A and A′.

## 3. Steinberg embedding lemmas

**Lemma D** (`leavitt-pairs-embed-sl-n-q-in-steinberg-groups`). Let `S` be a unital ring with `Q ⊆ S` unital
and a Leavitt pair `x_i, y_i`, and let `N >= 3`. Then `St_N(Q) → St_(6N+1)(S)`, induced by the index shift
`i ↦ N+i`, has kernel exactly `K_2(N,Q)`. So `SL_N(Q) ≤ St_(6N+1)(S)` and `GL_n(Q) ≤ St_(6n+7)(S)`.

Refereed **PASS** by `gq-referee-a` (fbbb1c736), `gq-referee-b` (2547e90a5; the route PASS was conditional on
A1 and A2, both since applied) and `gq-referee-c` (4529c10a3, a re-derivation).

*Proof sketch* (steps (a)–(f) of the node):
- **(a) Room lemma.** The image of `K_2(k,S)` in `St_k′(S)` is central for `k < k′`.
- **(b) Doubling.** `ψ(r) = (y_s r x_t)` and block expansion give `Φ : St_N(S) → St_2N(S)` with
  `Φ(ι y) = ι(ŝ(y) ŝ_τ(y))` on `St_N(Q)`.
- **(c) Square swap.** `W = [[𝒴,0],[0,𝒳]]` conjugates `diag(A, I_2N)` to `diag(𝒴A𝒳, I_N)`, and
  `diag(W, W^(-1)) ∈ E_6N(S)` by Whitehead's lemma.
- **(d) Two lifts agree.** Two lifts from the perfect group `St_N(S)` differ by a central homomorphism, so they
  agree in rank `6N+1`.
- **(e) Swindle.** `z = z · ŝ_τ(z)`, so `ŝ_τ(ιz) = 1`.
- **(f) Conclusion.** Injectivity modulo `K_2` comes from `Q → S`, and `E_N(Q) = SL_N(Q)`.

**Lemma E** (`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`; route `-proof`, which requires Lemma D).
1. If `A ⊆ S` is a unital subring commuting with the Leavitt pair and `N >= 3`, then `E_N(A)` embeds in
   `St_(3N+1)(S)`.
2. If `Q ⊆ S`, then `SL_(3k)(Q) ≤ St_10(S)` for every `k >= 1`, so every `GL_n(Q)` lies in the one group
   `St_10(S)`.

Refereed **PASS** by `gq-referee-a` (d45def137) and `gq-referee-b` (f60c835bf).

*Proof sketch.*
- **Change 1: `W` is elementary.** `U_2 U_1 W U_3 = [[0,-I_2N],[I_N,0]]`, which is in `E_3N(Z)`: it is an even
  permutation with `2N` minus signs. So step (d) runs with `M = 3N`.
- **Change 2: coefficients.** `ψ(a) = a I_2` for `a` commuting with the pair.
- **Part 2.** `M_k(S) ≅ S` via `θ_k(B) = R_k B C_k`. Apply part 1 to `(M_k(S), M_k(Q))` with `N = 3`, and use
  `E_3(M_k(Q)) = SL_(3k)(Q)`.

## 4. Finite presentation

**Theorem F** (`steinberg-finite-presentation-and-kazhdan-theorem`, a literature import). For a finitely
presented unital ring `R` and `n >= 4`, `St_n(R)` is finitely presented (Krstić–McCool, JPAA 141 (1999),
Theorem 3). The node also records property (T).
- The primary text is paywalled and unread. Three witnesses quote the theorem:
  - Ershov–Jaikin-Zapirain, arXiv:0809.4095v2;
  - Khanh, arXiv:2609.08428v1;
  - W. van der Kallen's review Zbl 0930.19001: "If n≥4 and R is a finitely presentable ring, then St_n(R) is
    finitely presentable".
- Records: `research/artifacts/gq-gq-lit-arxiv-krstic-mccool.md`,
  `research/artifacts/gq-steinberg-q-krstic-mccool-source.md`.

**Theorem F′** (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`; route `-proof`). For finitely presented
`R = Z<g_1..g_d | ρ_1..ρ_l>` and `n >= 5`, `St_n(R)` has the explicit presentation below.
- Generators: `y_ij(u)`, `u ∈ {1, g_1, ..., g_d}`.
- (B1): `[y_ij(u), y_kl(v)] = 1` for `j ≠ k`, `i ≠ l`.
- (B2): `[y_ij(1),y_jk(1)] = y_ik(1)`, `[y_ij(g),y_jk(1)] = y_ik(g)`, `[y_ij(1),y_jk(g)] = y_ik(g)`.
- One relator `x_12(ρ_t)` per ring relator, written through iterated commutators.

The proof is by `gq-referee-c` (artifact §2, cbe944ed7). It was checked by `gq-referee-b` against Milnor §5
(PASS, 95b06dff9) and by `gq-referee-a` (PASS, ee9131eef). The node calls it standard and claims no novelty.
Rank 5 is where the proof needs a free fifth index.

**Lemma G** (`st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`). For `n >= 4`,
`St_n(F/I) = St_n(F)/⟨⟨x_12(ρ_1), …, x_12(ρ_l)⟩⟩` when `I = (ρ_1, …, ρ_l)`.
- Proof: commutators with free indices spread `x_12(ρ)` over all index pairs, then over `aρb`.
- Checked by `gq-referee-b` (f60c835bf, noting it works already for `n >= 3`) and `gq-referee-c` (§4).

**The presentation of St_10(R_L).** By Theorem F′ with `d = 6`: generators `y_ij(u)`, `i ≠ j` in `[10]`,
`u ∈ {1, s_1, s_2, t_1, t_2, N, A}`, so 90·7 = 630 generators; relations (B1) and (B2); and the nine words of
route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`. With `c(a,b) = [x_13(a), x_32(b)] = x_12(ab)`,
those words are:
- `c(t_1,s_1) x_12(-1)`, `c(t_1,s_2)`, `c(t_2,s_1)`, `c(t_2,s_2) x_12(-1)`;
- `c(s_1,t_1) c(s_2,t_2) x_12(-1)`;
- `c(N,s_1) c(s_1,N)^(-1) x_12(-s_1)`, `c(N,s_2)`;
- `c(A,N) x_12(A) x_12(-1)`, `c(N,A) x_12(A) x_12(-1)`.

## 5. Assembly of Theorem A

1. Theorem B: `R_L` is finitely presented, with `Q ⊆ R_L` unital and a Leavitt pair.
2. Lemma E, part 2: every `GL_n(Q)` lies in `St_10(R_L)`.
3. `St_10(R_L)` is finitely presented. Rank 10 is at least 5, so Theorem F′ applies (citation-free), and so does
   Theorem F (Krstić–McCool).

For Theorem A′, replace step 2 by Lemma D with `N = n+1`. The rank is `6n+7`, at least 19.

## 6. Trust record

| Input | Node | Checks |
|---|---|---|
| R_L fp, Q ⊆ R_L, Leavitt pair | `leavitt-resolvent-ring-is-fp-and-contains-q` | referee b; direct computation |
| R_L simple (not needed for A, A′) | `leavitt-resolvent-ring-is-fp-simple-of-char-zero` | referees a, b, c PASS |
| SL_N(Q) ≤ St_(6N+1)(S) | `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` | referees a, b, c PASS |
| E_N(A) ≤ St_(3N+1)(S); all GL_n(Q) ≤ St_10(S) | `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` | referees a, b PASS |
| St_n(R) fp, n >= 5, explicit | `steinberg-groups-of-fp-rings-are-fp-in-rank-five` | proof by referee c; referees b, a PASS |
| St_n(R) fp, n >= 4 | `steinberg-finite-presentation-and-kazhdan-theorem` | import; primary unread; three witnesses |
| Quotient adds one relator per ideal generator | `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator` | referees b, c PASS |
| Property (T) of Γ (a side remark) | `steinberg-finite-presentation-and-kazhdan-theorem` | not re-checked (referee c); EJZ citation record |

## 7. Priority and framing (from the root and `research/artifacts/gq-gq-lit-arxiv-priority.md` §2, §7)

- **Existence is classical.** Higman's embedding theorem, applied to the Higman–Neumann–Neumann two-generator
  overgroup, puts GL_n(Q) in some finitely presented group (survey Corollary 2.4).
- **Kazhdan existence.** Chatterji–Kassabov, arXiv:2601.22907, Theorem 3, give a finitely presented Kazhdan
  overgroup that is normally generated by one element. It is not explicit.
- **Explicit, announced.** Mikaelian, arXiv:2507.04347v8 §1.4, *announces* an explicit, even 2-generator,
  finitely presented Γ_n ⊇ GL(n,Q) obtained by running his explicit Higman algorithm. No construction is given,
  and his ref. [41] was not found on arXiv on 2026-09-17.
- **Nearest unstable K_2 result.** Khanh, arXiv:2609.08428v1, Thm 5.4: `St_r(L_(F_2)(1,2)) ≅ GL_r` for
  `r >= 3`. His Lemma 5.2 is the analogue of the room lemma. Stable vanishing is Ara–Brustenga–Cortiñas,
  arXiv:0903.0056.
- **What the nodes claim as the contribution.** An explicit construction of matrix type, uniform in n (one
  group St_10(R_L)), over a ring with a 9-relation presentation; and the explicit finite-rank unstable swindle
  (Lemmas D, E).
  - Credit risk: the doubling trick is the standard K-triviality argument for properly infinite rings.
  - The literature search was bounded, with no MathSciNet.
  - `R_L` may be folklore among algebraic Cuntz–Pimsner rings (Carlsen–Ortega).

## 8. Open points recorded in, or visible from, the nodes

- **"Natural"** is left to experts (root). `R_L` is described as the Leavitt–Nekrashevych completion of the
  resolvent algebra `Q[N][(N+c)^(-1)]`.
- **Γ is not simple.** It maps onto `E_10(R_L)`. The simple-host question `gl-n-q-embeds-in-fp-simple-group`
  stays OPEN. The natural simple candidate `[R_L^x,R_L^x]/Z` is not finitely presented
  (`leavitt-resolvent-derived-units-mod-centre-not-fp`, ESTABLISHED).
- **Graph wiring.** Both routes `requires` the Krstić–McCool import node
  `steinberg-finite-presentation-and-kazhdan-theorem`, not `steinberg-groups-of-fp-rings-are-fp-in-rank-five`.
  So in Cairn's fixpoint the ESTABLISHED status still flows through the import. Only the prose (root, commit
  52b3743aa) says the answer no longer rests on the unread paper.
- **Stale prose.**
  - Both routes still say the presentation is explicit "only relative to Krstić–McCool's presentation … not
    written out". That text predates Theorem F′, which gives the presentation explicitly.
  - `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator` still says "not independently reviewed",
    although referees b and c passed it.
- **Property (T)** of Γ is not re-checked, and it is not needed for Problem 2.7.
- **The rank-4 route** (`St_4(R_L)`) depends on Krstić–McCool at rank 4, which has no direct proof here
  (referee c §3), and on the centrality input of arXiv:2004.08551v2.

## 9. What an expert should check

1. The nine relations of `R_L` and the identity `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`. Nonvanishing via the
   tail-class module (Theorem B).
2. Room lemma (a) for noncommutative `S`: the column and row groups and the conjugation action through `π_k`.
3. Block expansion `β : St_N(M_2(S)) → St_2N(S)` respects (R2). Also that `Φ(ι y) = ι(ŝ(y) ŝ_τ(y))` uses only
   that `Q`, or `A` in Lemma E, commutes with the pair.
4. The elementary factorization `U_2 U_1 W U_3 = [[0,-I_2N],[I_N,0]]`, and its membership in `E_3N(Z)`.
5. Step (d): the two lifts differ by a homomorphism into a central subgroup, and `St_N(S)` is perfect for
   `N >= 3`.
6. `M_k(S) ≅ S` via the pair, and `E_3(M_k(Q)) = SL_(3k)(Q)`.
7. The direct finite presentation of `St_n(F)` for free `F` and `n >= 5`: independence of the iterated
   commutators from splittings and intermediate indices, and the fifth-index step. Then Lemma G.
8. The nine relator words of §4 against the nine ring relations.
9. Whether `St_10(R_L)` meets the problem's intent. That covers "explicit" (a presentation with 630 generators)
   and "natural" (a Steinberg group over a named ring). Also whether `R_L`, or the construction, is already in
   the Leavitt path, Cuntz–Pimsner or K-theory literature.
