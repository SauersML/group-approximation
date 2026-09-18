# Referee report (citation/hypothesis lens): `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` and route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`

Referee: lane gq-referee-b, 2026-09-17. Reviewed as landed at b9dd69f0a:
- the claim and its Attempts 1 proof, parts (a)–(f);
- the route to `gl-n-q-explicit-natural-fp-overgroup` (Problem 2.7);
- the imports it uses: `steinberg-finite-presentation-and-kazhdan-theorem` and part 1 of
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero`.

This result would answer a named problem, so RULES §5 asks for two referees; this is one of them.

## Verdict

- **Lemma: PASS.** Its proof cites nothing beyond the Steinberg relations and Whitehead's lemma. I checked every
  step myself (below).
- **Route: PASS, conditional on amendments A1 and A2.** A3 is wording only.
  - With A1 and A2, `St_(6n+7)(R_L)` is a finitely presented group containing `GL_n(Q)`, for every `n >= 2`.
  - That depends only on:
    - the lemma;
    - Krstić–McCool's theorem (primary not read; transcription quoted below);
    - a direct computation from the nine relations of `R_L` plus an explicit nonzero module.
  - It does **not** depend on the simplicity of `R_L`.

## The lemma, step by step

- **(a) Room lemma. Correct for noncommutative `S`.**
  - Conjugation by `x_ij(s)` sends `x_jb(v)` to `x_ib(sv) x_jb(v)` and fixes `x_cb(v)` for `c ≠ j`. So `St_k`
    acts on the column group `≅ S^k` by left multiplication through `π_k`.
  - It sends `x_bi(v)` to `x_bi(v) x_bj(−vs)`, that is, right multiplication by `π_k(y)^{-1}` on rows.
  - The action is a homomorphism agreeing with `π_k` on generators. So `K_2(k,S)` centralizes the row and
    column groups, and it commutes with `x_bb'` by (R3).
  - `x_cd(r) = [x_cb(r), x_bd(1)]` covers the remaining generators.
- **(b) The doubling map.**
  - `ψ(r)ψ(r')_{su} = y_s r (Σ_t x_t y_t) r' x_u = y_s rr' x_u`, and `ψ(1) = (y_s x_t) = I`.
  - Block expansion `β`:
    - its factors commute, because `(j,t) ≠ (i,s')` and `(i,s) ≠ (j,t')` when `i ≠ j`;
    - (R1) and (R3) follow;
    - for (R2), the only nontrivial commutators of factors are `x_{(i,s),(l,u)}(a_st b_tu)`, and they commute
      with all factors, so `[∏X, ∏Y] = ∏[X,Y]` is the product for `x_il(ab)`. The noncommutative order
      `a_st b_tu` is the matrix product.
  - `𝒴𝒳 = I_2N` and `𝒳𝒴 = I_N`.
  - `π(Φ(x_ij(r))) = 𝒴 π(x_ij(r)) 𝒳`, which is multiplicative because `𝒳𝒴 = I`.
  - `Q` is central in `S`: `Z` is central, and the inverse of a central unit is central. So `ψ(q) = qI_2`.
  - `y ↦ ŝ(y)ŝ_τ(y)` is a homomorphism, because the two images commute elementwise by (R3).
- **(c) The square swap.**
  - `W W^{-1}` and `W^{-1} W` are the identity blockwise.
  - `W diag(A, I_2N) W^{-1} = diag(𝒴A𝒳, I_N)`.
  - The Whitehead factorization `diag(W,W^{-1}) = u(W) l(−W^{-1}) u(W) · u(−I) l(I) u(−I)` checked by
    multiplying out: `[[0,W],[−W^{-1},0]] · [[0,−I],[I,0]]`. It holds over any ring.
- **(d)**
  - `π_M(e(y)) = D diag(π(y), I_5N) D^{-1} · diag(𝒴π(y)𝒳, I_4N)^{-1} = I`.
  - `c(y)` is central in `St_{M+1}` by (a).
  - `c(yy') = c(y')c(y)`, so `c` is a homomorphism to an abelian group.
  - `St_N(S)` is perfect for `N >= 3`, so `c = 1`.
- **(e), (f) Correct.**
  - The swindle gives `ŝ_τ(ιz) = 1`.
  - The kernel is exactly `K_2(N,Q)`, because `Q → S` is an injective unital map and `E_N(Q) = SL_N(Q)`.
  - `GL_n(Q) ↪ SL_{n+1}(Q)` gives rank `6(n+1)+1 = 6n+7`.

## Import 1: `St_m(R)` is finitely presented for finitely presented noncommutative `R`, `m >= 4`

The repo node `steinberg-finite-presentation-and-kazhdan-theorem` **cites no source** in its body.

**Source found (secondary transcription; primary not read).** Huynh Viet Khanh, *General linear and Steinberg
groups over the Leavitt algebra L_{F_2}(1,2)*, arXiv:2609.08428v1, Theorem 6.1, read in arXiv HTML:
- "Krstić–McCool [10, Theorem 3] prove that St_n(B) is finitely presented for every finitely presented
  associative unital ℤ-algebra B and every n≥4."
- The same proof: "Their definition of a finitely presented ring is a quotient of a free associative unital
  ℤ-algebra on finitely many generators by a finitely generated two-sided ideal."
- [10]: S. Krstić and J. McCool, *Presenting GL_n(k⟨T⟩)*, J. Pure Appl. Algebra 141 (1999), no. 2, 175–183.
- I did not read the primary; it was unreachable.

**Hypothesis match.** `R_L = Z⟨s_1,s_2,t_1,t_2,N,A⟩` modulo nine relations is exactly a finitely presented
associative unital `ℤ`-algebra in that sense, and `6n+7 >= 19 >= 4`. It matches.

**Property (T) (not needed for Problem 2.7).** Ershov–Jaikin-Zapirain, arXiv:0809.4095v2 (Invent. Math. 179
(2010)), read in arXiv HTML:
- Theorem 1.1: "Let R be a finitely generated (associative) ring with 1 and n≥3. … Then G has Kazhdan's property
  (T)."
- "In fact, we prove property (T) for an even larger group St_n(R)."
- `R_L` is finitely generated, so `St_(6n+7)(R_L)` has (T). The node's `n >= 4` is stronger than needed.

**A1 (required).** Add these two citations to `steinberg-finite-presentation-and-kazhdan-theorem`, with Krstić–McCool
marked "via Khanh arXiv:2609.08428v1 Thm 6.1; primary not read".

## Import 2: part 1 of the ring node (`Q ⊆ R_L` unitally, with a Leavitt pair)

Checked directly from the relations.
- `(N+c)s_1 = s_1(N+c+1)` and `(N+m)s_2 = m s_2`.
- So `u_m · m = t_2 t_1^{m-1} A (N+1) s_1^{m-1} s_2 = t_2 t_1^{m-1} s_1^{m-1} s_2 = 1`. Since `m` is central,
  every `m >= 1` is a unit and `Q → R_L` is a unital ring map.
- It is injective if `R_L ≠ 0`, because `Q` is a field. The node's explicit model on `Q^(X)`, with `X` the tail
  class of `2^∞`, satisfies all nine relations; I checked each. So `R_L ≠ 0`.
- `s_i, t_i` satisfy `t_i s_j = δ_ij` and `s_1t_1 + s_2t_2 = 1` by definition.

None of this uses the simplicity criterion.

**A2 (required, structural).** The route `requires` the whole node `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
including simplicity. Simplicity rests on a criterion node under separate review.
- Split part 1 into its own claim: "`R_L` is a finitely presented ring containing `Q` unitally and a binary
  Leavitt pair".
- Its direct proof is the `u_m` computation plus the model.
- Make the route require that claim instead. Then Problem 2.7 no longer depends on the simplicity review.

## A3 (wording): "explicit and natural"

- **Explicit.** `R_L` is explicit, and so is the rank `6n+7`.
- **Presentation not written.** The finite presentation of `St_(6n+7)(R_L)` comes from Krstić–McCool's
  construction, and the route does not write it out. Say so in the route, and write a presentation later if
  possible.
- **"Natural" is the askers' judgement.** Suggest the route say the group answers Problem 2.7 "in the sense that
  it is the Steinberg group of an explicitly presented ring, not the output of a Higman embedding".
- **Related work to cite.** Khanh 2609.08428 studies `St_n` and `GL_n` over `L_{F_2}(1,2)`, which is close in
  technique. Ask `gq-lit-arxiv` for a priority check of "finitely presented group containing `GL_n(Q)`"
  against 2025–26 papers, and in particular against Khanh's.

## Not reviewed here

- The simplicity of `R_L` (parts 2–3 of the ring node): separate report.
- Novelty.
