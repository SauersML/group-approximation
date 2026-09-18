# Referee report (citation/hypothesis lens): gq-referee-c's direct proof that `St_n(R)` is finitely presented, `n >= 5`

Referee: lane gq-referee-b, 2026-09-17.
- **Reviewed:** §2–§5 of `research/artifacts/gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md`
  (5d6390c47).
- **Role:** it is now the independent backing for `steinberg-finite-presentation-and-kazhdan-theorem` at rank
  `>= 5`, and so for the Problem 2.7 root (168fb13a2).

## Verdict

**PASS.** For every finitely presented unital associative ring `R` and every `n >= 5`, `St_n(R)` is finitely
presented, with the explicit presentation of §2 plus the relators of §4. The proof uses only the defining relations
(R1)–(R3). There is nothing to cite beyond the definition of the Steinberg group.

## Against Milnor

The Steinberg group is as in Milnor, *Introduction to algebraic K-theory*, §5: generators `x_ij(r)`, `i ≠ j`, and
relations
- `x_ij(r)x_ij(s) = x_ij(r+s)`;
- `[x_ij(r), x_jl(s)] = x_il(rs)` for `i ≠ l`;
- `[x_ij(r), x_kl(s)] = 1` for `j ≠ k`, `i ≠ l`.

The report's (R1)–(R3) are exactly these, with `[a,b] = aba^{-1}b^{-1}`, the convention under which (R2) reads as
stated. Milnor states the standard relations for any associative ring. Noncommutativity enters only through the
order of `rs` in (R2), and §2 respects it (`X_ik(ab)` with `a` on the left).

## Line-by-line checks

- **Identity (★).** `x[y,z]x^{-1} = [uy, z]` (using `[x,z] = 1` and `xyx^{-1} = uy`). Then
  `[uy,z] = u[y,z]u^{-1}[u,z]`, which I expanded and checked. `u` commutes with `[y,z]`. `[y,z]` commutes with `u`
  and `z`, hence with `[u,z]`. **Correct.**
- **H(1).** It is exactly (B1) and (B2). The (R2) pairs with `|m| + |m'| <= 1` are `(1,1)`, `(g,1)` and `(1,g)`.
- **(i) Independence of the middle index `k`.** Each hypothesis of (★) is an instance of H(L):
  - `[y,z] = X_kj(b)`;
  - `[x,z] = 1` since `k ≠ k'`;
  - `u = X_ik'(a)`;
  - the commutations of `X_kj(b)` with `X_ik'(a)` and with `X_k'j(b)`.
  - It needs four indices.
- **(ii) Independence of the split.** Compare `(a,b)` with `(ac, b')`, where `b = cb'` and `|b'| >= 1`:
  - `|ac| <= L` because `|b'| >= 1`, so `u = X_il(ac)` is an H(L) instance;
  - any two splits are related by one such move;
  - then (i). **Correct.**
- **(iii) The (R3)-type commutation at length `L+1`.**
  - For index pairs `(i,j)`, `(k,l)` with `j ≠ k` and `i ≠ l`, choose `p ∉ {i,j,k,l}`. This is where `n >= 5`
    is needed.
  - `X_kl(m')` commutes with `X_ip(a)` and `X_pj(b)`: the conditions `l ≠ i`, `k ≠ p`, `l ≠ p` and `k ≠ j` all
    hold.
  - Both lengths `L+1`: use the first case twice. The second application needs `p' ∉ {i,j,k,p}`, and `l` qualifies
    when the four indices are distinct. Otherwise there are more free indices.
  - The case `(k,l) = (i,j)` is included. **Correct.**
- **(iv) The (R2)-type identity at length `L+1`.** Both boundary cases, `m' = 1` and `m = 1`, reduce by (★) to the
  definition. The needed commutations come from (iii) at level `L+1`, which is proved before (iv). **Correct.**
- **Conclusion.**
  - `φ` is well defined because monomials form a `Z`-basis of the free ring.
  - (R1) holds because `X_ij(m)` and `X_ij(m')` commute (the case `(k,l) = (i,j)` of (iii)).
  - (R2) is bilinear: commutators land in `X_ik(·)`, which is central in `⟨X_ij(·), X_jk(·)⟩` by (R3).
  - `ψφ = id` and `φψ = id`. **Correct.**
- **§4 quotient step.** Correct. I also passed it in `gq-referee-b-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md`.
- **§3, why the argument stops at `n = 4`.** This is consistent with the rank-4 case needing Krstić–McCool, whose
  primary text is still unread. `St_3` fails already for rings surjecting onto `F[t]`.
- **§5, rank 5.** In `one-steinberg-group-contains-every-gl-n-q` it needs:
  - centrality of `K_2(5, M_k(Q))`: Voronetsky's quote with `5 >= sr+2 = 3`;
  - central closure of `St_{5k}(Q)`: Voronetsky's quote with `5k >= 5`.
  - I verified both quotes at arXiv:2004.08551v2 (see `gq-referee-b-one-steinberg-group-contains-every-gl-n-q.md`).
  - `St_5(R_L)` or `St_5(D)` is therefore one finitely presented group containing every `GL_n(Q)`, with no
    Krstić–McCool input.

## Novelty remark (not a verdict item)

That `St_n(Z⟨X⟩)` is finitely presented for `n` large is folklore-level: this relator-bootstrap is how finite
presentations of Steinberg groups are usually proved. Credit it as "standard argument, written out", not as new.
