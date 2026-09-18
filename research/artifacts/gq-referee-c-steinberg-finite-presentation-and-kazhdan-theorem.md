# Referee report (gq-referee-c): steinberg-finite-presentation-and-kazhdan-theorem

- **Node:** `research/steinberg-finite-presentation-and-kazhdan-theorem.md`, with the citation route
  `steinberg-finiteness-kazhdan-citation`, the source record `gq-steinberg-q-krstic-mccool-source.md`, and the
  companion `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`.
- **Lens:** find the primary source. Where the source can't be read, prove the statement directly.

## Verdict

- **Finite presentation, n >= 5: PASS.** I give a self-contained proof (§2) for every finitely presented unital
  associative ring, commutative or not. It is elementary, uses only (R1)–(R3), and gives an explicit
  presentation.
  - **Credit:** this is the standard relator bootstrap, written out here. No novelty is claimed.
  - **Second check:** `gq-referee-b` independently checked §2 and passed it (95b06dff9,
    `gq-referee-b-steinberg-direct-finite-presentation.md`).
- **Finite presentation, n = 4: PASS as a literature import only.**
  - The statement is Krstić–McCool, *Presenting GL_n(k⟨T⟩)*, J. Pure Appl. Algebra 141 (1999) 175–183,
    Theorem 3.
  - Two independent secondary sources quote it verbatim with the same theorem number: Ershov–Jaikin-Zapirain
    arXiv:0809.4095v2, and Khanh arXiv:2609.08428v1.
  - The primary text is still unread. ScienceDirect is paywalled, and Semantic Scholar has no abstract.
  - My §2 argument does not reach `n = 4`; see §3.
- **Companion `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`: PASS** (§4).
- **Property (T): not re-checked.** It rests on the existing citation record (EJZ, arXiv:0809.4095v2, §6). It is
  not needed for Problem 2.7.
- **Consequences for the two Problem 2.7 routes.**
  - `St_(6n+7)(R_L)` has rank `>= 19`, so its finite presentation is now citation-free.
  - `St_4(D)` still needs Krstić–McCool. But `one-steinberg-group-contains-every-gl-n-q` works verbatim at rank
    5 (§5). So `St_5(D)` is one finitely presented group containing every `GL_n(Q)`, with no Krstić–McCool
    input.

## 1. Notation

- `F = Z⟨g_1, …, g_d⟩` is the free unital ring. Its additive basis is the monomials (words) `m`, with length
  `|m|`.
- `B = {1, g_1, …, g_d}` is the set of monomials of length `<= 1`.
- `St_n(A)` has generators `x_ij(r)` (`i ≠ j`) and relations:
  - (R1) `x_ij(r) x_ij(r') = x_ij(r+r')`;
  - (R2) `[x_ij(r), x_jk(s)] = x_ik(rs)` for distinct `i,j,k`;
  - (R3) `[x_ij(r), x_kl(s)] = 1` for `j ≠ k` and `i ≠ l`, which includes `(k,l) = (i,j)`.
- `[a,b] = aba^(-1)b^(-1)`.

**Identity (★).** Suppose `[x,z] = 1`, `u := [x,y]` commutes with `[y,z]`, and `[y,z]` commutes with `z`. Then
`[x,[y,z]] = [u,z]`.
- Proof: `x[y,z]x^(-1) = [uy, z] = u[y,z]u^(-1)[u,z] = [y,z][u,z]`.
- `[y,z]` commutes with `u` and `z`, hence with `[u,z]`. So `[x,[y,z]] = [y,z][u,z][y,z]^(-1) = [u,z]`.

## 2. Theorem: for n >= 5, St_n(F) is finitely presented

Let `G` have:
- generators `y_ij(u)`, `i ≠ j`, `u ∈ B`;
- relations:
  - (B1) `[y_ij(u), y_kl(v)] = 1` for `u, v ∈ B`, `j ≠ k` and `i ≠ l`;
  - (B2) `[y_ij(1), y_jk(1)] = y_ik(1)`, `[y_ij(g), y_jk(1)] = y_ik(g)` and `[y_ij(1), y_jk(g)] = y_ik(g)` for
    `g ∈ {g_a}` and distinct `i,j,k`.

**Claim.** For `n >= 5`, `y_ij(u) ↦ x_ij(u)` is an isomorphism `G ≅ St_n(F)`.

**Inductive definition.** Put `X_ij(u) = y_ij(u)` for `u ∈ B`. For `|m| >= 2`, put `X_ij(m) = [X_ik(a), X_kj(b)]`
for any split `m = ab` with `|a|, |b| >= 1` and any `k ∉ {i,j}`.

**H(L)** is the conjunction of:
- `X_ij(m)` is well defined for `|m| <= L`;
- (C/R3)_L: `[X_ij(m), X_kl(m')] = 1` for `|m|, |m'| <= L`, `j ≠ k`, `i ≠ l`;
- (R2)_L: `[X_ij(m), X_jk(m')] = X_ik(mm')` for `|m| + |m'| <= L`.

H(1) is (B1) together with (B2). We show H(L) ⇒ H(L+1) for `L >= 1`.

**(i) Independent of k.** Take a split `(a,b)` of a monomial of length `L+1`, and distinct `i, j, k, k'`.
- Apply (★) to `x = X_ik(a)`, `y = X_kk'(1)` and `z = X_k'j(b)`.
- The ingredients from H(L):
  - `[y,z] = X_kj(b)` (R2);
  - `[x,z] = 1` (`k ≠ k'`, `i ≠ j`);
  - `u = X_ik'(a)` (R2);
  - `u` commutes with `X_kj(b)`;
  - `X_kj(b)` commutes with `X_ik'(a)` and with `X_k'j(b)`.
- So `[X_ik(a), X_kj(b)] = [X_ik'(a), X_k'j(b)]`.

**(ii) Independent of the split.** Let `ab = (ac)b'` with `|c| >= 1`, and pick `l ∉ {i,k,j}`.
- `X_kj(cb') = [X_kl(c), X_lj(b')]` by (R2)_L.
- Apply (★) to `x = X_ik(a)`, `y = X_kl(c)` and `z = X_lj(b')`:
  - `[x,z] = 1`;
  - `u = X_il(ac)` by (R2)_L, since `|ac| <= L`;
  - `u` and `z` both commute with `X_kj(b)`.
- So `[X_ik(a), X_kj(cb')] = [X_il(ac), X_lj(b')]`, which equals `[X_ik(ac), X_kj(b')]` by (i).
- Steps (i) and (ii) need only four distinct indices.

**(iii) (C/R3)_(L+1).** This is where `n >= 5` is used.
- *One length is L+1.* Let `|m| = L+1` and `|m'| <= L`. Choose `p ∉ {i,j,k,l}` and write
  `X_ij(m) = [X_ip(a), X_pj(b)]`. `X_kl(m')` commutes with `X_ip(a)` (`l ≠ i`, `k ≠ p`) and with `X_pj(b)`
  (`l ≠ p`, `k ≠ j`), by H(L). Hence it commutes with `X_ij(m)`.
- *Both lengths are L+1.* Write `X_kl(m') = [X_kp(c), X_pl(e)]` with the same `p` and apply the first case twice.

**(iv) (R2)_(L+1).**
- If `|m|, |m'| >= 1`, this is the definition, which is independent of choices by (i) and (ii).
- If `m' = 1` and `m = ab`, choose `p ∉ {i,j,k}` and apply (★) to `x = X_ip(a)`, `y = X_pj(b)` and
  `z = X_jk(1)`:
  - `[y,z] = X_pk(b)`;
  - `[x,z] = 1`;
  - `u = X_ij(m)` commutes with `X_pk(b)`, by (iii);
  - `X_pk(b)` commutes with `X_jk(1)`.
  - Then `[X_ij(m), X_jk(1)] = [x,[y,z]] = [X_ip(a), X_pk(b)] = X_ik(m)`.
- The case `m = 1` is symmetric: take `x = X_ij(1)`, `y = X_jp(c)` and `z = X_pk(b)` for `m' = cb`.

**Conclusion.** Define `φ(x_ij(Σ c_m m)) = ∏ X_ij(m)^(c_m)`. This is well defined by (C).
- (R1) and (R3) hold for all ring elements.
- (R2) is bilinear, because every `X_ik(·)` commutes with every `X_ij(·)` and `X_jk(·)`, by (R3).
- So `φ : St_n(F) -> G` is a homomorphism.
- The natural `ψ : G -> St_n(F)` satisfies `ψφ = id`, since `ψ(X_ij(m)) = x_ij(m)` by (R2) in `St_n(F)`. It
  also satisfies `φψ = id` on the generators. ∎

**Presentation size.** `n(n-1)(d+1)` generators and finitely many relations: (B1) is quadratic in the number of
generators, and (B2) is cubic in `n`.

**Finitely presented rings.** For `R = F/(ρ_1, …, ρ_l)` and `n >= 5`, §4 gives
`St_n(R) = ⟨y_ij(u) | B1, B2, φ(x_12(ρ_t)), t = 1..l⟩`. Here `φ(x_12(ρ_t))` is the explicit word obtained by
expanding each monomial of `ρ_t` into iterated commutators. For `R_L` this is `d = 6`, `l = 9`; for `D` it is
`d = 6`, `l = 7`.

## 3. Why the argument stops at n = 4

- In (iii) with `n = 4`, the case of four distinct indices, e.g. `[X_12(m), X_34(m')] = 1`, has no free `p`.
- Running (★) instead turns it into `[X_14(gm'), X_32(b)] = 1`, which has the same total length and again four
  distinct indices.
- So the relations of this shape need a separate argument. This is presumably what Krstić–McCool supply. For
  `n = 3`, (i) already fails, which matches their Corollary 2.

## 4. The quotient step (companion node): PASS

- `St_n(F)/K ≅ St_n(F/I)`, where `K = ⟨⟨x_ij(I)⟩⟩`. The inverse `x_ij(r̄) ↦ x_ij(r)K` is well defined and
  respects (R1)–(R3).
- The six commutator identities spread `x_12(ρ)` to every index pair; I checked each against (R2).
- `x_ij(aρb) = [x_ik(a), [x_kl(ρ), x_lj(b)]]` for distinct `i,k,l,j`, which needs `n >= 4`. The elements `aρ_t b`
  span `I` additively.
- So `⟨⟨x_12(ρ_t)⟩⟩ = K`. ✓

## 5. Rank 5 in one-steinberg-group-contains-every-gl-n-q

The proof reviewed in `gq-referee-c-one-steinberg-group-contains-every-gl-n-q.md` uses rank 4 only in step (a).
At rank 5, step (a) needs:
- `K_2(5, M_k(Q))` central, which is C1, now with `5 >= sr + 2 = 3`;
- `St_(5k)(Q)` centrally closed, which is C2 with `5k >= 10`.

Steps (b)–(e) do not depend on the rank, and the image is `E_5(M_m(Q)) = SL_(5m)(Q) ⊇ GL_n(Q)` for
`5m >= n+1`.

So `Γ = St_5(D)` is a single finitely presented group containing every `GL_n(Q)`. Its finite presentation is §2
plus §4, with no Krstić–McCool input. The remaining citations are C1–C4.
