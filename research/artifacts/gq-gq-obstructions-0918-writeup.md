# Obstruction theorems of 2026-09-18: an expert summary

Compiled by lane `gq-writeup` from the Cairn nodes on origin/main at `476938cdb` (2026-09-18 03:39 local).
Five nodes changed while it was written, and those entries follow their text at `f8798d30a`: items 15, 16 and
23, the T_p candidate, and `prime-shift-group-k2-is-finitely-presented`. Each
theorem is restated from the current text of its node, and each carries the review status that the node itself
records. This summary makes no claims of its own. Where a lane board and a node disagree, the node is reported,
and the disagreement is listed in §5.

Review labels:
- **2 referees** means the node records PASS from gq-referee-a (proof gaps) and gq-referee-b (citations and
  hypotheses).
- **1 referee** names the one referee the node records.
- **Lane proof** means the node says "not independently reviewed".

Neither part below is a printed open problem. Both are claims that the graph uses to organize the attack on
`gl-n-q-embeds-in-fp-simple-group`, which is BBMZ arXiv:2306.16356v3, Problem 5.3(5).

## Part I. The Z_(l) bottleneck: `z-localized-embeds-in-fp-rf-group` (OPEN)

**The claim.** For some prime `l`, the additive group `Z_(l)` of rationals with denominators prime to `l` embeds
in a finitely presented residually finite group `Λ`.

**Why the graph tracks it.** Three open host hypotheses each imply it:
- a finitely presented Hecke overgroup of `SL_2(Z_(l))`, for `SL_2(Q)`;
- a finitely presented self-similar overgroup of `Aff_n(Z_(l))`, for `GL_n(Z_(l))`;
- a finitely presented self-similar overgroup of the rational Iwahori group, for `PSL_2(Q)`.

So a proof that no such `Λ` exists would close all three routes.

**Two levels are already reached, separately.**
- `Z_(l)` embeds in the finitely generated residually finite group `E_3(R̄_l)`
  (`sl-n-z-localized-embeds-in-fg-rf-elementary-group`).
- `Z_(l)` embeds in the finitely presented Kazhdan group `St_N(R_l)`, `N >= 4`
  (`z-localized-embeds-in-fp-kazhdan-steinberg-group`).

The open part is having both properties in one group.

**Constraints the root records for any witness Λ.** `Λ` is not linear, not metabelian, and contains no `(Q,+)`.
Every finite quotient sees `1 ∈ Z_(l)` with `l`-power order. The `l`-divisibility must come from a tree, an HNN
letter or level shifts.

### I.A Classes of groups that contain no Z_(l)

**1. `fg-metabelian-groups-have-roots-at-finitely-many-primes`** (lane proof; the addendum is a lane proof too).
- In a finitely generated metabelian group, an element of infinite order in `G'` has `q`-th roots for only finitely
  many primes `q`.
- So `Z[1/P]` with `P` infinite embeds in no finitely generated metabelian group. This covers `Z_(l)` and `Q`.
- Addendum: item 1 holds for every element of infinite order, not only those in `G'`.

**2. `z-localized-fixes-a-vertex-or-end-of-every-tree`** (2 referees; fixes W1 and W2 applied). Let `A ≤ (Q,+)`
contain some `a ≠ 0` divisible in `A` by infinitely many primes, and let `A` act on a simplicial tree without
inversions. Then:
- every element of `A` is elliptic;
- `A` fixes a vertex, or fixes an end `ω`; in the second case the groups `A ∩ Stab(v_k)` along a ray to `ω`
  eventually increase, with union `A`;
- in a graph of groups containing `A`, `A` is conjugate into a vertex group, or is the increasing union of its
  intersections with edge stabilizers along a ray.

**3. `free-group-mapping-tori-contain-no-z-localized`** (2 referees). Let `G_φ = ⟨F, t | t^(-1)xt = φ(x)⟩` for an
injective endomorphism `φ` of a free group `F` of finite rank, and let `A` be as in item 2.
1. If `A ≤ G_φ`, then after conjugation `A ≤ ∪_k t^k F t^(-k)`, and some `x ≠ 1` has an infinite root set
   `P(x) = {p : φ^k(x) is a p-th power in F for some k}`.
2. If `x ∈ γ_c F ∖ γ_(c+1) F` and `Φ_c^k [x] ≠ 0` for all `k`, then `P(x)` is finite.
3. So if `A ≤ G_φ`, then some `x ≠ 1` sinks through the lower central series.
4. If `φ_ab ⊗ Q` is injective, for example for free-by-cyclic groups, then `G_φ` contains no `Z_(l)`, no
   `Z[1/P]` with `P` infinite, and no `Q`.

**4. `ascending-hnn-extensions-of-free-groups-contain-no-z-localized`** (2 referees; Stallings graphs read at the
source, Kapovich–Myasnikov arXiv:math/0202285v1). For every injective `φ : F → F`, `F` free of finite rank:
1. if `r` is not a proper power and `φ(r) = s^f` with `s` not a proper power, then `f ≤ V_φ`, the number of
   vertices of the Stallings graph of `φ(F)`;
2. root primes of `x = r_0^(e_0)` divide `e_0` or are at most `V_φ`;
3. `G_φ` contains no `Z[1/P]` with `P` infinite, in particular no `Z_(l)` and no `Q`.

The node records that the argument extends to ascending HNN extensions of any finitely generated, torsion-free,
cyclic-centralizer group `F`, as long as `φ(F)` meets every cyclic subgroup with uniformly bounded index.

**5. `kms-minsky-groups-contain-no-z-localized`** (2 referees). For every Minsky machine `M` and prime `p`, every
torsion-free subgroup of the Kharlampovich–Myasnikov–Sapir group `G(M)` (arXiv:1204.6506v5, §4.1) is free abelian
of finite rank.
- So no `G(M)` contains `Z[1/q]`, `Z_(l)`, any `Z[1/P]` with `P` nonempty, `(Q,+)`, or the Euler lamplighter
  `G_l`.
- Input: Theorem 4.3(a), `G(M) ∈ 𝒜_p^2 𝒜`.

**6. `kms-configuration-letters-inherit-exponent-p`** (2 referees). Let `G^0(M)` be the KMS presentation with the
exponent-`p` law on `H_0` omitted. Then:
- `x_u^(A_i^n) = x_u x_(uA_i)^n` for `n ≥ 0`, and so `x_(uA_i)^p = 1` whenever `A_i` does not occur in `u`;
- only the letters `x_(q_0), …, x_(q_N)` can have infinite order.

Scope, as the node states it: the further reading, that the simulation takes place inside the `p`-torsion of
`T`, grants KMS Lemma 4.5, which was not re-derived.

**7. `euler-base-annihilator-over-lamplighter-is-not-fg`** (2 referees). Let `M = Z_(l)[y^(±1)]`, with
`H = ⟨x, β⟩ ≅ Z≀Z` acting by `x f_j = f_(j-1)` and `β f_j = (1+lj) f_j`.
1. With the Euler element `r = xβx^(-1) − β − l` and `D = Z[H]/(r)`, `M ≅ D/D(β−1)`.
2. The annihilator of `f_0` in `Z[H]` is not finitely generated as a left ideal, so `M` is not a finitely
   presented `Z[H]`-module.
3. For every group `Q ⊇ H`, `Z[Q] ⊗_(Z[H]) M` is not finitely presented over `Z[Q]`. Baumslag's finitely
   presented metabelian group is one such `Q`.

Referee a's strengthening R1: `(Z[Q] ⊗ M) ⋊ Q` is not finitely presented for any `Q ⊇ H`.

**8. `p-adic-dilation-normalizers-act-by-power-maps`** (2 referees; Serre's p-adic six exponentials theorem pinned
at the source).
- *Setting.* `Q_0 ≤ Q^x ∩ Z_p^x` contains three multiplicatively independent elements, and `c` is a homeomorphism
  from a ball `U ∋ 0` onto an open subset of `Z_p` with `c(uz) = β(u)c(z)` for `u ∈ Q_0`.
- Then `β` is an injective homomorphism, `c(0) = 0`, and `β(u)^b = u^a` on a finite-index subgroup of `Q_0`, for
  some integers `a ≠ 0` and `b ≥ 1`.
- For every prime `q ∈ Q_0`, `β(q) = ±q^e`. So no `c`, even as a germ at 0, satisfies
  `c d_(q_i) c^(-1) = d_(q_(i+1))` for `i = 0, 1, 2`, with `q_0, q_1, q_2` distinct primes other than `p` and
  `q_3` any prime other than `p`. Cycles `q_0 → q_1 → q_2 → q_0` are included.
- For a two-relation cycle `q_0 → q_1 → q_0` the node gets a contradiction elementarily. For a chain
  `q_0 → q_1 → q_2` it leaves `(log_p q_1)^2 = log_p q_0 · log_p q_2`, which the p-adic four exponentials
  conjecture would exclude (Serre's case `a = b = 2`, still open). A single relation `c d_q c^(-1) = d_(q′)` is not
  excluded.

**9. `finite-state-mobius-pieces-see-finitely-many-primes`** (2 referees).
- Let `Λ = ⟨h_1, …, h_k⟩` act by homeomorphisms of `Z_p`, each `h_i` locally Möbius on a dense open set with
  pieces in `Δ ≤ PGL_2(Q_p)`. Then any `γ ∈ Λ` that agrees with a Möbius map `m` on a nonempty open set has
  `m ∈ Δ`.
- Finite-state tree automorphisms have affine pieces, all in one `Aff(Z[1/N])`.
- So `⟨Γ_0, h_1, …, h_k⟩`, with `Γ_0 ≤ PGL_2(Q)` finitely generated and the `h_i` finite-state, contains `d_q` or
  `t_(1/q)` only for `q | N`. It contains neither `Γ_p` nor the translations by `Z_(p)`.

### I.B Ring and Steinberg results

*Setting, from the nodes.*
- `R_l` is the eight-relator resolvent ring. It is residually finite, with `Z_(l)` in a corner, and has a path
  normal form.
- `A = Z[u][π_k^(-1) : k ∈ Z] ⊂ Q(u)`, with `π_k = u + 1 + kl` and `σ(u) = u + l`.
- `D = A[x^(±1); σ]` is the Euler ring.
- `T_l = [[D, M],[0, Z]]`, with `M = D/Du ⊇ Z_(l)`, is finitely presented and residually finite.
- `St_N(T_l)` is finitely presented for `N ≥ 5` and contains `Z_(l)` through `x_12`
  (`euler-base-embeds-in-fp-steinberg-group`).
- `E_N(T_l)` is finitely generated and residually finite.

**10. `resolvent-ring-corner-symbols-survive-in-k2`** (1 referee: gq-referee-b PASS, W1 applied).
- The span `J` of the path elements with nonempty middle is an ideal, and
  `R_l/J = D ⊕ M_Z^fin(Z_(l))`.
- `θ_* : K_2(Z_(l)) → K_2(R_l)` is injective.
- For `N ≥ 3`, the stable classes of the corner symbols `c(λ,μ)` generate a subgroup that is not finitely
  generated: it has nonzero tame symbol `∂_q` for every odd prime `q ≠ l`.

**11. `resolvent-elementary-groups-are-not-fp`** (lane proof). For every prime `l` and `N ≥ 3`, neither `E_N(R_l)`
nor `E_N(R_l)/C` with `C` a finite normal subgroup is finitely presented.
- This refutes `resolvent-elementary-group-is-fp`.
- It closes route `z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l`.

**12. `resolvent-steinberg-rf-residual-is-infinitely-normally-generated`** (lane proof).
- gq-referee-b checked steps 1–4 given the two inputs, and later confirmed both inputs against the PDF pages:
  - Dennis–Stein, LNM 342, §12, for `K_2(Z/p^m)`;
  - van der Kallen, LNM 551, Thm 1, for injective stability.
- *Statement.* For every prime `l` and `N ≥ 3`, the finite residual of `St_N(R_l)` is not the normal closure of a
  finite set.
- This closes route `z-localized-fp-rf-via-resolvent-steinberg-rf-quotient`.

**13. `euler-ring-rational-symbols-are-infinitely-generated`** (2 referees).
- `I_p(z) = Σ_k k·v_p(∂_k z)` is a σ-invariant homomorphism `K_2(A) → Z`, with `I_p(c_d) = d·v_p(d)` for
  `c_d = {π_0, π_d}`.
- The classes of `c_q`, `q ≠ l` prime, generate a free abelian group of infinite rank in
  `coker(1 − σ_*)`, and also in `K_2(D)`, `K_2(T_l)` and `K_2(R_l)`.
- *Consequences.* For every `l` and `N ≥ 3`, `E_N(D)`, `E_N(T_l)` and `E_N(R_l)` are not finitely presented, and
  `K_2(N, T_l)` is not finitely generated.
- This refutes `euler-triangular-ring-has-fg-central-unstable-k2`.

**14. `euler-triangular-steinberg-retracts-to-euler-steinberg`** (1 referee: gq-referee-a PASS). For `N ≥ 3`:
- `St_N(D)` is a retract of `St_N(T_l)`;
- an element of `St_N(D)` survives in a finite quotient of `St_N(T_l)` if and only if it survives in one of
  `St_N(D)`.

For `N ≥ 5`, if `St_N(T_l)_rf` is finitely normally generated, so is `St_N(D)_rf`. So the Euler base, and `Z_(l)`
with it, plays no role in the `K_2` question.

**15. `euler-ring-symbols-in-small-finite-quotients`** (2 referees; gq-referee-a nits N1–N5 applied).
1. Every `c_q` dies in `K_2(N, F_(2,l))`, for all primes `l`, `q ≠ l` and `N ≥ 3`. For `l` odd and
   `1 ≤ r ≤ l − 1`, the image `C_r = Z[u]/(l,u)^r` has `K_2(N, C_r) = 0`, so every `c_q` dies in every
   `F_(r,N)`, `r ≤ l − 1`.
2. For `l` odd and `n ≥ l + 1`, the map `u ↦ ζ_l − 1` sends `c_q` to an element of `K_2(O_K/𝔭^n) ≅ Z/l` with
   Hilbert symbol `ζ^(-q)`. That is nontrivial.
3. Its σ-orbit gives `ρ_m : D → M_m(O_K/𝔭^n)` with `l | m`, and the image of `c_q` there is trivial.

The node does not treat `F_(r,N)` with `r ≥ max(l, 3)`, or `K_2(ρ_m(D))`.

**16. `one-sided-inverses-cannot-repair-the-steinberg-residual`** (2 referees).
- For every ideal `I ⊆ I_rf(T)`, `Γ_N(T) = St_N(T)/St_N(T)_rf ≅ Γ_N(T/I)`, when `N ≥ 3`.
- If `γπ = 1`, then `1 − πγ ∈ I_rf(T)`, because residually finite rings are Dedekind-finite.
- So replacing lamp inverses by one-sided inverses gives the same residually finite quotient, and the same
  finite-normal-generation question. When `T` is the presentation of `D` with `π_0^(-1)` replaced by a one-sided
  inverse `γ_0`, then `T′ ≅ D`.

### I.C The live candidates, and exactly what is open

**T_l route: `euler-ring-steinberg-rf-residual-is-fng`** (OPEN). The claim is that for some `l` and `N ≥ 5`,
`St_N(D)_rf` is finitely normally generated.
- It is **necessary** for the triangular route (item 14). If it fails, the route through `T_l` is closed.
- *Decided in the node's Attempts.* Every `c_q` dies in:
  - finite semisimple quotients;
  - split Artin–Schreier crossed products, for `q` odd;
  - `F_(2,l)`;
  - `F_(r,N)` with `r ≤ l − 1`.
  The cyclotomic σ-orbit is blind.
- *Open.*
  - `F_(r,N)` with `r ≥ max(l, 3)`, where at `r = l` the expected survivor is the class of `u^(l−1) du`.
  - `K_2` of wild crossed products `Ā ⋊ Z/m` with `l | m`, and `K_2(ρ_m(D))`.
  - Galois descent does not apply, since `σ` fixes the closed point.
- *Design constraint recorded.* Finite presentation needs the lamp inverses as ring relations, and that makes the
  `π_k` units, which creates the symbols.

**T_p route: `central-deformation-euler-host-has-fng-steinberg-residual`** (OPEN, lane gq-k2-q).
- *The host.* `B = Z⟨u, b, x^(±1)⟩` with `xux^(-1) = u + l`, `bu = ub` and `xpx^(-1) = p`, where
  `p = b(u+1)`. Then `M = B/(Bu + B(p−1))` and `T_p = [[B, M],[0, Z]]`.
- *Verified.* These are lane proofs:
  - `p` is central;
  - `B/(p−1) ≅ D`;
  - `T_p` is finitely presented with `Z_(l) ⊆ M`;
  - the lamps are not units of `B`, so the symbols `{π_0, π_q}` are not defined over `B`;
  - `p − 1 ∉ I_rf`;
  - `Z_(l)` survives in `Γ_N(T_p)` unconditionally.
- *Open.*
  - **C1: residual finiteness of `B` and `T_p`.** The lamps do not commute even in finite quotients, and adding
    finitely many commutations does not force the rest.
  - **C2: `K_2`.** At the stable level (Attempt 4, lane proof), a `t`-homotopy shows that the image of `K_2(B) → K_2(D)` has order at
    most 4. Quillen homotopy invariance is used as a textbook input, not re-read. So the image
    of `K_2(T_p) → K_2(T_l)` meets the span of the `c_q` only in `0`, and the Euler obstruction does not come
    from `T_p`. Three things are not covered:
    - classes in `ker(K_2(T_p) → K_2(T_l))`;
    - unstable `K_2(N, ·)`;
    - whether such classes die in every finite quotient.
  - **The ideal side** (Attempt 5, lane proof). For any ring `T` and `N ≥ 3`, a finitely normally generated
    `St_N(T)_rf` forces `I_rf(T)` to be finitely generated as a two-sided ideal. For `T_p` the route therefore
    needs `I_rf(B) ∩ (p−1)B` finitely generated, and the clean case is `B` residually finite. That is open, and
    needs a normal form for `B`.
  - **C3: finite quotients.** In the Euler-type Fitting components, a `c_q`-type obstruction could reappear.

## Part II. Prime mixing and type (A) actors for GL_n(Q), SL_2(Q) and Aff(Q)

**The target.** `gl-n-q-in-permutational-boone-higman-class` (OPEN): a finitely presented overgroup of `GL_n(Q)`
with an action of type (A).

**The prime-shift candidates** (root, Attempt 18, and `gl-n-q-lies-in-prime-shift-permutation-group`). Here `σ`
permutes the primes, `σ(p_k) = p_(k+1)`, and fixes `±1`.
- `K_n = ⟨GL_n(Z), e = diag(2,1,…,1), σ_n⟩ ≤ Sym(Q^n)` contains `GL_n(Q)` and is 2-transitive on `P^(n−1)(Q)`.
- `A_1 = ⟨x+1, 2x, −x, σ⟩ ≤ Sym(Q)` contains `Aff(Q)` and is 2-transitive on `Q`.
- For these, type (A) reduces to finite presentation plus one finitely generated point stabilizer.

**17. `prime-shift-affine-group-a1-is-not-finitely-presented`** (2 referees).
1. Germs at points with one very deep denominator give a surjection `Φ : A_1 → Z ≀ Z`. It has `Φ(τ) = Φ(ι) = 1`,
   `Φ(σ)` the top generator, and `Φ(m_r)` the valuation vector of `r`.
2. `m_r ∉ ⟨⟨τ⟩⟩_(A_1)` for every `r ∈ Q_(>0)`, `r ≠ 1`.
3. `A_1/⟨⟨τ⟩⟩` maps onto `Z ≀ Z` with kernel of order at most 2. So neither `A_1/⟨⟨τ⟩⟩` nor `A_1` is finitely
   presented.

This refutes `prime-shift-affine-group-a1-is-finitely-presented`. The action of `A_1` on `Q` is not of type (A),
and route `aff-q-bh-via-prime-shift-type-a-action` fails in its stated form.

**18. `prime-shift-kn-fp-reduces-to-a-metabelian-quotient`** (2 referees; Bieri–Strebel cited). For `n ≥ 2`:
1. There is a degree character `d : K_n → Z` onto, with `d(σ_n) = 1`, `d(GL_n(Q)) = 0` and
   `K_n = K_n^0 ⋊ ⟨σ_n⟩`.
2. The center of `K_n^0` is the scalar group `Q^x·I`.
3. `K_n/⟨⟨GL_n(Z)⟩⟩ ≅ (Q_(>0)/I_n) ⋊_σ Z`. This is a metabelian group whose base is a cyclic
   `Z[t,t^(-1)]`-module.
4. If `K_n` is finitely presented, then `e·diag(r,1,…,1)^(-1) ∈ ⟨⟨GL_n(Z)⟩⟩_(K_n)` for some finite product `r`
   of primes `p_k`, all with `k ≥ 1` or all with `k ≤ −1`.
5. Germs on `GL_n(Z)`-invariant domains of points cannot detect `e`.

Finite presentation of `K_2`, the prime-shift group for `n = 2` (not the K-group), stays OPEN:
`prime-shift-group-k2-is-finitely-presented`. Its Attempt 3 (lane gq-ring-fp-simple) is recorded as stalled. It
shows that `e ∈ N` if and only if one explicit element `r`, fixing three lines pointwise, lies in `N`. It also
shows that no scalar formula on those three lines decides this.

**19. `fg-restricted-product-actions-have-finite-support`** (lane proof).
- A finitely generated group of monomial bijections of a restricted product `∏′(Ω_i, o_i)` satisfies
  `|D(h)| ≤ s|h|`.
- In the coordinatewise case it fixes `o_i` for all `i` outside a finite set `S`.
- Every finitely generated subgroup of `∏′(G_i, K_i)` lies in `∏_(i∈S) G_i × ∏_(i∉S) K_i`.

*Consequence.* No finitely generated coordinatewise host carries `SL_n(Q)`, `GL_n(Q)` (`n ≥ 2`) or `Aff(Q)` acting
diagonally on the restricted product of their Bruhat–Tits buildings, or on any coordinatewise thickening with the
same base points. The reason: `u(1/p)` moves `o_p` for every `p`.

**20. `torus-amalgams-of-adelic-groups-are-not-finitely-presented`** (2 referees; Cornulier read at the source).
*Setting.* `Γ = GL_n(Q)` or `SL_n(Q)` (`n ≥ 2`), with `C ⊇` the diagonal subgroup and `C ∩ x_21(Q) = 1`; or
`Γ = Aff(Q)` with `C = Q^x`. `B` is finitely generated, and `C ↪ B`.
1. `Γ *_C B` is finitely generated and not finitely presented.
2. It is the directed colimit of the groups `E_S`, and for each prime `p ∉ S` the Baumslag–Solitar relation
   `(BS_p)` fails in `E_S`.
3. For every finitely generated `H` acting on the primes with finitely many orbits, `Π_n^H` and `Π_1^H` are not
   finitely presented.
4. `Π_n^H/⟨⟨GL_n(Z)⟩⟩ ≅ Z ≀_P H`. This is finitely presented exactly under Cornulier's conditions, so the
   metabelian test cannot see item 3. An example is `H = T`, acting on `P ≅ Z[1/2]/Z`.
5. **Hidden relations.** `K_n^H` or `A_1^H`, which are quotients of `Π_n^H` and `Π_1^H`, can be finitely presented
   only through a relation that fails in `Π_n^H`, respectively `Π_1^H`. This holds for every prime-permuting `H`.
6. Conjugation keeps the exponent: a prime-mixing element carries `(BS_p)` to another `p`-relation, not to
   `(BS_q)`.

**21. `algebraic-closure-kills-rational-steinberg-symbols`** (2 referees; four inputs pinned at the source).
Let `N ≥ 3`.
1. If `Q → F → R` are unital with `K_2(Q) → K_2(F)` zero, then the image of `K_2(N,Q)` in `St_N(R)` is trivial.
2. `F = Q̄` qualifies: `K_2(Q)` is torsion (Tate), and `K_2(Q̄)` is torsion-free (Bass–Tate).
3. `Q̄ ⊆ R_L` unitally, so all of `K_2(N,Q)` dies in `St_N(R_L)`. The literal rational symbol budget therefore
   obstructs no ring containing `Q̄`.
4. If `Q̄ ⊆ Z(R)`, the symbols `{λ, x}` with `λ ∈ Q̄^x` are divisible by every integer. So if `E_N(R)` is finitely
   presented, they vanish.

**22. `unimodular-line-pairs-detect-cyclic-quotients`** (1 referee: gq-referee-a PASS).
1. For `b ≠ 0`, `L_b = x_21(b) e_1 R` satisfies `R^N/(e_1R + L_b) ≅ R/bR ⊕ R^(N−2)`.
2. The isomorphism class of `R^N/(L + L′)` is an invariant of unordered pairs of lines.
3. So if the idempotents of `R` take infinitely many classes in `K_0(R)`, no group acting through `GL_N(R)` has
   finitely many orbits of pairs on lines.
4. This applies to every ring meeting items 3 and 4 of the gate below, and to every ring containing
   `U_Q = colim M_(n!)(Q)` unitally with `[1]` of infinite order. For such `R`, neither `E_N(R)` nor `PE_N(R)` is
   of type (A) on `Ω_N^0`.

Only the line action is excluded.

**23. `graded-rings-with-degree-one-units-fail-the-k-budget`** (1 referee: gq-referee-a PASS, report 223c763b9, W1
applied). Let `R ⊇ Q` be `Z`-graded with a unit
in degree one. Then `R = R_0[u^(±1); σ]`, and exactly one of the following holds:
- `ker(Q^x → K_1(R))` is not finitely generated;
- the symbols `{λ, u}`, `λ ∈ Q^x`, generate an infinitely generated subgroup of `K_2(R)`, and then neither
  `E_N(R)` nor `E_N(R)/C` with `C` finite normal is finitely presented, for any `N ≥ 3`.

The ring lamplighters `U_n ⋊ Z` and `U_Q ⋊ Z` fall in the second case, since `Q^x → K_1(U_n)` has finite kernel. So
no `E_N` of them is finitely presented. Adding homogeneous relations keeps a ring under the dichotomy, but can move
it to the first case (referee a, W1).

### What survives in Part II

- **The ring gate `fp-simple-resolvent-ring-with-divisible-unit-class`** (OPEN). It asks for a simple ring `R`
  finitely presented over `Z` with:
  1. `Q` produced by a resolvent vacuum;
  2. no Leavitt tuple;
  3. `R ≅ M_n(R_n)` for all `n`;
  4. `[1]` of infinite order in `K_0`;
  5. a finitely generated rational symbol subgroup of `K_2(R)`.

  Its necessary shape, from the nodes above:
  - not stably finite;
  - not a unital Leavitt–Nekrashevych completion;
  - not a finite graph algebra over a field;
  - no grading with a degree-one unit (item 23);
  - not of type (A) on lines (item 22).

  Item 21 makes the rational half of condition 5 automatic once `Q̄ ⊆ R` unitally. The symbols `{λ, x}` for
  non-rational units `x` are still to be controlled.
- **Prime-shift groups.** For every prime-permuting `H`, `K_n^H` (including `K_2` and `K_2^T`) can be finitely
  presented only through a hidden relation (item 20.5).
  - For `H = T`, the metabelian test passes (the kernel `J = 0` is allowed). So for `K_2^T`, finite presentation
    via a hidden relation is the only remaining possibility.
  - The node does not record this as a separate claim.
  - Also open: `prime-shift-hnn-map-to-a1-is-injective` and `prime-shift-affine-group-a1-has-fg-point-stabilizer`.

## Part III. BS(1,2) in nV (`bs12-embeds-in-brin-thompson-2v`, OPEN)

**24. `renormalization-return-times-tend-to-zero-adically`** (lane proof at `476938cdb`; since then 2 referees, gq-referee-b
fba51b1a0 and gq-referee-a d4e505ddd; see the evening summary `gq-gq-obstructions-0918-evening-writeup.md`). Let `T` have a height-`m`
renormalization `(A, φ)`.
1. `π(x) = Σ_j digit(S^j x) m^j` is a continuous factor onto `Z_m`, with `π ∘ T = π + 1`.
2. Under bounded brick depth `D` and bounded address growth `P`, `π mod m^j` is constant on bricks of depth
   `D + (j−1)P`. For moving-tape machines this is a window of radius `a + bj` around the head.
3. If `T^(n_i) y → y`, then `n_i → 0` in `Z_m`. So returns with `m^j ∤ n_i` for a fixed `j` exclude any height-`m`
   renormalization.

*Calibration.* SMART induced on genuine moves passes, with returns `n ≡ 0 mod 729` at radius 6 over `4·10^7`
steps on MSI.

**The +4 return-offset evidence** (`research/artifacts/gq-gq-nv-obstruct-binary-smart-search.md` §3e). For the
exact-doubling machine `M°` (mask 21, 52 zero-overhead types):
- every return found of the first `Y`-configuration has `n ≡ 4 mod 8`;
- at radii 10 and 14, `n ≡ 4 mod 64`;
- `rtm_cert` certificates, checked by `rtm_certcheck`, give `n = 29·2^m + 4` for `m = 11, 14, 15, 17`, at radii
  12–18;
- the other two exact-doubling machines show phase difference 4 in their first `mod 8` conflicts.

If `U°^(n_m) y → y` held at all radii, item 24.3 would exclude a height-2 renormalization of `U°`. The artifact
records this as certified only up to radius 18, so it is **OPEN**. It reads the failure as one of
recognizability, not of counting.

**Withdrawn.** The phase-conflict counts of §3d are withdrawn: "mod 4: hundreds of conflicts at radius 12" and
"mod 8: about 10^6 conflicts at radius 12–15".
- *The cause* was a hash collision in `rtm_induce`: state and first window cell shared one byte.
- *After the fix,* `mod 2` and `mod 4` show 0 conflicts at radii 6 and 9, and the remaining `mod 8` conflicts all
  involve one early configuration.

Context: `crossing-move-hierarchies-have-odd-branching` (lane proof) forces binary hierarchies to use return
moves.

## §5. Graph hygiene for the owners

1. **Resolved while this was compiled.** `euler-ring-symbols-in-small-finite-quotients` and
   `one-sided-inverses-cannot-repair-the-steinberg-residual` said "not independently reviewed" at `476938cdb`,
   although gq-referee-a had PASSed both. At `f8798d30a` both record PASS from referees a and b. No action needed.
2. **Stale sentence in the Z_(l) root** (`z-localized-embeds-in-fp-rf-group`, Attempt 3). It still calls
   `resolvent-steinberg-rf-residual-is-infinitely-normally-generated` "OPEN until two cited K-theory inputs are
   confirmed". The node is ESTABLISHED, with both inputs read at the source.
3. **Dangling "Part 4" reference.** Attempt 4 of `euler-ring-steinberg-rf-residual-is-fng` cites
   "`euler-ring-symbols-in-small-finite-quotients`, Part 4". The claim's Statement has items 1–3, and the
   `r ≤ l − 1` result sits in item 1. "Part 4" exists only in the proof route.
4. **Name collision.** `prime-shift-group-k2-is-finitely-presented` and the group `K_2^T` share a symbol with
   algebraic `K_2`. Both appear in `torus-amalgams-of-adelic-groups-are-not-finitely-presented`, next to Steinberg
   `K_2` statements.
5. **Unreviewed inputs in the chains.** The following are all lane proofs:
   - `fg-metabelian-groups-have-roots-at-finitely-many-primes`, with its addendum;
   - `resolvent-elementary-groups-are-not-fp`;
   - `fg-restricted-product-actions-have-finite-support`;
   - the verified facts of the T_p host.

   Four nodes have one referee each: `resolvent-ring-corner-symbols-survive-in-k2` (b),
   `euler-triangular-steinberg-retracts-to-euler-steinberg` (a), `unimodular-line-pairs-detect-cyclic-quotients` (a)
   and `graded-rings-with-degree-one-units-fail-the-k-budget` (a). Item 12 was checked by b only.
6. **British spellings in node text.** "centre", in `prime-shift-kn-fp-reduces-to-a-metabelian-quotient` and
   elsewhere, if the American-English rule is meant to cover node text.
