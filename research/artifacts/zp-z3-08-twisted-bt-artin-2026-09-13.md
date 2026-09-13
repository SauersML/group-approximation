# Zaremsky Problem 3.8: twisted Brin–Thompson groups of Artin groups, 2026-09-13

Lane `z3-08-artin-bt-embed`. Root: `zaremsky-3-08-twisted-brin-thompson-artin-in-fp-group`.

## 1. The problem and its reading

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 8, verbatim:
"Given an Artin group A, we can embed it in the finitely generated simple twisted
Brin–Thompson group AV_A. Does this group embed in a finitely presented group? If
so, then this would prove that Artin groups have solvable word problem."

**Reading.** `A = A_Γ` is an Artin group on a finite nonempty generating set. `AV_A`
is the twisted Brin–Thompson group `SV_G` with `G = S = A` and `A` acting on itself
by left translation. This is the group written `G·V_G` in Belk–Bleak–Matucci–Zaremsky
§4, where "G acts on itself by translation". The action is transitive, so `AV_A` is
finitely generated (Belk–Zaremsky Theorem A). It is simple (Belk–Zaremsky Theorem
3.4), and `A` embeds in it (BBMZ Theorem 4.13).

The question quantifies over all Artin groups. **Yes** means every `AV_A` embeds in a
finitely presented group. **No** means some `AV_A` embeds in none.

## 2. Sources read on 2026-09-13

All sources were read through HTML renderings (ar5iv or arXiv abstract pages) with a
summarizing fetch tool, which returned quotations and theorem numbers. No primary PDF
was read line by line.

- J. Belk and M. C. B. Zaremsky, *Twisted Brin–Thompson groups*, arXiv:2001.04579,
  Geom. Topol. 26 (2022) 1189–1223.
  - Definition: dyadic bricks `B(ψ) = {κ ∈ ℭ^S : ψ(s) is a prefix of κ(s)}` for a
    finitely supported `ψ: S → {0,1}*`; twist homeomorphisms "τ_γ(κ)(s) = κ(γ^{-1}s)".
  - Theorem A: "The group SV_G is finitely generated if and only if G is finitely
    generated and the action of G on S has finitely many orbits."
  - Theorem 3.4: "The twisted Brin–Thompson group SV_G is simple."
- J. Belk, C. Bleak, F. Matucci and M. C. B. Zaremsky, *Progress around the
  Boone–Higman Conjecture*, arXiv:2306.16356 (ar5iv rendering; a fetch of the v3
  HTML timed out). Its Theorems 3.6 and 3.8 carry the numbers that
  `boone-higman-thompson-simple-envelope` recorded from v3.
  - Theorem 4.13: "If G is a finitely generated group then G·V_G is a finitely
    generated simple group, and G embeds isometrically into G·V_G."
  - Corollary 4.14: "A finitely generated group G has solvable word problem if and
    only if the group G·V_G is computably presented."
  - Also: "It is easy to see that G·V_G has solvable word problem if and only if G
    does."
  - Higman's embedding theorem as stated there: "Let G be a finitely generated group.
    Then G is computably presented if and only if G embeds into a finitely presented
    group."
  - Footnote 10: "It is an open question whether all Artin groups have solvable word
    problem [Charney, *Problems related to Artin groups*, Problem 10], but this is
    known for several large classes, such as right-angled Artin groups ... and Artin
    groups of spherical or Euclidean type."
- M. C. B. Zaremsky, *Finite presentability of twisted Brin–Thompson groups*,
  arXiv:2405.18354v2. Abstract: "Given a group G acting faithfully on a set S, ...
  SV_G is finitely presented if and only if we have the following: G is finitely
  presented, the action of G on S has finitely many orbits of two-element subsets of
  S, and the stabilizer in G of any element of S is finitely generated." Also Theorem
  A, stated with "type (A)". Already in the graph as
  `twisted-brin-thompson-finite-presentation-criterion`.
- Word problem sources are listed in §5.
- **Status search.** arXiv full-text search for "word problem" Artin groups, newest
  first (25 results, the newest July 2026). No result claims the word problem for all
  Artin groups, and none treats finitely presented hosts of twisted Brin–Thompson
  groups of Artin groups. The search was bounded: arXiv only, no MathSciNet or
  zbMATH, and no general web search (the session's search budget was exhausted).

## 3. Theorem 1: the problem is the word problem

**Theorem 1.** Let `G` be a finitely generated group, and let `G·V_G` be its twisted
Brin–Thompson group for the translation action. The following are equivalent:
1. `G·V_G` embeds in a finitely presented group;
2. `G·V_G` is computably presented;
3. `G·V_G` has solvable word problem;
4. `G` has solvable word problem.

**Credit.** Almost none of this is new:
- (1)⇔(2) is Higman's embedding theorem;
- (2)⇔(4) is BBMZ Corollary 4.14;
- (3)⇔(4) is the step BBMZ call easy.

What this graph adds is the observation that, for `G = A`, the equivalence answers
the *logical status* of Problem 3.8. The problem's own sentence gives (1)⇒(4); by
Higman the converse holds as well. So Problem 3.8 is equivalent to the word problem
for Artin groups.

**Proofs.**
- **(1)⇒(2).** Let `G·V_G = ⟨y_1, …, y_k⟩ ≤ H`, where `H` is finitely presented. The
  words in the `y_i` that are trivial in `H` form a recursively enumerable set, and
  Craig's trick turns that into a computable presentation. (This is one direction of
  Higman's theorem as BBMZ state it.)
- **(2)⇒(1).** Higman's embedding theorem.
- **(2)⇒(3).** This is Kuznetsov's two enumerations.
  - `G·V_G` is simple (Belk–Zaremsky Theorem 3.4) and nontrivial. It has a finite
    generating set `Y` and a recursively enumerable set `R` of relators.
  - Given a word `w`, enumerate the normal closure of `R`, and halt if `w` appears.
  - In parallel, enumerate consequences of `R ∪ {w}`, and halt once every `y ∈ Y` has
    been proved trivial.
  - Exactly one of the two halts: if `w ≠ 1`, then `⟨⟨w⟩⟩ = G·V_G`.
  - The proof is that of `simple-envelope-forces-solvable-word-problem-proof`, with an
    enumerable relator set in place of a finite one.
- **(3)⇒(2).** A solvable word problem gives a computable set of relators.
- **(3)⇒(4).** `G` embeds in `G·V_G` (BBMZ Theorem 4.13). A finitely generated
  subgroup of a group with solvable word problem has solvable word problem.
- **(4)⇒(3).** This is the brick algorithm.
  - **Data.** Fix a finite generating set `X` of `G` and a word problem algorithm for
    `G`. An element `f ∈ G·V_G` has a finite description: triples `(ψ_i, γ_i, ψ'_i)`.
    - The domain bricks `B(ψ_i)` partition `ℭ^G`, and so do the range bricks
      `B(ψ'_i)`.
    - `f` maps `B(ψ_i)` onto `B(ψ'_i)` as the twist `τ_{γ_i}` followed by the
      canonical prefix-replacement map between bricks.
    - A brick function `ψ` is a finite list of pairs (point of `G` as a word over `X`,
      binary string) with pairwise distinct points. Distinctness is decidable.
  - **Operations.** Three operations suffice:
    - twisting a brick function relabels the point `s` as `γs`, by word
      concatenation;
    - two bricks `B(ψ)` and `B(φ)` intersect exactly when `ψ(s)` and `φ(s)` are
      prefix-comparable at every common point, and then the intersection is a brick.
      Common points are found with the word problem of `G`;
    - canonical maps and twists send subbricks to computable subbricks.
    Composing two descriptions means intersecting each range brick of the first with
    each domain brick of the second, pulling back and pushing forward through the
    piece maps, and multiplying the twists.
  - **Twist uniqueness.** Suppose two piece maps `h ∘ τ_γ` and `h' ∘ τ_{γ'}` agree on
    a nonempty open set `U`. Then `γ = γ'`.
    - Put `δ = γ'^{-1}γ`. If `δ ≠ 1`, choose `s` with `δ^{-1}s ≠ s`; the action is
      faithful.
    - On `U` the `s`-coordinate of `τ_δ κ` is `κ(δ^{-1}s)`, while a canonical map
      changes coordinate `s` only by replacing a prefix of `κ(s)`.
    - Shrink `U` to a brick, which constrains finitely many coordinates by finite
      prefixes. Varying the tail of `κ(s)` while fixing `κ(δ^{-1}s)` contradicts the
      agreement.
  - **Triviality test.** `f = id` iff every piece of a description has `γ_i = 1` and
    `ψ_i = ψ'_i`.
    - By twist uniqueness, every piece of the identity has twist `1`.
    - A canonical map `B(ψ) → B(ψ')` is the identity iff `ψ = ψ'`.
    - Both tests are decidable with the word problem of `G`.
  - Fix finite descriptions of a finite generating set of `G·V_G` and of the inverses
    of its elements. Composition along a word then decides the word problem of
    `G·V_G`. ∎

## 4. Theorem 2: G·V_G is never finitely presented for infinite G

**Theorem 2.** If `G` is infinite, then `G·V_G` is not finitely presented.

**Proof.**
- The translation action is faithful, so Zaremsky's criterion applies, and finite
  presentability requires finitely many orbits of two-element subsets.
- The orbit of `{g, h}` contains `{1, g^{-1}h}`.
- Suppose `k{1, x} = {1, y}` with `x, y ≠ 1`. Either `k = 1` and `y = x`, or `k = y`
  and `kx = 1`, so `y = x^{-1}`.
- So the orbits of two-element subsets correspond bijectively to the sets
  `{x, x^{-1}}` with `x ≠ 1`, and there are infinitely many when `G` is infinite. ∎

**Artin groups are infinite.** Send every standard generator to `1 ∈ Z`. Each relator
`prod(s,t;m) = prod(t,s;m)` has sides of equal length, so this is a homomorphism onto
`Z`.

**Consequence.** A finitely presented host of `AV_A` is always a proper overgroup, so
the naive route "`AV_A` is itself finitely presented" is dead for every Artin group.

## 5. Artin groups with known solvable word problem

| Class | Source (statement as returned by the renderings) | Mechanism |
|---|---|---|
| right-angled | BBMZ footnote 10, citing Theorem 5.1 | secondary citation only |
| spherical type | BBMZ footnote 10; also contained in FC type below | secondary citation; also Helly |
| irreducible euclidean type | McCammond–Sulway, arXiv:1312.7770 (Invent. Math.), Theorem D: "Every irreducible euclidean Artin group Art(X̃_n) is a torsion-free centerless group with a solvable word problem and a finite-dimensional classifying space." | Garside structures on supergroups |
| type FC | Huang–Osajda, arXiv:1904.09060, Main Theorem: "Weak Garside groups of finite type and Artin groups of type FC are Helly"; Corollary item (6): biautomatic | Helly ⇒ biautomatic |
| Helly groups | Chalopin–Chepoi–Genevois–Hirai–Osajda, arXiv:2002.06895, Geom. Topol. 29 (2025), Theorem 1.5(1): "Γ is biautomatic" | biautomatic ⇒ solvable word problem |
| large type (labels ≥ 3) | Huang–Osajda, arXiv:1706.05473 (Proc. LMS), Theorem 5.8: "Every Artin group of almost large type is systolic"; Corollary (1): biautomatic | systolic ⇒ biautomatic (Januszkiewicz–Świątkowski) |
| dimension ≤ 2 (`1/p+1/q+1/r ≤ 1` on triangles) | Huang–Osajda, arXiv:1710.05157, Corollary 1.3(2): finitely presented subgroups of 2-dimensional Artin groups "ha[ve] solvable Conjugacy Problem" | conjugacy problem ⇒ word problem |
| rank three | Delucchi–Paolini–Salvetti, arXiv:2206.14518, Geom. Topol. 28 (2024) 4295–4336, Theorem 7.4: "The word problem for G_W is solvable." | dual Garside structure |

Two further points:
- Finite direct products of groups with solvable word problem have solvable word
  problem, and an Artin group whose defining graph splits by label-2 joins is the
  direct product of the pieces.
- **Abstract only, not added to the table:** arXiv:2204.03523, Blasco-García,
  Cumplido and Morris-Wright, "The Word Problem is Solvable for 3-free Artin Groups in
  Quadratic Time". Its abstract says: "We give a quadratic-time explicit and
  computable algorithm to solve the word problem for Artin groups that do not contain
  any relations of length 3." The body was not read.

**Corollary.** For `A` in any of these classes, or a finite direct product of such
groups, `AV_A` embeds in a finitely presented group. The host can be taken with
solvable word problem (Clapham; `clapham-fp-embedding-preserves-word-problem`).

## 6. Lemma 3: explicit hosts from actors with a free orbit (unreviewed)

**Lemma 3.** Let `Δ` act on a set `T`, let `Γ ≤ Δ`, and let `S ⊆ T` be `Γ`-invariant
with `Γ` acting faithfully on `S`. Then `SV_Γ` embeds in `TV_Δ`.

**Proof.**
- Write `ℭ^T = ℭ^S × ℭ^{T∖S}`. Since `Γ` preserves `S`, `τ_γ = τ_γ|_S × τ_γ|_{T∖S}`.
- For `f ∈ SV_Γ`, twist uniqueness (§3) gives a well-defined locally constant twist
  cocycle `c_f: ℭ^S → Γ`. It satisfies `c_{fg}(x) = c_f(g x) c_g(x)`.
- Define `φ(f)(x, y) = (f(x), τ_{c_f(x)} y)`. This is a homomorphism by the cocycle
  identity, and injective because `φ(f) = id` forces `f = id`.
- On the brick of `ℭ^T` obtained by extending a domain brick of `f` by empty words
  off `S`, `φ(f)` is `τ_{γ_i}` on all of `T` followed by the canonical map on the
  `S`-coordinates. So `φ(f) ∈ TV_Δ`. ∎

**Corollary 3′.** Let `A ≤ Δ`, where `Δ` acts faithfully on `T` with type (A) (Δ
finitely presented, finitely generated point stabilizers, finitely many orbits of
two-element subsets), and suppose some `A`-orbit in `T` is free. Then `AV_A` embeds in
the finitely presented simple group `TV_Δ`. This uses Zaremsky Theorem A and
Belk–Zaremsky Theorem 3.4.

**Remarks.**
- This is the kind of *explicit* host Zaremsky's question invites. By Theorem 1,
  though, any such `Δ` forces a solvable word problem for `A`, so finding one is at
  least as hard as the word problem.
- The permutational Boone–Higman types proved so far lie in the spherical and
  euclidean classes, where the word problem is known:
  - A_n, B_n = C_n, D_n, I_2(m) and Ã_n, in `aut-free-groups-satisfy-permutational-boone-higman`;
  - C̃_n and B̃_n, in this graph.
- Whether their actors have free `A`-orbits was not checked.
- No functoriality lemma of this form was found in Fournier-Facio–Wu–Zaremsky,
  arXiv:2603.24687v2 (fetch-tool reading). It may be folklore.

## 7. What remains, and firewalls

- The root is equivalent to Charney's Problem 10: do all Artin groups have solvable
  word problem? Yes for Problem 3.8 ⇔ yes for all Artin groups; no ⇔ some Artin group
  has unsolvable word problem.
- **Firewall.** No argument through `AV_A` can settle the word problem of an Artin
  group more cheaply than a direct one, since Theorem 1 is an equivalence. A route
  "embed `AV_A` in a finitely presented group, hence WP" is a proof strategy, not a
  weaker target.
- **Firewall.** `AV_A` itself is never finitely presented (Theorem 2), so any
  finitely presented host must be a proper overgroup, e.g. `TV_Δ` from Corollary 3′.
- **Open directions.**
  - The word problem beyond the listed classes: diagrams containing spherical
    triangles but not FC, of rank at least 4, and not euclidean.
  - An Artin group with unsolvable word problem, of which no candidate is known.
