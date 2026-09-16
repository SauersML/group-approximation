# Amenable automatic groups: the free-subsemigroup dichotomy and the split into Thurston's conjecture plus elementary amenability

2026-09-16, swarm lane `swarm-amenable-automatic-groups-are-`, working on the hole
`amenable-automatic-groups-are-virtually-abelian`.

- **Proved (Theorem 4):** every automatic group is virtually abelian or contains a free
  subsemigroup of rank 2. So an automatic group of subexponential growth is virtually
  abelian. The proof uses four imported facts: structures with uniqueness exist, Gromov's
  theorem, finite-index subgroups of automatic groups are automatic, and automatic nilpotent
  groups are virtually abelian. On top of those it uses only finite-automaton pumping.
  Novelty is not claimed (Section 5).
- **Proved (Section 6):** with three more imports, the hole is *equivalent* to the
  conjunction of two open statements:
  - (S) every soluble automatic group is virtually abelian (Thurston's conjecture, open as of
    Rees's 2022 survey and no 2024–2026 arXiv progress found);
  - (EA) every amenable automatic group is elementary amenable.
- **Not proved:** the hole, (S) or (EA). Section 7 records exactly where the known
  biautomatic proof of (S) stops for automatic groups.

## 0. Conventions and imported facts

A group `G` is *automatic* in the sense of Epstein–Cannon–Holt–Levy–Paterson–Thurston
(ECHLPT, *Word Processing in Groups*, 1992). We use the formulation in Romankov,
arXiv:1511.00223v1, §6, read 2026-09-16. `A` is a finite alphabet with a map
`λ : A* → G` onto `G` that is a monoid homomorphism. `L ⊆ A*` is a regular language
with `λ(L) = G`. For every `a ∈ A`, the language

    M_a = { (u, v)$ : u, v ∈ L,  λ(u) a = λ(v) }

is regular over the padded alphabet `(A ∪ {$}) × (A ∪ {$})`. Here `(u, v)$` denotes the
*padded pair*. It is the word of length `max(|u|, |v|)` whose `i`-th letter is
`(u_i, v_i)`, and the shorter word is filled with `$` at the end. The structure has
*uniqueness* if `λ|_L : L → G` is a bijection. For `g ∈ G` write `|g|` for the word
length with respect to `λ(A)`, which generates `G` as a monoid.

Imported facts (each a claim with its own citation route):

- **(U)** Every automatic group has an automatic structure with uniqueness
  (`automatic-groups-admit-structures-with-uniqueness`; ECHLPT Theorem 2.5.1 as cited by
  Engel–Wulff).
- **(Gr)** A finitely generated group of polynomial growth is virtually nilpotent
  (`gromov-and-milnor-wolf-growth-alternatives`, established).
- **(FI)** A finite-index subgroup of an automatic group is automatic
  (`finite-index-subgroups-of-automatic-groups-are-automatic`).
- **(Nil)** A finitely generated nilpotent automatic group is virtually abelian
  (`automatic-nilpotent-groups-are-virtually-abelian`).
- **(Fin)** Automatic groups are of type `F_∞` (`automatic-groups-are-of-type-f-infinity`).
- **(KMN)** An elementary amenable group of type `FP_∞` is virtually soluble
  (`elementary-amenable-fp-infinity-groups-virtually-soluble`).

## 1. Representatives are at most linearly long

**Lemma 1.** Let `(A, λ, L)` be an automatic structure with uniqueness for `G`, and
write `w_g` for the unique word of `L` representing `g`. Fix, for each `a ∈ A`, a
deterministic finite automaton recognising `M_a`, and let `S` be the largest number of
states among them. Then
for all `g ∈ G` and `a ∈ A`,

    |w_{g λ(a)}| <= |w_g| + S,

and hence `|w_g| <= S |g| + |w_1|` for every `g ∈ G`.

*Proof.* Put `u = w_g` and `v = w_{gλ(a)}`. Suppose `|v| > |u| + S`. The padded pair
`σ = (u, v)$` lies in `M_a` and has length `|v|`. For every position `i > |u|` its letter
is `($, v_i)`. The run of the fixed deterministic automaton for `M_a` on `σ` is a
sequence of states `s_0, …, s_{|v|}` ending in an accept state. The `|v| − |u| + 1 > S + 1` states
`s_{|u|}, …, s_{|v|}` include a repetition `s_i = s_j` with `|u| <= i < j <= |v|`.
Deleting the letters in positions `i + 1, …, j` of `σ` leaves an accepted word `σ'`. Its
first `|u|` letters are those of `σ`, and every later letter still has the form
`($, x)` with `x ∈ A`. Hence `σ' = (u, v')$`, where `v'` is `v` with the positions
`i + 1, …, j` deleted, so `|u| <= |v'| < |v|`. Because `σ' ∈ M_a`, the definition of
`M_a` gives `v' ∈ L` and `λ(v') = λ(u) a = λ(v)`. Uniqueness forces `v' = v`, which
contradicts `|v'| < |v|`. So `|v| <= |u| + S`.

For the second inequality, write `g = λ(a_1 ⋯ a_n)` with `n = |g|` and apply the first
inequality `n` times, starting from `w_1`. ∎

**Corollary 2.** With `β_G(n) = #{g : |g| <= n}` and `β_L(n) = #{w ∈ L : |w| <= n}`,

    β_L(n) <= β_G(n) <= β_L(S n + |w_1|)   for all n.

*Proof.* The left inequality holds because `λ|_L` is injective and `|λ(w)| <= |w|`. The
right one holds because `g ↦ w_g` is injective and, by Lemma 1, lands in words of length
at most `S|g| + |w_1|`. ∎

## 2. The growth dichotomy for a regular language, in the form needed

Let `D` be a deterministic finite automaton over `A`. It has start state `q_0`, accept
states `F` and a partial transition function `(q, a) ↦ q·a`, extended to words. Assume
`D` is *trim*: every state is reachable from `q_0`, and from every state some accept
state is reachable. Every nonempty regular language is recognised by such a `D`: delete
the useless states of any deterministic automaton. Let `s` be the number of states.

A *first-return loop at `q`* is a nonempty word `u` with `q·u = q` and `q·u' ≠ q` for every
nonempty proper prefix `u'` of `u`.

**Lemma 3.** Exactly one of the following holds.

1. Some state `q` has two distinct first-return loops `u ≠ v`. Then neither of `u`, `v` is
   a prefix of the other, and the monoid homomorphism `φ : {a, b}* → A*` with
   `a ↦ u`, `b ↦ v` is injective.
2. Every state has at most one first-return loop. Then there is a constant `K = K(D)`
   with `β_L(n) <= K (n + 1)^s` for all `n`, where `L = L(D)`.

*Proof of 1.* If `u` were a proper prefix of `v`, then, since `u` is nonempty and
`q·u = q`, the word `v` would have a nonempty proper prefix returning to `q`. That
contradicts the choice of `v`. The symmetric argument applies, so `{u, v}` is a prefix
code. Suppose `φ(α) = φ(β)` with `α ≠ β`, and remove the longest common prefix of `α`
and `β`. If one of the remainders is empty and the other is not, then a nonempty product
of `u`'s and `v`'s is the empty word, which is impossible. Otherwise the remainders begin
with different letters. Then `u` and `v` are both prefixes of the same word, so one is a
prefix of the other, which is also impossible. Hence `φ` is injective.

*Proof of 2.* Let `C` be a strongly connected component of the transition graph that
contains at least one edge with both ends in `C`. Every state of `C` then has an outgoing
edge inside `C`. Suppose some `p ∈ C` has two different outgoing edges inside `C`. Their
labels `x ≠ y` differ because `D` is deterministic. Pick words `z_x` and `z_y` that lead
from `p·x` and `p·y` back to `p` inside `C`. The shortest prefixes of `x z_x` and `y z_y`
that return to `p` are first-return loops at `p`, and they begin with different letters.
This contradicts 2. So every state of `C` has exactly one outgoing edge inside `C`, and a
strongly connected graph in which every vertex has out-degree 1 is a single directed
cycle.

Let `w ∈ L` have length `<= n`. Its run `q_0 = r_0, r_1, …, r_{|w|}` visits a sequence
of components `C_1, …, C_m` that is strictly increasing in the (acyclic) condensation,
so `m <= s`. Within a component that is a cycle, the run moves along the unique cycle
edges. The segment of `w` read inside `C_i` is therefore determined by the state at which
the run enters `C_i` and the number `t_i ∈ {0, …, n}` of letters read there. Between
components the run crosses a single edge, determined by a letter. So `w` is determined by
two pieces of data. The first is the discrete data: the components, the entry states and
the crossing letters. There are at most `K` possibilities for it, with `K` depending only
on `D`. The second is the tuple `(t_1, …, t_m)`. Hence `β_L(n) <= K (n + 1)^s`.

*Exactly one.* If 1 holds, then with `x` a word with `q_0·x = q` and `z` a word with
`q·z ∈ F`, the `2^k` words `x φ(α) z` with `|α| = k` are distinct words of `L` of length
at most `|x| + |z| + k max(|u|, |v|)`. So `β_L` grows exponentially and 2 fails. ∎

## 3. The dichotomy for automatic groups

**Theorem 4.** Let `G` be an automatic group. Then `G` is virtually abelian, or `G`
contains two elements that freely generate a free subsemigroup of rank 2.

*Proof.* By (U), `G` has an automatic structure `(A, λ, L)` with uniqueness. Let `D` be a
trim deterministic automaton for `L` and apply Lemma 3.

*Case 2 of Lemma 3.* By Corollary 2, `β_G(n) <= K (S n + |w_1| + 1)^s`, so `G` has
polynomial growth. By (Gr), `G` has a nilpotent subgroup `H` of finite index. `H` is
finitely generated, being of finite index in a finitely generated group. By (FI), `H` is
automatic. By (Nil), `H` has an abelian subgroup `B` of finite index. Then `B` has finite
index in `G`, so `G` is virtually abelian.

*Case 1 of Lemma 3.* Take `q`, `u ≠ v` and the injective `φ` from Lemma 3. Since `D` is
trim there are words `x` and `z` with `q_0·x = q` and `q·z ∈ F`. For every
`α ∈ {a, b}*` we have `q·φ(α) = q`, so `x φ(α) z ∈ L`. Let `ψ : {a, b}* → G` be the monoid
homomorphism `ψ(α) = λ(φ(α))`, so `ψ(a) = λ(u)` and `ψ(b) = λ(v)`. Suppose `α ≠ β`. Then
`φ(α) ≠ φ(β)` because `φ` is injective. So `x φ(α) z` and `x φ(β) z` are distinct words
of `L`, and uniqueness makes them represent distinct elements:
`λ(x) ψ(α) λ(z) ≠ λ(x) ψ(β) λ(z)`. Cancelling in the group gives `ψ(α) ≠ ψ(β)`. So `ψ` is
injective. This means `λ(u)` and `λ(v)` freely generate a free submonoid of `G`. Its
nonempty words form a free subsemigroup of rank 2. ∎

**Remarks.**

- The two cases are exclusive. A group containing a free subsemigroup of rank 2 has
  exponential growth, and virtually abelian groups grow polynomially. In particular every
  automatic structure with uniqueness on a virtually abelian group has a polynomially
  growing language.
- Case 1 needs only (U). Case 2 is the only place where (Gr), (FI) and (Nil) are used.

## 4. What Theorem 4 does and does not give for the hole

**Corollary 5.** An automatic group of subexponential growth is virtually abelian. In
particular no automatic group has intermediate growth. A counterexample to
`amenable-automatic-groups-are-virtually-abelian` must have exponential growth and must
contain a free subsemigroup of rank 2.

*Proof.* A free subsemigroup of rank 2 forces exponential growth. Apply Theorem 4. ∎

Automatic groups are finitely presented (Rees, arXiv:2205.14911v1, Proposition 2.1,
p. 10). So Theorem 4 is also the automatic case of Grigorchuk's conjecture
`fp-groups-without-free-subsemigroups-are-virtually-nilpotent`, in a stronger form: the
conclusion is "virtually abelian", not just "virtually nilpotent". No route into that claim
is recorded, because the claim is about all finitely presented groups.

**Why this does not reduce the hole.** Amenability does not exclude free subsemigroups.
Here is an explicit amenable example. In `BS(1,2) = Z[1/2] ⋊ Z`, acting on `R` by affine
maps, the elements `f_0(x) = 2x` and `f_1(x) = 2x + 1` generate a free subsemigroup. A
composite `f_{i_1} ∘ ⋯ ∘ f_{i_k}` is `x ↦ 2^k x + n`, where the integer `n` has binary
digits `i_1 … i_k` read from the most significant digit. So `k` is recovered from the
slope and the word from `n`. `BS(1,2)` is metabelian, hence amenable, but it is not
automatic. Rees (arXiv:2205.14911v1, pp. 11–12) says the Dehn function argument "proves
easily the non-automaticity of the Baumslag–Solitar groups ⟨a, b | b a^p b^{-1} = a^q⟩ for
which p, q > 0 and p ≠ q, since they have exponential Dehn function"; take `p = 1`,
`q = 2`. So the example is not a counterexample. It only shows that Corollary 5
cannot finish the job: amenable groups of exponential growth can contain free
subsemigroups. (From memory, not re-verified: Rosenblatt 1974 and Chou 1980 show that
every finitely generated elementary amenable group that is not virtually nilpotent
contains a free subsemigroup of rank 2. If so, Theorem 4 says nothing about elementary
amenable automatic groups beyond the nilpotent case.)

## 5. Novelty and sources for Section 3

- Rees, arXiv:2205.14911v1 (30 May 2022), p. 14, verbatim: "it was already proved in [26]
  that an automatic nilpotent group must be virtually abelian; the proof uses the fact that
  a regular language with polynomial growth cannot satisfy a (synchronous) fellow traveller
  property." Here [26] is ECHLPT. The polynomial half of Theorem 4 is therefore the
  ECHLPT mechanism, imported through (Nil) instead of reproved.
- Case 1 (pumping two first-return loops into a free submonoid) is the standard proof that
  a regular language of non-polynomial growth contains `x{u,v}*z` for a code `{u, v}`. We
  attribute it to the folklore of regular-language density, from memory: Ibarra–Ravikumar
  1986; Szilard–Yu–Zhang–Shallit 1992. The attribution is unverified. The only
  group-theoretic input is uniqueness.
- **Novelty audit, incomplete.** arXiv API title/abstract queries on 2026-09-16 found
  nothing stating Theorem 4:
  - `abs:"automatic" AND abs:"subsemigroup"`;
  - `abs:"automatic" AND abs:"intermediate growth"`;
  - `abs:"automatic structure" AND abs:"growth"` in math.GR, which returned five unrelated
    growth papers.

  The web-search budget of this session was exhausted before a full-text search. **No
  priority is claimed.** Treat Theorem 4 as a folklore-level consequence of ECHLPT whose
  proof is written out here so the graph can use it.

## 6. The hole is equivalent to Thurston's conjecture plus elementary amenability

Let

- (S) = `soluble-automatic-groups-are-virtually-abelian`: every finitely generated soluble
  automatic group is virtually abelian;
- (EA) = `amenable-automatic-groups-are-elementary-amenable`: every amenable automatic
  group is elementary amenable;
- (H) = the hole `amenable-automatic-groups-are-virtually-abelian`.

**Proposition 6.** (H) implies (S) and (EA). Conversely, (S), (EA), (Fin), (KMN) and
(FI) together imply (H).

*Proof of (H) ⇒ (S).* Soluble groups are amenable: abelian groups are amenable, and
amenability passes to extensions. Apply (H).

*Proof of (H) ⇒ (EA).* A virtually abelian group `G` has a normal abelian subgroup of
finite index: the normal core of an abelian finite-index subgroup. So `G` is an extension
of an abelian group by a finite group, and lies in Chou's class `EG`.

*Proof of the converse.* Let `G` be amenable and automatic. By (EA), `G` is elementary
amenable. By (Fin), `G` is of type `F_n` for every `n`. The cellular chain complex of the
universal cover of a `K(G,1)` with finite `n`-skeleton is a free resolution of `Z` over
`ZG` that is finitely generated in degrees `<= n`. So `G` is of type `FP_n` for every `n`,
which is the definition of `FP_∞` used by Brittenham–Hermiller–Johnson (arXiv:1506.00071v1,
p. 3). A single resolution of finite type exists by the standard extension argument (Brown,
*Cohomology of Groups*, VIII.4, from memory). By (KMN), `G` has a soluble subgroup `H` of
finite index. `H` is finitely generated, and it is automatic by (FI). By (S), `H` has an
abelian subgroup `B` of finite index. Then `[G : B] < ∞`, so `G` is virtually abelian. ∎

**Proposition 7.** `every-f-infinity-amenable-group-is-elementary-amenable` and (Fin)
imply (EA).

*Proof.* An amenable automatic group is amenable and, by (Fin), of type `F_∞`. ∎

So (EA) sits under Zaremsky Problem 1.12. The nonexistence answer
(`zaremsky-1-12-by-nonexistence`) would give it, and a torsion-free counterexample to (EA)
would be a new amenable non-elementary-amenable group of type `F_∞`.

## 7. Where the biautomatic proof of (S) stops for automatic groups

Romankov, arXiv:1511.00223v1 (1 November 2015), Theorem 6.3, which he attributes to
Bazhenova, Noskov, Remeslennikov and Roman'kov, says: "Let G be a finitely generated
soluble biautomatic group. Then G is virtually abelian." Rees (arXiv:2205.14911v1, p. 27)
calls this "the most recent progress" on Thurston's question. The written proof was read
on 2026-09-16. Its steps are listed below with their status when "biautomatic" is
replaced by "automatic". The group-theoretic theorems it quotes (Kropholler, Kargapolov,
Robinson–Zaĭcev, Mal'cev, Gersten–Short) were not read in the primary sources. This
section is a map of the difficulty. No graph node rests on it except the Attempts
bullets.

- **(R1) Type `FP_∞`.** Romankov: "By [1], theorem 10.2.6, every soluble biautomatic
  group has type FP∞." For automatic groups this **survives**, by (Fin).
- **(R2) Finite virtual cohomological dimension.** Theorem 5.3 in Romankov (Kropholler):
  "If G is a soluble group of type FP∞ then vcd(G) < ∞." This is pure group theory and
  **survives**. It gives a finite-index subgroup `H` with `cd H < ∞`. So `H` is
  torsion-free and its free abelian subgroups have bounded rank (Romankov, Lemma 5.4).
  `H` is automatic by (FI).
- **(R3) Minimax structure.** Kargapolov gives finite rank. Robinson–Zaĭcev gives
  minimax. A torsion-free soluble minimax group is nilpotent-by-(virtually abelian). All
  of this is group theory and **survives**. So `H` has a nilpotent normal subgroup `N`
  with `H/N` virtually abelian.
- **(R4) `N` is abelian.** Suppose not. Take `y ∈ ζ_2(N) \ ζ_1(N)` and `u ∈ N` with
  `z = [u, y] ≠ 1`. Romankov writes `z ∈ ζ_1(H)`. What the argument gives, and needs, is
  `z ∈ ζ_1(N)`, so `z` commutes with `u` and `y`. Then `⟨u, y⟩` is a quotient of the
  Heisenberg group `UT_3(Z)` in which the image of its central generator has infinite
  order (`H` is torsion-free). Every nontrivial normal subgroup of `UT_3(Z)` meets the
  centre nontrivially, so the quotient map is injective and `⟨u, y⟩ ≅ UT_3(Z)`. The
  biautomatic input is Gersten–Short: every polycyclic subgroup of a biautomatic group is
  virtually abelian. This **fails** for automatic groups. This lane knows no theorem that
  excludes `UT_3(Z)` as an infinite-index subgroup of an automatic group. (Nil) covers
  only nilpotent groups that are themselves automatic.
- **(R5) `H` is polycyclic.** Romankov: `H` "satisfies to the minimal condition for
  centralizers", then "By [3] each biautomatic group with this property satisfies to the
  maximal condition on abelian subgroups. By Mal'cev's theorem (see [5]) a soluble group
  with this condition is polycyclic." This **fails** for automatic groups. Both the
  minimal condition on centralizers and its consequence use the biautomatic theory of
  centralizers.
- **(R6) Polycyclic ⇒ virtually abelian.** Gersten–Short again. For automatic groups a
  replacement exists: Rees (p. 14) says Thurston's conjecture "was proved for automatic
  polycylic groups in [39]", where [39] is A. Harkins, *Combing lattices of soluble Lie
  groups*, PhD thesis, University of Newcastle, 2001. The thesis was not read. Rees
  describes the method as embedding a finite-index subgroup as a lattice in a Lie group
  and applying ECHLPT Theorem 10.3.5 on higher-dimensional isoperimetric functions.

**Consequence.** (R4) is not needed once `H` is polycyclic. The essential missing input
for automatic groups is therefore (R5). Precisely, given (FI) and Harkins' theorem, (S) is
equivalent to

- (P) = `soluble-automatic-groups-are-polycyclic`: every finitely generated soluble
  automatic group is polycyclic.

*Proof.* Assume (P) and let `G` be soluble and automatic. Then `G` is polycyclic, and
Harkins' theorem makes it virtually abelian. This step does not use (FI). Conversely,
assume (S). A finitely generated virtually abelian group `G` has a normal abelian
subgroup `B` of finite index, namely a normal core. `B` is finitely generated, hence
polycyclic. `G/B` is finite, and it is soluble when `G` is. Extensions of polycyclic
groups by finite soluble groups are polycyclic. So `G` is polycyclic. ∎

By Mal'cev's theorem as quoted, (P) holds exactly when every abelian subgroup of a
soluble automatic group is finitely generated. A polycyclic group has all subgroups
finitely generated. Conversely, if all abelian subgroups are finitely generated, then
the maximal condition on abelian subgroups holds, because a union of a chain of abelian
subgroups is abelian.

## 8. Other approaches and where they die

- **Dehn function.** Automatic groups have quadratic Dehn function (Rees, Proposition
  2.1). This does not exclude a counterexample to (P). De Cornulier–Tessera,
  arXiv:1003.0148 (abstract page read 2026-09-16; the PDF fetch failed), write: "we embed
  the solvable Baumslag-Solitar groups into finitely presented metabelian groups with
  quadratic Dehn function. Also, we prove that Baumslag's finitely presented metabelian
  groups, in which the lamplighter groups embed, have quadratic Dehn function." So
  finitely presented, non-polycyclic metabelian groups with quadratic Dehn function
  exist. The lamplighter examples are not of type `FP_∞`, because by (R2) a soluble
  `FP_∞` group is virtually torsion-free and so has no infinite torsion subgroup. Whether
  the Baumslag–Solitar-containing examples are of type `FP_∞` was not checked. So no
  Dehn function argument for (P) is available to this lane. For the hole itself the Dehn
  function is already dead: see the 2026-09-13 bullet in its Attempts, on higher
  Heisenberg groups.
- **Growth.** Theorem 4 excludes subexponential growth. Every non-virtually-nilpotent
  soluble group has exponential growth (Milnor–Wolf, `gromov-and-milnor-wolf-growth-alternatives`),
  so growth says nothing more about (S).
- **Subgroup distortion.** A counterexample to (P) contains a non-finitely-generated
  abelian subgroup. In the metabelian model cases such as `BS(1,n)` this comes with an
  exponentially distorted cyclic subgroup. If automatic groups had undistorted cyclic
  subgroups, those model cases would be excluded. This lane knows that property only for
  biautomatic groups (Gersten–Short, from memory) and did not establish it for automatic
  groups. The de Cornulier–Tessera embeddings above show that `BS(1,n)` is a subgroup of
  a group with quadratic Dehn function, so distortion is not controlled by the Dehn
  function either.
- **(EA) from amenability.** No mechanism is known that makes an amenable group of type
  `F_∞` elementary amenable (see the Attempts of
  `every-f-infinity-amenable-group-is-elementary-amenable`). Automaticity adds a regular
  normal form and the fellow traveller property. This lane found no way to turn Følner
  sets and those properties into a finite subnormal series with elementary amenable
  factors.
