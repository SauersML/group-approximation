# Referee report (gq-referee-a, proof-gap lens): residually finite hosts cannot realize branch substitutions, and spine hosts reduce to finitely presented residually finite overgroups of the lamp

**Reviewed** (lane bh-self-similar, 264d89930), read on origin/main, with the proofs inline:
- `rf-hosts-cannot-realize-branch-substitutions`;
- `spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp`.

**Verdict: PASS for both.** There are two nits on the first node and three on the second.
- For the citation lens:
  - Basilica is weakly branch over `B'`, and the Bartholdi–Virág `σ` is an injective endomorphism;
  - Grigorchuk's `Γ` is branch over `K`;
  - no finitely presented residually finite group containing `Γ` is known (the "real barrier" paragraph).

## 1. `rf-hosts-cannot-realize-branch-substitutions` (the author asked about each step)
- **`G = (t^(−1)Gt)K`, so `K ⊄ St(1)`.**
  - `φ(t)^(−1)φ(G)φ(t) ⊆ φ(G)`, conjugation is injective, and `φ(G)` is finite, so this is an equality.
  - For `g ∈ G`, pick `g' ∈ t^(−1)Gt ⊆ G` with `φ(g') = φ(g)`. Then `g'^(−1)g ∈ G ∩ ker φ = K`, so
    `G = (t^(−1)Gt)K ⊆ St_G(1)K`.
  - `G ≠ St_G(1)`, since `G` is transitive on `X` and `|X| ≥ 2`. So some `k ∈ K` moves some letter `x` (N1). ✓
- **One rigid copy becomes abelian.**
  - `kι_x(ℓ)k^(−1) = ι_(k(x))(k|_xℓk|_x^(−1))`, with `k|_x ∈ G` normalizing `L`, and `ι_y(L) ⊆ G`.
  - `φ(k) = 1`, so `φ(ι_x(ℓ)) = φ(ι_y(m))` with `y ≠ x`, and `ι_y(m)` commutes with every `ι_x(ℓ')`. So
    `φ(ι_x(L))` is abelian. ✓
- **All rigid copies.** `gι_x(L)g^(−1) = ι_(g(x))(g|_xLg|_x^(−1)) = ι_(g(x))(L)`, and `G` is transitive.
- **The conclusion.**
  - `φ` kills `ι_(x')([L,L])`, which is nontrivial because `ι_(x')` is injective and `L` is non-abelian.
  - Groups acting faithfully on locally finite rooted trees are residually finite. ✓
  - No torsion is used, and nothing about `H` beyond `t`.
- **The instances.**
  - *Grigorchuk.* `K = ⟨⟨(ab)²⟩⟩` is non-abelian with `ι_x(K) ⊆ K ⊆ Γ`, and `σ(Γ) ⊆ St_Γ(1)` because
    `σ(a) = aca`. In `Γ̃`, `tΓt^(−1) = σ(Γ)`, so the node's element "`t`" is `t^(−1)` (N2).
  - The theorem then makes item 2 of `rf-hosts-cannot-realize-the-lysenok-substitution` independent of Sapir–Wise.
    Any `P ⊇ Γ` realizing `σ` is not residually finite, even without its item 1.
  - *Basilica.* `σ(a) = b²` and `σ(b) = a` both lie in `St(1)`, and `B'` is non-abelian. So `B̃` is not residually
    finite, given the cited weak-branch fact. ✓
  - *Last-section substitutions.* Covered, provided `σ` is an endomorphism into `St(1)` of a transitive group that
    is weakly branch at level 1.

## 2. `spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp`
- **Item 1: `L_y ≅ G_(y^ω)` (the author asked about this).**
  - `L_y` is a group, since `(gh)|_y = g|_(h(y))h|_y = gh`.
  - Its elements fix `y^ω`, so the germ map on `L_y` is a homomorphism.
  - It is onto: by (Φ5), every germ is the germ of some `ŵ(p) ∈ L_y`.
  - It is injective: a trivial germ means `g` is trivial on some `y^kX^*`, and `g(y^kv) = y^kg(v)`, so `g = 1`.
  - Finite presentation then follows from the unconditional necessity for lift-presented actions. Finitely
    presented automaton groups are lift-presented trivially. ✓
- **Item 2: the adding-states lemma (the author asked about this).**
  - The retraction `s'' ↦ u_(s'')` sends relators to relators.
  - `M ∩ F(S)` is lift-closed in `F(S)`, because `S`-words have `S`-word sections. So it contains `N_S`.
  - Every `w ∈ N_(S'')` is congruent to `ρ(w) ∈ N_S` modulo the finitely many relators `s''^(−1)u_(s'')`. So
    `N_(S'') = M`. ✓
- **Item 2: transplant and saturation (the author asked about this).**
  - `B̂ ↪ B ≀ Sym(Y) ↪ K ≀ Sym(Y) ≤ P' = P ≀ Sym(Y)` are abstract embeddings, which is all the transplant uses.
  - A closed-path element is determined by three things: its action on `Z∖z`, where every letter then dies; its
    `Y'`-block element `q_w ∈ φ(B̂) ⊆ K'`; and `w|_z = w`. So `G_(z^ω) ↪ Sym(Z∖z) × K'`.
  - The saturating loops with germ data the generators of `Sym(Z∖z) × K'` are separated once their finitely many
    sections, which lie in `P'`, are added as states. The base group stays `P'` and remains lift-presented by the
    lemma.
  - The germ groups become `Sym(Z∖z) × K'`, which is finitely presented, so the separated criterion applies. ✓
- **Item 3 (the author asked about this).**
  - `L_z(G) ≤ L_z(G^+)` in the common action, and the latter is finitely presented by item 1.
  - For the spine group, `⟨ŝ_γ⟩ ≅ Γ` lies in `L_2(G)`, and inclusion is all the conclusion needs.
  - Item 2 then applies with `K = L_2(G^+)` and `P = G^+`, via abstract embeddings. ✓

## Nits
- **N1 (first node).** Write "`k` moves some letter `x`, and put `y = k(x)`". The proof then uses that `x`, and
  transitivity covers the others. As written, `x` is fixed before `k` is chosen.
- **N2 (first node, instances).** For the HNN extensions `Γ̃` and `B̃`, where `tgt^(−1) = σ(g)`, the element
  satisfying `t^(−1)Gt ⊆ St_G(1)` is `t^(−1)`. Say so, or state the hypothesis as `tGt^(−1) ⊆ St_G(1)`.
- **N3 (second node, item 2).** "`P` could be contracting" relies on contracting implying lift-presented, which is
  Theorem A's necessity half. Say so. The final Boone–Higman step uses its sufficiency half.
- **N4 (second node, saturation).** Say that the added section states, together with their inverses, are finitely
  many elements of `P'`: all sections of finitely many fixed words. So the base group is unchanged.
- **N5 (second node, item 3).** "It is all of it" is not needed. `⟨ŝ_γ⟩ ≅ Γ ≤ L_2(G)` suffices.
