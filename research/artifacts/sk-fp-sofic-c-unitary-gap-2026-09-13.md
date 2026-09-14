# sk-fp-sofic-c: a unitary gap firewall for finitely presented simple groups (2026-09-13)

Lane sk-fp-sofic-c, start (c): the question of a finitely presented infinite simple Kazhdan group that is sofic or hyperlinear
(`hyperlinear-fp-infinite-simple-kazhdan-group`). Everything below is unreviewed; review is queued with sk-verify-5.

## 0. Summary
- **Theorem U** (`fp-simple-groups-have-no-gapped-finite-unitary-models`). A hyperlinear approximation of a finitely presented
  infinite simple group cannot factor through unitary representations of finite groups with a uniform character-ratio gap at
  noncentral elements. The maps into the finite groups may be arbitrary.
- **Corollary C** (`fp-simple-groups-have-no-classical-group-unitary-models`). The same holds for every finite group whose
  commutator subgroup is quasi-simple classical (`GL_N(q)`, `SL_N(q)`, and the unitary, symplectic and orthogonal analogs), in
  any rank and over any field, with any representation. So it holds for any action of these groups as well. The gap comes
  from Larsen–Shalev–Tiep (`lst-quasisimple-classical-character-ratio-bound`), read from the source.
- **What it does not decide.** The question stays OPEN. Room is left in:
  - symmetric and alternating targets;
  - unbounded products of gapped groups;
  - finite groups with long chief series outside these families;
  - unitary models that do not factor through finite groups.

## 1. Theorem U
A family of finite groups `Q_k` is θ-gapped (θ < 1) if `|χ(q)| ≤ θχ(1)` for every nontrivial irreducible `χ` and every
noncentral `q`.

**Statement.** Let `S = ⟨X | R⟩` be finitely presented, infinite and simple. There are no:
- maps `φ_k : X → Q_k` into a θ-gapped family, and
- unitary representations `ρ_k`,

such that `x ↦ (ρ_k(φ_k(x)))_ω` extends to an injective homomorphism `S → ∏_ω (U(d_k), ‖·‖_2)`.

**Proof outline** (full text on the route):
1. Products along words: `Π(w̄) = (ρ_k(W_k(w)))_ω`.
2. Separation of one commutator `c = [x,y] ≠ e` bounds the trivial isotypic weight away from 1.
3. The gap then forces `‖ρ_k(q) − I‖_2² ≥ δ > 0` at every noncentral `q`. So the relator images `W_k(r)` are central for
   ω-almost all `k`.
4. That gives a homomorphism `S → Q_k/Z(Q_k)`, which is trivial because `S` is infinite simple. So `φ_k(X)` is central.
5. `W_k(c) = 1`, which contradicts separation.

**Strengthening at no cost.** For simple `S`, a nontrivial homomorphism into the ultraproduct is injective. So: *every
homomorphism `S → ∏_ω U(d_k)` induced through a θ-gapped family is trivial.* That is, such almost-homomorphisms are
asymptotically trivial. Compare the Stability-shortcut bullet on `hyperlinear-fp-infinite-simple-kazhdan-group`: one
nontrivial almost-homomorphism into symmetric groups already makes such an `S` sofic.

**Relation to the permutation firewall.** `gap-sofic-approximations-are-local-embeddings` (sk-fp-sofic-a; PASS by sk-verify-3)
uses a fixed-point gap at all nontrivial elements and concludes LEF for any countable group. Theorem U asks for the gap only
at noncentral elements, on irreducible constituents. It concludes directly for finitely presented infinite simple groups,
where the center is handled by the projective homomorphism in step 4.

## 2. The imported gap (read from the Annals PDF, pages 1889 and 1907)
Larsen, Shalev, Tiep, *The Waring problem for finite simple groups*, Ann. of Math. 174 (2011) 1885–1950,
doi:10.4007/annals.2011.174.3.10.
- **Theorem 1.2.1, verbatim.** "If Γ is a finite quasi-simple classical group over F_q and g ∈ Γ is an element of support at
  least N, then |χ(g)|/χ(1) < q^{−√N/481} for all 1_Γ ≠ χ ∈ Irr(Γ)."
- **Definition 4.1.1, verbatim.** "The support supp(g) of an element g ∈ GL_n(F) ⊂ GL_n(F̄) is the codimension of the largest
  eigenspace of g: supp(g) = inf_{λ∈F̄} codim ker(g − λ). The support of any element in a classical group G(F) is the support
  of its image under the natural representation ρ: G(F̄) → GL_n(F̄)."
- **Noncentral elements have support at least 1.** `supp(g) = 0` means `ρ(g)` is scalar. Then `[g,h] ∈ ker ρ ⊆ Z(Γ)` for all
  `h`, so `gZ(Γ)` is central in the simple nonabelian group `Γ/Z(Γ)`, and `g ∈ Z(Γ)`.
- **Gap.** With `N = 1`, `θ = 2^{−1/481}` works for all quasi-simple classical groups at once.
- **Recorded, not imported.** Gluck's bound as quoted by LST on p. 1907: 19/20 for `2 ≤ q < 43`, `1/(√q−1)` for `q ≥ 43`,
  for connected reductive groups with quasi-simple simply connected commutator subgroup. Read literally, it fails at linear
  characters of `GL_n`, so as quoted only its quasi-simple case is meaningful. The primary source was not opened. With it,
  exceptional groups of bounded rank would join Corollary C.

## 3. Corollary C (commutator subgroups quasi-simple classical)
1. `S` is perfect. Replace `X` by a finite set `X'` of commutators of words in `X` that generates `S`. Finite presentability does
   not depend on the finite generating set.
2. For `x' = [a,b]`, `W_k(x') ∈ [Q_k,Q_k]` and `Π(x') = (ρ_k(W_k(x')))_ω`. So the approximation factors through
   `φ'_k : X' → [Q_k,Q_k]` and `ρ_k` restricted there.
3. Apply Theorem U with `θ = 2^{−1/481}`.

Sofic approximations through actions are the special case of permutation representations.

## 4. Model tests
- **`SL_3(Z)`** (finitely presented, infinite, not simple): congruence quotients give sofic models through `SL_3(F_p)` on
  vectors. The theorem does not apply because simplicity fails. Step 4 breaks: the homomorphism to `PSL_3(F_p)` is onto.
- **`G_X`** (simple, not finitely presented): its LEF models use `SL_{3N}(F_2)` on vectors. Finite presentation fails, so
  step 4 has no finite relator set.
- **Trivial group:** not infinite.
- **Alternating groups on points:** not gapped, since 3-cycles have ratio `(n−4)/(n−1) → 1`. Symmetric targets stay allowed,
  as they must, because sofic groups have permutation models.
- **Abelian targets:** vacuously gapped. The theorem then says a nonabelian `S` has no models through representations of
  abelian groups, which is true.

## 5. Consequences for the candidates
- **Ring route** (`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`). A rank model into `M_N(F_q)` gives `F_q`-linear
  soficity, and the elementary generators map into `SL_{nN}(F_q)`. No representation of these groups upgrades that to
  hyperlinear models of a finitely presented `EL_n(R)/Z`. So the linear-to-sofic upgrade (Arzhantseva–Păunescu Q8.5 at this
  group) must pass through non-algebraic finite targets.
- **Binary Leavitt unit group** (finitely presented, simple, nonsofic; hyperlinear open). No hyperlinear models through finite
  classical groups. This agrees in spirit with main's finite-coefficient projective-gap artifacts on that node; I did not
  merge it there.
- **Caprace–Rémy lattices, Titz Mite–Witzel kernels (if simple):** same conclusion. Their natural finite quotients are absent
  anyway, since they are simple.

## 6. Novelty and limits
- **Novelty.** Theorem U is folklore-level: a minimum-distance observation plus a projective homomorphism. Corollary C combines
  it with a deep published bound. Checked only by grepping main (no web search); no earlier node states a unitary or
  character-ratio firewall for finitely presented simple groups.
- **Not covered:**
  - `GL_N(F_q)` targets whose relator images are not controlled beyond the commutator subgroup (handled in §3 through
    perfectness);
  - direct products `∏_{i≤m_k} Q_{k,i}` with `m_k → ∞`, which need a template argument like
    `simple-group-relator-templates-over-finite-simple-groups`;
  - symmetric groups.
- **Sharpest next target in this direction.** A trace-metric template theorem over products of gapped groups (bounded chief
  length) would reduce every finite-group hyperlinear model of a finitely presented infinite simple group to alternating
  constituents.
