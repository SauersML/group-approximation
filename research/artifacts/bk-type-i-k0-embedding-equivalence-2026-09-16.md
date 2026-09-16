# The type I case of Problem VII is the K_0-embedding problem for type I algebras

Swarm artifact, 2026-09-16.  Target: `stw99-problem-vii-blackadar-kirchberg`.
New nodes: `bk-type-i-stably-finite-algebras-are-qd`,
`type-i-qd-algebras-have-k0-embedding-property`,
`separable-ccr-algebras-are-quasidiagonal`,
`toeplitz-pair-algebra-is-qd-with-non-qd-irreps`, and the routes that cite this
file.

Contents.

- §0 Conventions, imported statements, standard facts (with citation status)
- §1 Lemma 1: separable CCR algebras are quasidiagonal
- §2 Lemma 3: the per-subgroup Brown--Dadarlat gluing step
- §3 Theorem A: four equivalent forms of the type I case
- §4 Corollaries: single-algebra form, and what is already covered
- §5 Example: the Toeplitz pair `T' = C*(S ⊕ S*)`
- §6 Attempts on the K_0-embedding property for type I algebras, and where they die
- §7 Relation to the existing graph

## §0 Conventions, imported statements, standard facts

All algebras are C\*-algebras.  `K` denotes the compact operators on a separable
infinite-dimensional Hilbert space.  `Ã` is the unitization of `A`, with a unit
adjoined even when `A` is unital.

**Stable finiteness.**  A unital algebra `D` is *finite* if every isometry in `D`
is a unitary.  `A` is *stably finite* if `M_n(Ã)` is finite for every `n`.  For
nonunital `A`, `K_0^+(A)` is the set of classes `[p]` of projections
`p ∈ M_∞(A)`; it lies inside `K_0(A) = ker(K_0(Ã) → Z)`.

**Quasidiagonality.**  A set `S ⊆ B(H)`, `H` separable, is *quasidiagonal* if
there are finite-rank projections `P_1 ≤ P_2 ≤ ...` with `P_n → 1` strongly and
`||[P_n, s]|| → 0` for every `s ∈ S`.  A separable algebra is *quasidiagonal*
(QD) if it has a faithful representation with quasidiagonal image.  This is
Voiculescu's definition as used by Brown--Ozawa, *C\*-algebras and
finite-dimensional approximations*, Chapter 7 (definition numbers not
re-checked).

**Type I.**  `A` is *CCR* (liminal) if `π(A) ⊆ K(H_π)` for every irreducible
representation `π`; then `π(A) = K(H_π)`.  `A` is *type I* (postliminal, GCR)
if every nonzero quotient of `A` has a nonzero CCR ideal.

### Imported statements (already ESTABLISHED in the graph)

From `brown-dadarlat-ext-trivial-class-gives-qd-extension` and
`brown-dadarlat-qd-extensions-and-k0-hahn-banach` (N. P. Brown, M. Dadarlat,
arXiv:math/0008182).  The TeX source was re-read on 2026-09-16.  Compiled
numbering is used; the TeX labels are one lower after the unlabelled
suspension proposition.

- **BD-Sp (Prop 4.1, Spielberg [Sp, Lemma 1.5]).**  Let `0 → I → E → B → 0` be
  exact with `I` and `B` stably finite.  Then `E` is stably finite iff
  `∂(K_1(B)) ∩ K_0^+(I) = {0}`.
- **BD-3.4 (Theorem 3.4).**  Let `0 → I → E → B → 0` be exact with `E`
  separable, `I` QD, and `B` nuclear, QD and UCT.  If `∂ : K_1(B) → K_0(I)` is
  zero, then `E` is QD.
- **BD-Def (Definitions 4.3, 4.4).**  A QD algebra `A` has the *QD extension
  property* if, for every separable nuclear QD UCT algebra `B` and every Busby
  invariant `γ : B → Q(K ⊗ A)`, `E(γ)` is QD iff `E(γ)` is stably finite.  `A`
  has the *K_0-embedding property* if, for every subgroup `G ⊆ K_0(A)` with
  `G ∩ K_0^+(A) = {0}`, there is an embedding `ρ : A ↪ C` with `C` QD and
  `ρ_*(G) = 0`.
- **BD-4.6 (Proposition 4.6).**  A separable QD algebra has the QD extension
  property iff it has the K_0-embedding property.

A subgroup `G` with `G ∩ K_0^+(A) = {0}` is called *singular*.

### Standard facts used (textbook; theorem numbers NOT re-checked)

- **(T1)** Every type I algebra is nuclear.  (Blackadar, *Operator Algebras*,
  Section IV.3; Brown--Ozawa, Chapter 2.)
- **(T2)** Closed ideals and quotients of type I algebras are type I.  An
  extension of a type I algebra by a type I ideal is type I.  `A ⊗ K` is type I
  iff `A` is.  Every commutative algebra is type I.  (Dixmier, *C\*-algebras*,
  Chapter 4; Pedersen, *C\*-algebras and their automorphism groups*, Chapter 6.)
- **(T3)** A type I algebra `A` has a composition series `(I_α)_{α ≤ β}` of
  closed ideals: `I_0 = 0`, `I_β = A`, `I_{α+1}/I_α` is CCR, and
  `I_λ = closure(∪_{α<λ} I_α)` at limit ordinals `λ`.  Take `I_{α+1}/I_α` to be
  the largest CCR ideal of `A/I_α`.  (Dixmier Chapter 4; Pedersen Chapter 6.)
  If `A` is separable, `β` is countable: the open sets `Prim(I_α)` strictly
  increase in the second countable space `Prim(A)`.
- **(T4)** Separable type I algebras satisfy the UCT.  (Rosenberg--Schochet,
  Duke Math. J. 55 (1987); they lie in the bootstrap class.)
- **(Q1)** C\*-subalgebras of QD algebras are QD.  `A` is QD iff `K ⊗ A` is QD.
  The closure of an increasing union of QD subalgebras is QD.  QD algebras are
  stably finite.  `A` is QD iff `Ã` is.  (Brown--Ozawa, Chapter 7.)
- **(S1)** A C\*-subalgebra `D ⊆ A` of a stably finite algebra is stably finite.
  Proof: `D̃` embeds unitally in `Ã` as `D + C1`.  If `D` already contains a
  unit for itself, embed `D̃ = D ⊕ C` unitally in `Ã ⊕ C`, which is stably
  finite since `M_n(Ã ⊕ C) = M_n(Ã) ⊕ M_n`.  A unital subalgebra of a finite
  unital algebra is finite, because a non-unitary isometry stays non-unitary.
  Apply this to `M_n`.
- **(U1) UCT realisation of a prescribed boundary.**  Let `A` be separable and
  `G ⊆ K_0(A)` a subgroup, necessarily countable.  Then there is an exact
  sequence `0 → K ⊗ A → E → ⊕_N C(T) → 0`, with `E` separable, such that
  `∂(K_1(⊕_N C(T))) = G`.  Verbatim BD, proof of Prop 4.6: "Since abelian
  C\*-algebras satisfy the UCT we can construct an extension
  `0 → K⊗A → E → ⊕_N C(T) → 0`, such that `∂(K_1(⊕_N C(T))) = ∂(⊕_N Z) = G`."
  Mechanism: surjectivity of `Ext(⊕_N C(T), K ⊗ A) → Hom(K_1(⊕_N C(T)), K_0(A))`
  from the UCT.  Map the `n`-th generator of `⊕_N Z` to the `n`-th element of
  an enumeration of `G`.  The sign convention for `∂` is irrelevant since
  `G = −G`.
- **(K1)** `A` and `A ⊗ K` have the same `K_0` group and the same positive cone
  under the corner embedding `a ↦ e_11 ⊗ a`.  The map `K_0(A) → K_0(Ã)` is
  injective, and `K_0^+(Ã) ∩ K_0(A) = K_0^+(A)`: a projection `p ∈ M_n(Ã)` whose
  scalar part has rank `0` lies in `M_n(A)`.

## §1 Lemma 1: separable CCR algebras are quasidiagonal

**Lemma 1.**  Let `A` be separable.  Suppose `A` has a countable family of
representations `π_i : A → B(H_i)`, `i ∈ N`, with `H_i` separable,
`π_i(A) ⊆ K(H_i)` and `⊕_i π_i` faithful.  Then `⊕_i π_i(A)` is a quasidiagonal
set of operators on `H = ⊕_i H_i`, so `A` is QD.  In particular every separable
CCR algebra is QD, and so is stably finite.

*Proof.*
1. **CCR gives such a family.**  Take a dense sequence `(a_k)` in `A`.  For each
   `k, m` choose an irreducible `π_{k,m}` with
   `||π_{k,m}(a_k)|| > ||a_k|| − 1/m`.  Then `⊕ π_{k,m}` is isometric on a dense
   set, hence faithful.  Each `H_{k,m}` is separable because `A` is separable
   and `π_{k,m}` is irreducible.  CCR means `π_{k,m}(A) ⊆ K(H_{k,m})`.
2. **One compact operator.**  Fix `i`.  Choose finite-rank projections
   `Q_{i,1} ≤ Q_{i,2} ≤ ...` on `H_i` converging strongly to `1`.  If
   `dim H_i < ∞`, take `Q_{i,m} = 1`.  For compact `T ∈ K(H_i)`,
   `||Q_{i,m} T − T|| → 0` because strong convergence is uniform on the compact
   set `T(ball)`.  Taking adjoints, `||T Q_{i,m} − T|| → 0`.  Hence
   `||[Q_{i,m}, T]|| → 0`.
3. **The projections.**  Choose integers `m_1 ≤ m_2 ≤ ...` with `m_n ≥ n` and
   `||[Q_{i,m_n}, π_i(a_k)]|| < 1/n` for all `i ≤ n` and `k ≤ n`.  This is a
   finite list of conditions for each `n`, each achievable by step 2.  Put
   `P_n = (⊕_{i ≤ n} Q_{i,m_n}) ⊕ 0`.
4. **Properties of `P_n`.**
   - `P_n` has finite rank, and `P_n ≤ P_{n+1}`.
   - For `ξ = (ξ_i) ∈ H`,
     `||(1 − P_n)ξ||² = Σ_{i ≤ n} ||(1 − Q_{i,m_n}) ξ_i||² + Σ_{i > n} ||ξ_i||²`.
     Every term tends to `0` and is bounded by `||ξ_i||²`, which is summable.
     So `P_n → 1` strongly.
   - `π = ⊕ π_i` is block diagonal and `P_n` is block diagonal, so
     `||[P_n, π(a_k)]|| = max_{i ≤ n} ||[Q_{i,m_n}, π_i(a_k)]|| < 1/n` for
     `n ≥ k`.
5. **All of `A`.**  For `a ∈ A`,
   `||[P_n, π(a)]|| ≤ 2||a − a_k|| + ||[P_n, π(a_k)]||`.  Choosing `k` first and
   then `n` large makes this small.  So `π(A)` is a quasidiagonal set with `π`
   faithful, and `A` is QD.  QD algebras are stably finite by (Q1).  ∎

*Status.*  Elementary and complete.  The statement is presumably folklore; no
source was checked for it.

*Remark.*  Lemma 1 needs `π_i(A) ⊆ K(H_i)`.  An irreducible representation
whose image merely *contains* `K(H)` does not suffice: the unilateral shift
generates the Toeplitz algebra, which contains `K` and is not QD.  §5 shows
that this matters inside quasidiagonal type I algebras.

*Consequence for the `T_1` case.*  A separable type I algebra with `T_1`
primitive ideal space is CCR.  Every primitive quotient is simple and type I,
hence `K(H)` or `M_n`.  (Standard; numbering not re-checked.)  So Lemma 1 settles
the type I part of `bk-t1-primitive-spectrum-case`, even without stable
finiteness.  The same conclusion also follows from
`bk-primitive-quotients-qd-or-traceless-force-qd`, since `K` and `M_n` are QD,
but Lemma 1 does not need nuclearity or stable finiteness.

## §2 Lemma 3: the per-subgroup Brown--Dadarlat gluing step

(No Lemma 2 is used; the numbering follows the notes.)

**Lemma 3 (per-subgroup form of BD-4.6, "if" direction).**  Let `A` be separable
and QD.  Let `0 → K ⊗ A → E → B → 0` be exact with `B` separable, nuclear, QD
and UCT.  Put `G = ∂(K_1(B)) ⊆ K_0(K ⊗ A) = K_0(A)`.  Suppose some embedding
`ρ : A ↪ C` into a QD algebra has `ρ_*(G) = 0`.  Then `E` is QD.

*Proof.*  This is the second half of the proof of BD Proposition 4.6,
quoted in the TeX source read 2026-09-16.  That argument uses the
K_0-embedding property exactly once: to produce `ρ` for this particular `G`.
Stable finiteness of `E` is used there only to see that `G` is singular, so
that the property applies.  Here `ρ` is given, so neither is needed.  The steps:

1. **Separable target.**  Since `G` is countable, `C` may be taken separable.
   Only countably many projections and partial isometries over `C` are needed
   to kill `ρ_*(G)`; BD make this remark verbatim.
2. **A nice ambient algebra.**  By the proof of BD Proposition 3.3 (citing
   Brown, Prop 5.2 of [Br3]), `C` embeds via some `π` into
   `D = Π_i M_{n_i} + K(H)`, where `H = ⊕_i C^{n_i}`.  `D` is QD: it consists
   of block-diagonal operators plus compacts.  Let `J ⊆ D` be the hereditary
   subalgebra generated by `πρ(A)`.  It is σ-unital, since a strictly positive
   element of `πρ(A)` is strictly positive for `J`.  `J` is QD, and the proof of
   BD Lemma 3.2 gives `K_1(J) = 0`.
3. **`G` dies in `J`.**  `D` has real rank zero and stable rank one.  So BD
   Lemma 4.5 makes `K_0(J) → K_0(D)` injective.  Since `(πρ)_*(G) = 0` in
   `K_0(D)`, also `(πρ)_*(G) = 0` in `K_0(J)`.
4. **Pushing the extension forward.**  `πρ : A → J` is approximately unital, so
   `K ⊗ A → K ⊗ J` is approximately unital too.  By the remarks after BD
   Definition 3.1 (imported in `brown-dadarlat-ext-trivial-class-gives-qd-extension`)
   there is an injective map of extensions
   `(0 → K⊗A → E → B → 0) → (0 → K⊗J → E(η) → B → 0)`, the identity on `B`.
   By naturality, `∂ : K_1(B) → K_0(K ⊗ J)` is `(πρ)_* ∘ ∂_E`, which is zero.
   Also `K_1(K ⊗ J) = 0`, so both index maps of `η` vanish.
5. **Quasidiagonality of `E(η)`.**  Follow the proof of BD Theorem 3.4 from its
   second sentence on.  Stabilise and tensor with the universal UHF algebra
   `U`.  Both index maps of `(η^s)^Q` vanish.  Divisibility of
   `K_0(J ⊗ K ⊗ U)` and the UCT for `B ⊗ K ⊗ U` then give `[(η^s)^Q] = 0` in
   Ext.  BD Proposition 2.5 (imported; it needs only a σ-unital ideal and a
   separable quotient) makes `E((η^s)^Q)` QD.  Finally
   `E ↪ E(η) ↪ E(η^s) ↪ E((η^s)^Q)`, and (Q1) gives that `E` is QD.  ∎

*Status.*  This is a re-reading of a published argument, not a new proof.  The
one point that differs from citing BD-4.6 as a black box is that the hypothesis
is used only for the single subgroup `G`.  Moutzouris makes the same per-subgroup
observation for his Proposition 3.2, where he notes that the proof never uses
singularity (see `moutzouris-k0-killing-is-local`, item 2).

**Stabilisation remark.**  Let `0 → I → E → B → 0` be exact with `I` separable
and QD, `B` separable, nuclear, QD and UCT, and `E` separable.  Tensoring with
`K` gives `0 → K⊗I → K⊗E → K⊗B → 0`.  `K ⊗ B` is again separable, nuclear, QD
and UCT, and the boundary image is the same subgroup of `K_0(I)`.  If Lemma 3
applies to the stabilised sequence (with `A = I`), then `K ⊗ E` is QD, and so is
`E ≅ e_11 ⊗ E` by (Q1).

## §3 Theorem A: four equivalent forms of the type I case

**Theorem A.**  The following are equivalent.

- **(a)** Every separable stably finite type I algebra is QD.
- **(b)** Every separable QD type I algebra has the K_0-embedding property.
- **(c)** Let `A` be separable, QD and type I, and let
  `0 → K ⊗ A → E → ⊕_N C(T) → 0` be exact.  Then `E` is QD iff `E` is stably
  finite.
- **(e)** Let `A` be separable, QD and type I, and let `x ∈ K_0(A)` satisfy
  `Zx ∩ K_0^+(A) = {0}`.  Then some embedding of `A` into a QD algebra kills `x`.

Two preliminary observations.

- **(O1)** Every extension `0 → I → E → B → 0` is isomorphic to `E(γ)` for its
  Busby invariant `γ`.  The map `e ↦ (σ(e), q(e)) ∈ M(I) ⊕_{Q(I)} B` is
  injective: if `σ(e) = 0` and `q(e) = 0`, then `e ∈ I` and `eI = 0`, so
  `ee* = 0`.  It is surjective: given `(m, b)`, lift `b` to `e` and subtract
  `σ(e) − m ∈ I`.
- **(O2)** Commutative algebras are stably finite, since their unitizations are
  commutative.  QD algebras are stably finite (Q1).

*Proof of (a) ⇒ (c).*  `K ⊗ A` is type I and `⊕_N C(T)` is commutative, so `E`
is separable and type I by (T2).  QD implies stably finite (Q1).  Conversely,
if `E` is stably finite then (a) makes it QD.  ∎

*Proof of (c) ⇒ (b).*
1. Let `A` be separable, QD and type I, and `G ⊆ K_0(A)` singular.  By (U1)
   there is an exact sequence `0 → K⊗A → E → ⊕_N C(T) → 0` with
   `∂(K_1(⊕_N C(T))) = G`.
2. `K ⊗ A` is QD, hence stably finite.  `⊕_N C(T)` is stably finite by (O2).
   By (K1), `G ∩ K_0^+(K ⊗ A) = G ∩ K_0^+(A) = {0}`.  So BD-Sp makes `E` stably
   finite, and (c) makes `E` QD.
3. Let `ρ : A → E` be `a ↦ e_11 ⊗ a` followed by the inclusion `K ⊗ A ⊆ E`.  It
   is injective.  The six-term sequence is exact at `K_0(K ⊗ A)`:
   `K_1(⊕_N C(T)) --∂--> K_0(K ⊗ A) --ι_*--> K_0(E)`.  So `ker ι_* = G`.  Since
   `K_0(A) → K_0(K ⊗ A)` is the canonical isomorphism, `ρ_*(G) = 0`.  So `ρ`
   witnesses the K_0-embedding property for `G`.  ∎

This is the easy half of BD Proposition 4.6, with `B = ⊕_N C(T)`.  The only new
point is that the extension it builds is again type I.

*Proof of (b) ⇒ (e).*  Take `G = Zx`.  ∎

*Proof of (e) ⇒ (b).*
1. **Setup.**  Let `A` and `G` be as in (b), and enumerate `G = {g_1, g_2, ...}`
   (repetitions allowed; `G = 0` is trivial).  By (U1), choose
   `0 → K⊗A → E --q--> ⊕_N C(T) → 0` with `∂(e_n) = g_n`, where `e_n` generates
   `K_1` of the `n`-th summand.
2. **The ideals `E_n`.**  Let `E_n = q^{-1}(⊕_{k ≤ n} C(T))`, so
   `E_0 = K ⊗ A`.  These are increasing closed ideals.  `∪ E_n` is dense in `E`:
   if `q(e) = b` and `b_n` is the truncation of `b` to the first `n` summands,
   lift `b − b_n` to `y` with `||y|| ≤ ||b − b_n|| + ε`; then `e − y ∈ E_n`.
3. **Stable finiteness.**  `E` is stably finite by BD-Sp, as in the proof of
   (c) ⇒ (b), so every `E_n` is stably finite by (S1).  Each `E_n` is separable
   and type I by (T2).
4. **Induction.**  `E_0 = K ⊗ A` is QD.  Suppose `E_{n−1}` is QD.
   - `E_n / E_{n−1} ≅ C(T)`, giving `0 → E_{n−1} → E_n → C(T) → 0`.
   - All three terms are stably finite, so by BD-Sp the cyclic group
     `Zx_n = ∂(K_1(C(T))) ⊆ K_0(E_{n−1})` meets `K_0^+(E_{n−1})` only in `0`.
   - By (e) for `E_{n−1}`, some embedding of `E_{n−1}` into a QD algebra kills
     `x_n`, hence kills `Zx_n`.
   - The stabilised sequence `0 → K⊗E_{n−1} → K⊗E_n → K⊗C(T) → 0` has boundary
     image `Zx_n` under `K_0(K ⊗ E_{n−1}) = K_0(E_{n−1})`.  `K ⊗ C(T)` is
     separable, nuclear, QD and UCT.
   - Lemma 3 (with `A = E_{n−1}`) makes `K ⊗ E_n` QD, hence `E_n` QD by (Q1).
5. **Conclusion.**  `E = closure(∪ E_n)` is QD by (Q1).  The embedding
   `ρ : A → E_0 ⊆ E` kills `G` as in step 3 of (c) ⇒ (b).  ∎

This is BD's proof of `4 ⇒ 2` in their Theorem 4.11, rerun inside the class of
type I algebras.  BD's remark after Theorem 4.12 asserts exactly this
transfer, for any class closed under extensions of abelian algebras by stabilised
members.  Separable type I algebras form such a class by (T2).

*Proof of (b) ⇒ (a).*
1. **Setup.**  Let `E` be separable, stably finite and type I, with composition
   series `(I_α)_{α ≤ β}` from (T3), `β` countable.  We show by transfinite
   induction that every `I_α` is QD.
2. **`α = 0`.**  Trivial.
3. **Limit `λ`.**  Choose `α_1 < α_2 < ...` cofinal in `λ`.  Then
   `I_λ = closure(∪_n I_{α_n})` is an increasing union of QD subalgebras, hence
   QD by (Q1).
4. **Successor `α + 1`.**
   - `I_α` is separable, QD (induction) and type I (T2).
   - `B := I_{α+1}/I_α` is separable and CCR.  So it is QD and stably finite
     (Lemma 1), nuclear (T1) and UCT (T4).
   - `I_{α+1}` is stably finite, being a subalgebra of `E` (S1).
   - By BD-Sp, `G_α := ∂(K_1(B)) ⊆ K_0(I_α)` is singular.
   - Stabilise: `0 → K⊗I_α → K⊗I_{α+1} → K⊗B → 0`.  Its boundary image is `G_α`
     under `K_0(K ⊗ I_α) = K_0(I_α)`, still singular by (K1).  `K ⊗ B` is
     separable, nuclear, QD and UCT.  `K ⊗ I_α` and `K ⊗ B` are QD, hence stably
     finite.  BD-Sp shows that `K ⊗ I_{α+1}` is stably finite.
   - By (b), `I_α` has the K_0-embedding property.  By BD-4.6 it has the QD
     extension property.  By (O1), `K ⊗ I_{α+1} ≅ E(γ)` for the Busby invariant
     `γ : K ⊗ B → Q(K ⊗ I_α)`.  The QD extension property makes `K ⊗ I_{α+1}`
     QD, hence `I_{α+1}` QD by (Q1).
   - Alternatively, apply Lemma 3 directly to the subgroup `G_α`.
5. **Conclusion.**  `E = I_β` is QD.  ∎

**Addendum (d), the K_0-Hahn--Banach form.**  (a)--(e) are also equivalent to:

- **(d)** Every separable QD type I algebra has the K_0-Hahn--Banach property
  (BD Definition 4.8).

BD Theorem 4.12 (TeX label 4.11, read 2026-09-16) says, for a single separable
nuclear QD algebra, `1 ⇔ 2 ⇒ 3 ⇔ 4 ⇔ 5`.  Here 2 is the K_0-embedding property,
3 is the Hahn--Banach property and 4 is statement (e) for that algebra.  Type I
algebras are nuclear (T1).  So (b) ⇒ (d) is `2 ⇒ 3`, and (d) ⇒ (e) is `3 ⇒ 4`.
This addendum relies on BD Theorem 4.12, which is not yet an imported node.  The
graph imports only the class version, Theorem 4.11.

**What is new.**  (b) ⇔ (e) ⇔ (d) is the type I instance of BD's class remark
and their individual theorem.  (a) ⇒ (c) ⇒ (b) is the easy half of BD 4.6.  The
new ingredient is (b) ⇒ (a).  Lemma 1 makes every composition factor of a type
I algebra a legitimate UCT quotient for the Brown--Dadarlat gluing step, and
stable finiteness passes to the ideals `I_{α+1}`.  So the type I case of
Problem VII is *exactly* the K_0-embedding problem for type I QD algebras.

## §4 Corollaries

**Corollary B (single-algebra form).**  Let `E` be separable and type I with
composition series `(I_α)_{α ≤ β}` as in (T3).  Write
`G_α = ∂(K_1(I_{α+1}/I_α)) ⊆ K_0(I_α)`.  Suppose that for every `α < β` with
`I_α` QD, some embedding of `I_α` into a QD algebra kills `G_α`.  Then `E` is
QD.

*Proof.*  Run the induction of (b) ⇒ (a), using Lemma 3 in step 4 in place of
BD-4.6.  Stable finiteness of `E` is not needed: it only served to make `G_α`
singular, and the hypothesis supplies the killing embedding directly.  ∎

- **B1.**  If every `G_α` is zero, `E` is QD, with no finiteness hypothesis.
  This happens, for example, if `K_0(I_α) = 0` or `K_1(I_{α+1}/I_α) = 0` for all
  `α`.  In that case BD-3.4 applies directly at each successor step.
- **B2.**  Suppose `E` is stably finite and the successive boundary maps are
  killed along the series.  For instance, suppose every `I_α` with `α < β` has
  the K_0-embedding property.  Examples where this is known:
  - `I_α ⊗ K ≅ C_0(X) ⊗ K`;
  - `I_α` AF;
  - `I_α` in Moutzouris' class `Y`, or locally approximated by such algebras.

  Then `E` is QD.  For commutative algebras BD assert the embedding property in
  the text after Definition 4.4, without proof.  The AF case is Spielberg's
  Lemma 1.14 (not fetched).  Class `Y` is imported as
  `moutzouris-qd-extensions-y-class`, and approximation is covered by
  `moutzouris-k0-killing-is-local`.  Stable isomorphism invariance is checked in
  §6.1.
- **B3 (`T_1` spectra).**  A separable type I algebra with `T_1` primitive
  spectrum is CCR, hence QD by Lemma 1.  Its composition series has length one.

**Why the induction cannot be run from the top.**  One might try to glue from
the top quotient `E/I_α` downwards.  But quotients of stably finite type I
algebras need not be stably finite: `T'/(0 ⊕ K) ≅` Toeplitz algebra in §5.  So
the induction must climb through the ideals, as above.  Ideals inherit stable
finiteness (S1); quotients do not.

## §5 Example: the Toeplitz pair `T' = C*(S ⊕ S*)`

Let `S` be the unilateral shift on `ℓ²(N)` with basis `(ξ_n)_{n ≥ 0}`.  Let
`T = C*(S)` be the Toeplitz algebra and `q : T → C(T)` the symbol map, with
`q(S) = z`.  Put `e_0 = 1 − SS*`, the projection onto `Cξ_0`.  Let
`V = S ⊕ S*` on `ℓ²(N) ⊕ ℓ²(N)` and `T' = C*(V)`.

**Proposition C.**  `T'` is separable, quasidiagonal (hence stably finite) and
type I.  Every separating family of irreducible representations of `T'` contains
the two coordinate representations
`π_1(a, b) = a` and `π_2(a, b) = b`.  Their images are both `T`, which is not
finite, not quasidiagonal and not traceless.  Consequently:

- (i) `T'` has primitive quotients that are neither QD nor traceless, so
  `bk-primitive-quotients-qd-or-traceless-force-qd` does not reach `T'`;
- (ii) the quotient `T'/(0 ⊕ K) ≅ T` of the stably finite algebra `T'` is not
  stably finite;
- (iii) `T'` has no separating family of irreducible representations whose
  images are quasidiagonal sets, or quasidiagonal algebras.

*Proof.*

1. **`K ⊕ K ⊆ T'`.**
   - `V*V = 1 ⊕ SS*` and `VV* = SS* ⊕ 1`.  So `V*V − VV* = e_0 ⊕ (−e_0)`, and
     its square `p = e_0 ⊕ e_0` lies in `T'`.
   - Since `S* ξ_0 = 0`, `Vp = Se_0 ⊕ 0`.  Hence `(Vp)*(Vp) = e_0 ⊕ 0` lies in
     `T'`, and so does `0 ⊕ e_0 = p − (e_0 ⊕ 0)`.
   - `V^k (e_0 ⊕ 0) V^{*l} = S^k e_0 S^{*l} ⊕ 0`, which ranges over the matrix
     units of `K(ℓ²(N)) ⊕ 0`.
   - `V^{*k} = S^{*k} ⊕ S^k`, so `V^{*k} (0 ⊕ e_0) V^l = 0 ⊕ S^k e_0 S^{*l}`.
   - So `K ⊕ K ⊆ T'`.
2. **`T'` is a pullback.**  Let `σ(f)(λ) = f(λ̄)`.  `T'` is contained in
   `P = {(a, b) ∈ T ⊕ T : q(a) = σ(q(b))}`, a C\*-algebra containing `V`, since
   `σ(q(S*)) = σ(z̄) = z`.  Conversely, `(a, b) ↦ q(a)` maps `T'` onto
   `C*(z) = C(T)`.  For `(a, b) ∈ P`, pick `c ∈ T'` with the same image.  Then
   `(a, b) − c ∈ P` has both symbols zero, so it lies in `K ⊕ K ⊆ T'`.  So
   `T' = P`, and there is an exact sequence
   `0 → K ⊕ K → T' → C(T) → 0`.
3. **Type I.**  This is an extension of a commutative algebra by `K ⊕ K`, so
   `T'` is type I by (T2).  It is separable.
4. **Quasidiagonal.**
   - Identify `ℓ²(N) ⊕ ℓ²(N)` with `ℓ²(Z)` by `ξ_n ⊕ 0 ↦ f_n` and
     `0 ⊕ ξ_n ↦ f_{−n−1}`.
   - Then `V f_n = f_{n+1}` for `n ≠ −1`, and `V f_{−1} = 0`.  So
     `V = W − f_0 ⊗ f_{−1}*`, where `W` is the bilateral shift.
   - `W` is normal.  By the Weyl--von Neumann--Berg theorem (Berg, Trans. AMS
     160 (1971); Davidson, *C\*-algebras by Example*, Section II.4; numbering not
     re-checked), `W = D + K_0` with `D` diagonal in some orthonormal basis
     `(h_j)` and `K_0` compact.
   - So `V = D + K_1` with `K_1` compact.  Let `P_n` project onto
     `span{h_1, ..., h_n}`.  Then `[P_n, D] = 0` and `||[P_n, K_1]|| → 0` (§1,
     step 2).  So `||[P_n, V]|| → 0`, and also `||[P_n, V*]|| → 0`.
   - The commutator is a derivation, so `||[P_n, x]|| → 0` for every
     \*-polynomial `x` in `V`.  By density this holds for every `x ∈ T'`.
   - The identity representation of `T'` is faithful, so `T'` is QD.
5. **Irreducible representations.**
   - An irreducible representation of `T'` that is nonzero on the ideal
     `J = K ⊕ K` is the unique extension of an irreducible representation of `J`,
     so it is `π_1` or `π_2`.  (Standard; e.g. Arveson, *An Invitation to
     C\*-algebras*, Section 1.3; numbering not re-checked.)
   - The others factor through `C(T)`, so they are characters and vanish on `J`.
   - `e_0 ⊕ 0` is killed by `π_2` and by every character, so a separating family
     contains `π_1`.  Symmetrically it contains `π_2`.
6. **The images.**
   - `π_1(T') = C*(S) = T` and `π_2(T') = C*(S*) = T`.
   - `T` contains the non-unitary isometry `S`, so it is not finite, hence not
     QD (Q1).
   - `τ(a) = ∫ q(a) dλ` is a tracial state on `T`, so `T` is not traceless.
   - `ker π_1 = 0 ⊕ K`, so `T'/(0 ⊕ K) ≅ T`.
   - If `π_1(T')` were a quasidiagonal set of operators, `T` would be QD.  This
     gives (i)--(iii).  ∎

*Boundary.*  The lift `V` of `z` has Fredholm components of index `−1` and
`+1`, so `∂([z]) = ±(−1, 1) ∈ K_0(K ⊕ K) = Z²`.  This class has mixed signs, so
`∂(K_1) ∩ K_0^+ = {0}`, as BD-Sp requires for a stably finite `T'`.  So `T'` is
the simplest stably finite type I extension with a *nonzero* singular boundary.
Its quasidiagonality is genuinely non-fibrewise: it comes from the reducible
representation on `ℓ²(Z)`, where the two Toeplitz halves recombine into a
bilateral shift.

*Relation to `bk-radical-projection-quotients-are-toeplitz-infinite`.*
Corollary 10 there says the obstruction in a type I counterexample sits at
"Toeplitz-like" points.  `T'` shows that such points occur in quasidiagonal
algebras too, so their presence is not by itself an obstruction.  The
distinction must be K-theoretic.  That is what Theorem A isolates.

*Status of the "inner QD" formulation (abstract only).*  Blackadar--Kirchberg,
*Inner quasidiagonality and strong NF algebras* (arXiv:0711.4949; published in
Pacific J. Math.), prove that "a separable C\*-algebra is inner quasidiagonal if
and only if it has a separating family of quasidiagonal irreducible
representations".  This quotes the abstract, read 2026-09-16.  An ar5iv
rendering of the body was then skimmed by an automated query.  It reports no
statement about type I, CCR or residually stably finite algebras, and no
explicit definition of "quasidiagonal irreducible representation".  The paper
refers to earlier examples [BK01] of NF algebras that are not strong NF.  If
"quasidiagonal irreducible representation" means that the image is a
quasidiagonal set of operators, then (iii) says `T'` is QD but not inner QD,
so `T'` is not a strong NF algebra.  Nothing above depends on this.

## §6 Attempts on the K_0-embedding property for type I algebras

### 6.1 Reductions (complete)

- **Stable isomorphism.**  Suppose `A ⊗ K ≅ B ⊗ K` and `B` has the
  K_0-embedding property.  Then so does `A`.
  - Let `G ⊆ K_0(A)` be singular.  By (K1) its image `G'` in
    `K_0(A ⊗ K) ≅ K_0(B ⊗ K) ≅ K_0(B)` is singular, since isomorphisms preserve
    positive cones.
  - Choose `ρ : B ↪ C` with `C` QD and `ρ_*(G') = 0`.
  - The composite `A ↪ A ⊗ K ≅ B ⊗ K --ρ⊗id--> C ⊗ K` is injective, lands in a
    QD algebra, and kills `G`.
- **Unitization.**  If `Ã` has the K_0-embedding property, so does `A`.  By
  (K1) a singular `G ⊆ K_0(A)` is singular in `K_0(Ã)`.  Restrict a killing
  embedding of `Ã` to `A`.  `Ã` is type I and QD when `A` is.  So (b) reduces
  to unital `A`.
- **Finitely generated subgroups, locality.**  For unital `A`,
  `moutzouris-k0-killing-is-local` (Moutzouris Props 3.3, 3.5) reduces (b) to
  finitely generated singular subgroups.  It also shows that the embedding
  property passes to algebras locally approximated by algebras that have it.

### 6.2 Lemma 4: killing through irreducible representations of CCR algebras

Let `A` be separable and CCR, and `x ∈ K_0(A)`.  For `π ∈ Â` put
`r_x(π) = π_*(x) ∈ K_0(K(H_π)) = Z`, the *rank function* of `x`.

**Lemma 4.**  Suppose (i) `Z_x = {π : r_x(π) = 0}` is dense in `Â`, or (ii) `r_x`
takes both a positive and a negative value.  Then there are asymptotically
multiplicative, asymptotically isometric c.c.p. maps `φ_n : A → M_{k_n}` with
`(φ_n)_*(x) = 0` for large `n`.  Hence some embedding of `A` into a QD algebra
kills `x`.

*Proof sketch.*

1. **Compressions.**  For `π ∈ Â` and finite-rank `Q_m ↑ 1`, the maps
   `φ_m = Q_m π(·) Q_m` are c.c.p.
   - They are asymptotically multiplicative:
     `||φ_m(ab) − φ_m(a)φ_m(b)|| ≤ ||[Q_m, π(a)]|| ||b||`, which tends to `0` by
     §1 step 2.
   - They are asymptotically norming: `||φ_m(a)|| → ||π(a)||`.
   - For large `m`, `(φ_m)_*(x) = r_x(π)`.  This is the standard identification
     of `K_0(K)` with `Z` through ranks of compressions.  Write `x = [e] − [f]`
     with the same scalar part, perturb `π̃(e)` and `π̃(f)` to projections that
     differ from that scalar part by finite-rank operators, and compare ranks.
     This step is sketched, not written out.
2. **Norming families.**  For `a ∈ A`, the set `U_a = {π : ||π(a)|| > ||a|| − ε}`
   is open (lower semicontinuity of `π ↦ ||π(a)||`) and nonempty.  Given a
   finite `F ⊆ A`, choose `π_a ∈ U_a` for each `a ∈ F`.  In case (i), choose
   `π_a ∈ U_a ∩ Z_x`.
   - A direct sum of compressions of the `π_a` is almost multiplicative on `F`
     and almost isometric on `F`.  Its `K_0`-image of `x` is
     `s = Σ_a r_x(π_a)`.
   - In case (i), `s = 0`.
3. **Case (ii).**  The additive semigroup `S ⊆ Z` generated by `r_x(Â)` contains
   some `u > 0` and some `−w < 0`.  If `v ∈ S` and `v > 0`, then
   `−v = v·(−w) + (w − 1)·v ∈ S`; symmetrically for `v < 0`.  So `S` is a group.
   - Hence `−s = Σ_j n_j r_x(σ_j)` with `n_j ≥ 0` and `σ_j ∈ Â`.
   - Add `n_j` copies of compressions of `σ_j`.  Norms and multiplicativity on
     `F` are unaffected, since direct summands are contractive and almost
     multiplicative.
   - The total `K_0`-image is `0`.
4. **The sequence.**  Diagonalise over an increasing exhaustion `F_n` and
   `ε_n → 0`.  This gives the Hahn--Banach killing of `x`.
5. **An embedding.**  `A` is nuclear (T1).  BD's proof of `3 ⇒ 5 ⇒ 4` in
   Theorem 4.12 works one element at a time, and turns this into an embedding
   of `A` into a QD algebra killing `x`.  ∎

### 6.3 Where it dies

- **(α) One-signed rank functions with non-dense zero set.**
  - Take `A = C(S²) ⊕ C` and `x = (β, 1)`, where `β = [L] − [1]` is the Bott
    class.
  - `x` is singular.  Suppose `kx = [p]`.  Then `p = (p_1, p_2)` with
    `[p_1] = kβ`.  The rank of `p_1` is the rank of `kβ`, which is `0`.  So
    `p_1 = 0` and `kβ = 0`, forcing `k = 0`.
  - Here `r_x = 0` on `S²` and `1` at the isolated point, so `Z_x = S²` is not
    dense.
  - Every direct sum of compressions of irreducible representations that is
    almost isometric on `(0, 1)` uses the isolated point.  So it sends `x` to a
    positive integer.
  - Killing `x` therefore needs *non-representation* approximate morphisms
    `C(S²) → M_k` sending `β` to a negative integer: "fuzzy sphere"
    almost-representations with nonzero Bott index.  Their existence is
    standard folklore (Loring's work on almost commuting matrices; not
    re-checked).
  - BD state that commutative algebras have the embedding property, so this `x`
    *is* killable, but by a mechanism that the rank function cannot see.
  - For general CCR algebras no source of such twisted almost-representations
    is known.  The first test case not settled by 6.1 and Moutzouris' class `Y`
    would be a continuous-trace algebra with non-torsion Dixmier--Douady class
    and a singular class of the one-signed, non-dense type.  This was not
    analysed.
- **(β) Toeplitz points.**  Outside the CCR part, irreducible images contain
  `K` without being `K`.  By Proposition C this already happens in QD type I
  algebras.  Compressions of the shift are not asymptotically multiplicative:
  `(Q_m S Q_m)*(Q_m S Q_m) − Q_m S*S Q_m` has norm `1`.  So Lemma 4 has no analogue
  there, and killing maps must come from reducible representations.
- **(γ) Extensions.**  The natural attempt is to deduce (b) from its CCR case
  through the composition series.  That needs the K_0-embedding property to pass
  from `I` and `A/I` to `A`.  A singular `G ⊆ K_0(A)` need not come from
  `K_0(I)`, and its image in `K_0(A/I)` need not be singular.  No tool for this
  step is known.  It is the K-theoretic core of the gluing problem, so this
  attempt is circular.
- **(δ) Top-down induction.**  This dies by Proposition C (ii), as recorded in §4.

## §7 Relation to the existing graph

### 7.1 Nodes citing this file

- `separable-ccr-algebras-are-quasidiagonal` (claim), with the direct proof route
  `separable-ccr-algebras-are-quasidiagonal-proof` (`requires: []`): Lemma 1.
- `toeplitz-pair-algebra-is-qd-with-non-qd-irreps` (claim), with the direct proof
  route `toeplitz-pair-algebra-is-qd-with-non-qd-irreps-proof` (`requires: []`):
  Proposition C.
- `bk-type-i-stably-finite-algebras-are-qd` (claim, OPEN): statement (a).
- `type-i-qd-algebras-have-k0-embedding-property` (claim, OPEN): statement (b).
- Route `bk-type-i-case-via-k0-embedding`: (b) ⇒ (a), §3.  It requires (b),
  Lemma 1 and the Brown--Dadarlat imports (BD-4.6, or BD-3.4 via Lemma 3).
- Route `type-i-k0-embedding-from-type-i-case`: (a) ⇒ (b), §3, via (c).  It
  requires (a) and the Brown--Dadarlat imports (Spielberg's criterion and the
  UCT realisation (U1), both quoted in BD's proof of Proposition 4.6).
- Route `bk-type-i-case-from-uct-quotient-extensions`: the induction of
  (b) ⇒ (a), with the successor step supplied by
  `blackadar-kirchberg-for-uct-quotient-extensions`.  At a successor step, `I_α`
  is separable, nuclear (T1) and QD (induction).  `I_{α+1}/I_α` is separable,
  nuclear, QD (Lemma 1) and UCT (T4).  `I_{α+1}` is stably finite (S1).  So that
  claim makes `I_{α+1}` QD.  Limits are handled by (Q1).

### 7.2 Where the new claims sit

- **Below Problem VII.**  Type I algebras are nuclear (T1).  So
  `stw99-problem-vii-blackadar-kirchberg` implies (a).  No route is written for
  this trivial specialisation.  A counterexample to (a) would refute Problem
  VII, and by Theorem A it would come with a separable QD type I algebra lacking
  the K_0-embedding property.
- **Below the UCT-quotient extension case.**
  `blackadar-kirchberg-for-uct-quotient-extensions` implies (a), by the route
  above.  Via Brown--Dadarlat Theorem 4.11,
  `every-separable-nuclear-qd-algebra-has-k0-hahn-banach` implies both.  Theorem
  A shows that (a) needs only the type I instances of the K_0-embedding
  property, not the property for all nuclear QD ideals.
- **Any composition series works.**  The proof of (b) ⇒ (a) and Corollary B use
  only that the subquotients `I_{α+1}/I_α` are CCR.  So any well-ordered
  composition series with CCR subquotients may replace the canonical one from
  (T3).
- **`bk-projection-generated-ideals-with-uct-quotients-force-qd`.**  That node
  settles type I algebras with finitely many ideals, assuming stable finiteness.
  Corollary B1 recovers this without stable finiteness.  Such an algebra has a
  finite composition series with simple, hence elementary, subquotients `K` or
  `M_n`.  Their `K_1` vanishes, so every `G_α = 0`.
- **`bk-t1-primitive-spectrum-case`.**  Its type I part is settled by Lemma 1
  (Corollary B3), without nuclearity or finiteness hypotheses.  That claim stays
  open in general, because its non-type I part is the simple case.
- **`bk-primitive-quotients-qd-or-traceless-force-qd`.**  By Proposition C (i),
  it does not reach every QD type I algebra.  Its fibrewise hypothesis fails for
  `T'`.
- **`bk-radical-projection-quotients-are-toeplitz-infinite` (Corollary 10)
  and `bk-relative-boundary-descends-or-is-positively-detected` (item 4).**
  - These locate the obstruction in a type I counterexample at Toeplitz-like
    points, and show that quotient-side peeling of the boundary is blocked.
  - Proposition C shows that Toeplitz-like points do occur inside QD type I
    algebras.  So they are not by themselves an obstruction.
  - Theorem A climbs through the *ideals* `I_α ⊆ E`, never through quotients.
    It is therefore consistent with item 4.  Its only open input is the killing
    of the singular subgroups `G_α ⊆ K_0(I_α)` by QD embeddings of the ideals.
- **`moutzouris-k0-killing-is-local` and `moutzouris-qd-extensions-y-class`.**
  These supply the known cases of (b) used in Corollary B2 and the reductions of
  §6.1.

### 7.3 Literature consulted (2026-09-16 unless stated)

- N. P. Brown, M. Dadarlat, *Extensions of quasidiagonal C\*-algebras and
  K-theory*, arXiv:math/0008182, TeX source re-read 2026-09-16.  Used:
  - Propositions 2.5, 3.3, 4.1 and 4.6;
  - Theorem 3.4;
  - Lemmas 3.2 and 4.5;
  - Definitions 4.3, 4.4 and 4.8;
  - Theorems 4.11 and 4.12, and the remark after 4.12.

  Compiled numbering is used throughout.
- N. P. Brown, *On quasidiagonal C\*-algebras*, arXiv:math/0008181, TeX source
  read 2026-09-16.  It has no type I results beyond the classical ones.
- I. Moutzouris, arXiv:2112.03224v3, HTML read 2026-09-16.  Used: Propositions
  3.2, 3.3 and 3.5, and class `Y`.
  The introduction lists the known cases of the conjecture as simple UCT,
  traceless, and AH-of-real-rank-zero crossed by `Z`; type I algebras are not
  mentioned.
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902.  Only the abstract page was read, on 2026-09-16 (v2 dated
  8 May 2026).  This is the source of the graph node
  `stw99-problem-vii-blackadar-kirchberg`.  The problem text itself was not
  re-read.  No later arXiv item found in this session claims to resolve
  Problem VII.
- N. Ozawa, arXiv:2609.08892 (8 Sep 2026), abstract read.  It is about MF
  algebras and the hyperfinite II_1 factor, with no bearing on the type I case.
- B. Blackadar, E. Kirchberg, *Inner quasidiagonality and strong NF algebras*,
  arXiv:0711.4949, abstract read (see §5).
- H. Yao, *On extensions of stably finite C\*-algebras (II)*, Canad. Math. Bull.
  59 (2016), abstract page read.  It treats real rank zero algebras with an
  approximate unit of projections, and says nothing on quasidiagonality of type
  I algebras.
- Brown's survey, Proposition 10.10, quotes Spielberg's criterion verbatim
  ([Sp, Lemma 1.5]).
- **Cited but NOT fetched (unverified):**
  - J. Spielberg, J. Funct. Anal. 81 (1988): ScienceDirect returned 403.  This
    covers Lemma 1.5 and the AF case Lemma 1.14.  The criterion itself is used
    only as quoted by BD and by Brown's survey.
  - I. D. Berg, Trans. AMS 160 (1971), for the Weyl--von Neumann--Berg theorem.
  - Rosenberg--Schochet, Duke Math. J. 55 (1987), for the UCT for type I
    algebras.
  - Dixmier, Pedersen and Brown--Ozawa, for the textbook facts (T1)--(T3) and
    (Q1).  Numbering not re-checked.
  - T. A. Loring, on almost commuting matrices and fuzzy spheres (§6.3 (α)).
    No specific paper was checked, and nothing proved here depends on it.
