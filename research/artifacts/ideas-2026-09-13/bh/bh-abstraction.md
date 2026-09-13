# bh-abstraction: which structure-to-action step each known Boone–Higman case uses

Idea lane, 2026-09-13 ideation funnel. Target: `boone-higman-conjecture`.

Lens: abstract the host-producing step from every known BH and PBH case, find the minimal hypothesis they share, and state the missing universal step precisely.

Read from origin/main at 5309163713. Nothing here is claimed established, and no Cairn node is edited.

## 0. What each known case actually uses

| Case | Node on main | Structure that produces the host | Engine | Where finiteness comes from |
|---|---|---|---|---|
| Hyperbolic groups (BBMZ, arXiv:2309.06224, import) | `hyperbolic-groups-satisfy-boone-higman` | boundary dynamics → contracting rational similarity group | E3 | contraction plus rational germs |
| Contracting self-similar groups (same paper; Zaremsky arXiv:2405.09722 Thm 1.1 for fp self-similar) | `fp-self-similar-subgroups-satisfy-permutational-boone-higman` | self-similarity | E2 → E1 | fp self-similar H |
| Char-0 and char-p linear groups, spherical Artin groups, metabelian groups | `char-zero-linear-pbh-via-polynomial-self-similar-hosts`, `char-p-linear-pbh-via-polynomial-self-similar-hosts`, `spherical-artin-pbh-via-char-zero-linear-groups`, quasi-linear chain | linearity (Noether normalization) → `R^n ⋊ E_n(R)` over polynomial rings, one coordinate as uniformizer | E2 → E1 | K₂/Steinberg finite presentation; states by coordinate substitution |
| Char-2 surface-linear groups | `char-two-surface-linear-groups-satisfy-boone-higman` | group ring → `B ⊗ L_(F₂)(1,2)` | E4 | Khanh / Ara–Cortiñas: K₁ = K₂ = 0 |
| Baumslag–Solitar, free-by-cyclic (Bux–Llosa Isenrich–Wu, arXiv:2408.05673, import) | `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` | action on a locally finite tree with virtually free / abelian / nilpotent vertex groups | not recorded on main | tree plus vertex-group finiteness |
| Aut(F_n), punctured mapping class groups (BFFHZ, arXiv:2503.21882, import) | `aut-free-groups-satisfy-permutational-boone-higman` | relative automorphism action on `Hom_G(G*F_n, G)` (highly transitive) | E1 | the actor is itself fp |
| Boundary-orbit cyclic wreath (repo) | `boundary-orbit-cyclic-wreath-has-fp-simple-envelope` | contracting self-similar group plus an adjoined letter | E2 → E1 | rational stabilizers are fp |
| A5 arithmetic shell envelope (repo) | `a5-arithmetic-shell-envelope-embeds-in-fp-simple-group` | shell envelope inside a full contracting RSG | E3 | contraction (the envelope's own fp is OPEN) |

**Engines** are the steps that deliver simplicity plus finite presentation. For each, the input it needs and its status for arbitrary decidable inputs:

- **E1 twisted Brin–Thompson** (Zaremsky arXiv:2405.18354 Thm A; `type-a-action-gives-boone-higman-for-subgroups`). Input: a faithful fp actor with f.g. stabilizers and finitely many pair orbits (type (A)). OPEN: this is PBH.
- **E2 Röver–Nekrashevych commutator** (Zaremsky Thm 1.1). Input: an fp faithful self-similar H. FALSE universally: `self-similar-hosts-contain-only-residually-finite-groups`, `deligne-lattice-embeds-in-no-rover-nekrashevych-group`.
- **E3 contracting RSG** (BBMZ). FALSE universally: `rational-homeomorphism-subgroups-have-exponential-wp` plus `complexity-bounded-host-classes-are-not-universal`.
- **E4 Leavitt tensor unit group** (`boone-higman-via-central-simple-leavitt-tensor-host`). Input: an fp central simple B containing `F₂[G]`, with `K₁(B⊗L) = K₂(B⊗L) = 0`. OPEN: `decidable-group-algebras-have-fp-central-simple-hosts`.
- **E5 shell envelope** (`boone-higman-via-fp-shell-envelopes`). Input: finite presentation of `E_ν` for some enumeration. OPEN.
- **E6 CK maximal kernel / finite bi-index** (`boone-higman-via-ck-maximal-kernel`, `boone-higman-via-finite-bi-index-envelope`). Input: a finitely normally generated maximal kernel, or finite bi-index. OPEN.

**"Every decidable group embeds in X": the ladder on main**
- **True:**
  - X = f.g. computably presented simple group (BBMZ arXiv:2306.16356 Thm 3.8; `boone-higman-thompson-simple-envelope`);
  - X = an fp overgroup whose proper normal subgroups all miss G (`bht-trivial-normal-intersection-envelope`);
  - infinite simple inputs suffice (`boone-higman-iff-infinite-simple-inputs`);
  - a faithful finite-germ shell realization (its fp is open).
- **False:**
  - fp self-similar hosts;
  - contracting rational hosts;
  - Röver–Nekrashevych hosts;
  - any class with a uniform recursive word-problem bound;
  - the canonical relative-automorphism host for non-fp cores (`relative-automorphism-fp-host-reflects-base-presentation`, `bffhz-computable-core-fp-upgrade-is-false`).
- **Open:**
  - X = a type (A) actor (PBH);
  - X = an isolated group (Cornulier–Guyot–Pitsch Question 4);
  - an E4 algebra host;
  - an E5 fp shell envelope;
  - an E6 fng maximal kernel or finite bi-index.

## 1. Approaches

### A1. Normal form for every engine premise: start from simple inputs

- **Idea:** by Thm 3.8 and `boone-higman-iff-infinite-simple-inputs`, every engine premise can be required only for infinite f.g. computably presented simple S. A simple S has no finite quotients, so in any faithful action every nontrivial S-orbit is infinite and S acts faithfully on each one. For E1 the step reads "S lies in an fp type (A) actor". For E4 it reads "`F₂[S]` lies in an fp central simple B with vanishing Leavitt-tensor K₁, K₂".
- **Would prove:** nothing new by itself. It narrows every premise to simple inputs.
- **Kill test (hand):** is "PBH for simple inputs" equivalent to PBH? Every decidable G lies in some computably presented simple S (Thm 3.8), and subgroups of type (A) actors inherit PBH. So yes.
- **Verdict:** killed as new content (a restatement). Kept as the normal form used below.

### A2. Complexity diagnostic: no known case has run a candidate engine on a hard input

- **Idea:** sort the engines by whether their input class has a uniform recursive word-problem bound.
  - E2 and E3 do (the RF wall; exponential word problem), so they can't be universal.
  - E1, E4, E5 and E6 don't, so they're the only candidates.
  - Every established case in §0 feeds its engine inputs from a bounded class: linear groups (logspace word problem, per Lipton–Zalcstein and Simon, not re-read here), hyperbolic groups (linear time), Aut(F_n), BS and free-by-cyclic groups (low complexity).
- **Would prove:** the positive cases carry no evidence about universality. The prerequisite benchmark is an engine running on inputs with arbitrarily complex word problem. That is the OPEN root `fp-simple-groups-with-arbitrarily-complex-word-problem`, and main has routes for it (`arbitrarily-complex-fp-simple-via-hard-type-a-actors`, `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`).
- **Kill test:** find an established BH case on main whose inputs have a word problem beyond elementary recursive. None found in the case table.
- **Verdict:** SURVIVES as a diagnostic. It ranks the arbitrarily-complex root as the benchmark to clear before any universal claim.

### A3. The missing step is a Higman embedding theorem with an engine condition

- **Idea:** every engine input is finite-type data: finitely many pair orbits (E1), finite K-data plus finite presentation (E4), finite normal generation (E6). Decidability supplies only effective enumeration data. Higman's theorem is exactly a finitization functor, "computable presentation ↦ fp overgroup", with no action condition. So the universal step is precisely one of:
  - **(M1)** a *permutational Higman theorem*: every computably presented f.g. simple S embeds in an fp group Γ with a faithful action on some set, having f.g. stabilizers and finitely many pair orbits;
  - **(M4)** an *algebra Higman theorem with control*: `F₂[S]` embeds in an fp central simple `F₂`-algebra B with `K₁(B⊗L) = K₂(B⊗L) = 0`. This is the algebra root `algebra-boone-higman-conjecture` plus K-theory control.
- **Would prove:** BH, through E1 or E4 respectively.
- **Kill test for M1 (hand):** Higman's construction reaches benign subgroups through HNN/amalgam towers. Let H fix a vertex w of an unbounded Bass–Serre tree. For g ∈ Γ and h, h′ ∈ H, `d(w, hgh′·w) = d(w, g·w)`, so each double coset HgH determines `d(w, g·w)`. That distance takes infinitely many values, so Γ/H has infinitely many pair orbits. Hence the tower's coset actions on vertex or edge stabilizers are never type (A).
- **Kill test for M4:** `no-fp-simple-algebra-hosts-every-decidable-algebra` rules out a single fixed host. It doesn't rule out a construction that depends on the input.
- **Verdict:** SURVIVES as the precise target. Constraint for M1: a type (A) stabilizer must contain an element acting hyperbolically in every unbounded splitting coming from the tower.

### A4. BH ⇒ PBH is a statement about fp simple groups only

- **Idea:** decide whether some engine premise is *necessary* for BH, so effort isn't spent on something strictly stronger.
  - E6 is about one specific Γ, so BH doesn't imply it.
  - For E4 and E5, the implication from BH is unknown.
  - For PBH, BFFHZ call BH ⇒ PBH "a fundamental question"; FFWZ Theorem C gives only BH ⇒ relPBH.
  - With BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`): G satisfies PBH iff G embeds in an fp simple highly transitive (or MIF) group.
- **Hand corollary:** "for every decidable G, BH(G) ⇒ PBH(G)" holds iff *every finitely presented simple group embeds in a finitely presented simple highly transitive group*.
  - (⇐) From H ⊇ G fp simple and H ≤ H′ fp simple highly transitive, G satisfies PBH by Thm C(iii).
  - (⇒) An fp simple H has solvable word problem and satisfies BH trivially, so PBH(H) holds, and Thm C gives H ≤ an fp simple highly transitive group.
- **Would prove:** reduces the BH-versus-PBH question to a universality statement inside the class of fp simple groups. It isn't a statement over all decidable groups, and it doesn't touch BH itself.
- **Kill test:** is it already on main? A grep for `highly transitive` over research/ finds BFFHZ Thm C imported in `fp-simple-highly-transitive-groups-satisfy-pbh` and `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, but no node states the corollary. Test inputs:
  - Thompson T is fp simple and not highly transitive on the circle, but T ≤ V, which is fp simple and highly transitive, so T passes.
  - Röver's group is V_2(Grig), highly transitive, so it passes.
  - The Burger–Mozes fp simple lattices are the natural test case; nothing on main decides them.
  - Not an obstruction by itself: every countable group embeds in some highly transitive group. The only obstruction could come from finite presentation plus simplicity of the overgroup.
- **Verdict:** SURVIVES as a sharp reformulation of BFFHZ's question. Novelty against the literature is unchecked; BFFHZ may state it themselves. Next test: whether the Burger–Mozes simple lattices embed in an fp simple highly transitive group.

### A5. Use BFFHZ's relative automorphism actor as the universal E1 input

- **Idea:** for infinite f.g. simple S and n ≥ 2, `Abar = Aut_S(S*F_n)/K` acts faithfully and highly transitively on `Hom_S(S*F_n, S) ≅ Sⁿ` with f.g. stabilizers, and S embeds by translations (`relative-automorphism-action-is-highly-transitive`). So finite presentation of Abar would be the only missing input to E1.
- **Would prove:** PBH for S, hence BH for all decidable inputs.
- **Kill test:** already on main. `relative-automorphism-fp-host-reflects-base-presentation` shows that any fp subgroup of `Aut_G(G*F_n)` containing the translation copy of G forces G to be fp. The upgrade for computable cores is refuted by `bffhz-computable-core-fp-upgrade-is-false`. For computably presented, non-fp simple S the construction therefore can't give an fp host through the canonical embedding. Only arbitrary quotients escape, and those lose the explicit structure.
- **Verdict:** killed (a duplicate of main's recorded obstruction). The construction still covers fp simple cores, which is BFFHZ's own question.

## 2. The precise missing universal step

Every known case factors as (bounded structure class) → (one engine). The engines able to be universal are E1, E4, E5 and E6. For each, what's missing is a finitization theorem of Higman type for simple computably presented inputs:
- **M1 (E1):** a permutational Higman embedding;
- **M4 (E4):** an algebra Higman embedding into fp central simple algebras with vanishing Leavitt-tensor K₁ and K₂;
- **M5 / M6:** finite presentation of the shell envelope, or finite normal generation of a CK maximal kernel.

None of these is known to be necessary for BH. A4 shows that the E1 premise is necessary for BH exactly when every fp simple group embeds in an fp simple highly transitive group.

No known positive case exercises any of these engines on inputs whose word problem is beyond a uniform recursive bound (A2). So the arbitrarily-complex fp simple root is the first benchmark any universal proof has to pass.
