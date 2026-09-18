# bh-pal-kourovka61, pass 2: the F_∞ route, the Bleak–Quick template, and a sharper coherence gap

Lane bh-pal-kourovka61, 2026-09-18 (afternoon). Target: T8 of `gq-bh-pal-scope.md`, i.e. an
explicit, literature-free finite presentation of `CT_P(Z)` (Kourovka 17.61) for Lean. No priority is
claimed. Notation follows `class-transposition-presentation-has-central-kernel`. `Γ_P` is the
transposition presentation (R1)–(R3), `ε: Γ_P → CT_P(Z)` its evaluation map, and `K = ker ε`, which
that node proves central. `PC` is the group of piecewise-canonical permutations, which equals `CT_P(Z)`
by `piecewise-canonical-permutations-are-transposition-products` (elementary).

## 1. The "type F_∞" route to 17.61 (checked first, as asked)

The referee remark in `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` (fac0259d6) points to item 2
of `ct-p-z-is-a-one-vertex-k-graph-full-group`. That item is already the positive answer to 17.61 on
main, and it is literature-dependent: type `F_∞` comes from Li, arXiv 2110.04505.
- **Read at source this pass** (`gq/src/li2110/main.tex`):
  - l.2171, Cor. `cor:OneVertex`, a finite one-vertex higher rank graph;
  - l.2140, the general finite-k-graph form;
  - l.2125, the `Z^k_{≥0}` Garside specialization it comes from.
- **Hypotheses that match:**
  - `Λ_P` is a finite one-vertex `(|P|+1)`-graph with `p ≥ 2` edges of colour `p`;
  - `X = ∂Ω` is closed and invariant.
- **To confirm at referee time:**
  - The choice `Y = X`. The node writes `e_P = ∅`. We did not locate Li's definition of `X(v; 𝔢)`,
    so whether the right choice is `e_P = ∅` or `e_P = {0}` (with `d^{-1}(0) = {1}`) is unchecked.
  - The identification `I_l ⋉ ∂Ω = G_Λ`, which the node marks "not re-read".
- **Verdict.** The route is sound modulo those two reading checks. It settles 17.61 only with Li
  (and Matui, and Farsi–Kumjian–Pask–Sims) as inputs, so it cannot be the Lean route: Mathlib has
  none of this. It deserves a referee pass as its own node, as the remark says.

## 2. The P = ∅ template does not exist elementarily

Bleak–Quick, arXiv 1511.02123 (TeX read; `gq/src/bq/bq.tex`), Thm `thm:infpres` (l.477). They prove
exactly our (R1)–(R3), with cones for boxes, for `V`. Their proof (§§3–6, l.1068–1118, l.2210ff)
does two things:
1. It verifies Thompson's finite presentation of `V` in the Cannon–Floyd–Parry form (CFP Lemma 6.1,
   fourteen relations) inside the presented group.
2. It derives the infinite presentation from that.

So even for `P = ∅` the infinite presentation rests on a known finite presentation. For `P ≠ ∅` the
only printed presentations are Martínez-Pérez–Matucci–Nucinkis's (1609.07058, via Stein complexes
and Geoghegan's theorem). An elementary proof has to supply the Stein-complex step itself.

## 3. New lemmas (lane proofs, elementary)

**Lemma T (every lift is a transport).** Let `h ∈ Γ_P` and let `β` be a box partition such that
`g = ε(h)` is canonical on every cell of `β`. Then `h t(E,F) h^{-1} = t(gE, gF)` for all disjoint
boxes `E, F`, each contained in a cell of `β` (possibly the same cell).

*Proof.*
1. Write `h` as a word `w`.
2. By Lemma 4 of the central-kernel node, some refinement `S` of `β ∧ {E, F, Z∖(E∪F)}` has all
   cells regular along `w`.
3. Choose `k ∈ N_{P'}` such that `U_k(E)` and `U_k(F)` refine `S`.
4. By Lemma 2, `t(E,F) = ∏_{u ∈ U_k(Z)} t(κ_E u, κ_F u)`.
5. By Lemma 3, each factor goes to `t(g κ_E u, g κ_F u) = t(κ_{gE} u, κ_{gF} u)`, since `g` is
   canonical on `E` and on `F`.
6. Lemma 2 reassembles the product into `t(gE, gF)`. ∎

This removes all word bookkeeping from the transport argument: regularity is a property of
`ε(h)`, not of the word. Item 2 of the central-kernel node is the case `g = 1`.

**Lemma P (corrected in pass 3).** The Higman–Thompson-type Ore presentation of `PC` has:
- generators: the splits `x_{n,i,p}` of position `i` of an ordered natural basis of size `n` by a
  prime `p ∈ P'`, and the permutations `σ ∈ Sym(n)`;
- relations:
  - (a) the relations of `Sym(n)`;
  - (b) far commutation of two splits;
  - (c) colour exchange (`p` then `q` = `q` then `p`, followed by the residue bijection
    `j + pl ≡ j' + ql' (mod pq)`);
  - (d) naturality of permutations under splits.

Fix comb frames `β_1 = (Z)`, `β_n = (0(2), φ_1 β_{n−1})`. Send `σ` to its canonical copy in
`Γ_{β_n} ≅ Sym(n)`, and choose any lift `X_{n,1,p}` of the frame change
`β_{n+p−1} → β_n·(1,p)`. For `i ≥ 2`, *define* `X_{n,i,p}` by (d) from `X_{n,1,p}`: conjugate by
canonical permutations that move position 1 to position `i`. Then:
- this is well defined;
- (a) and (d) hold exactly;
- the defect `L R^{-1}` of an instance of (b) or (c) depends only on the sizes and colours, not on
  the positions.

*Proof.* Two such definitions differ by a canonical permutation fixing the split cell. By Lemma T
and (R3), `X^{-1} S X` is the canonical permutation of the split basis. (a) is Lemma 1 of the
central-kernel node. Position independence uses (d) together with centrality of `K`. ∎

*Correction.* Pass 2 claimed that (d) holds for *any* lifts. That is true only for permutations
fixing the split position. For other permutations, (d) is what defines `X_{n,i,p}` from
`X_{n,1,p}`.

**The compression identities.** Choose one lift `Y_p` of `β_p → (p-split of Z)`, with `Y_2 = 1`, and
one lift `R_p` of the rebracketing `r_p: β_{p+1} → (φ_0 β_p, 1(2))`. The rebracketing is an
element of Thompson's `F` (2-power boxes only). Put `X_{1,1,p} = Y_p` and
`X_{n,1,p} = φ_0(Y_p) R_p` for `n ≥ 2`. As a PC element, `r_p` is also the frame change
`β_{n+p−1} → (φ_0 β_p, φ_1 β_{n−1})` for every `n ≥ 2`.

Define `π(n,p) ∈ K` by `X_{n,2,p} = φ_1(X_{n−1,1,p}) · π(n,p)`. Computing with (R2) gives
`π(n,p) = φ_1(R_p)^{-1} · t(c_1, c_2) R_p S` for a canonical `S`. This is *independent of `Y_p`*:
it is a relation of the 2-power subgroup `Γ_∅` (the V-core, a pentagon-type identity for the
lifts `R_p`).

**Proposition F (far commutation closes).** Assume `π(n,p) = 1` for all `n ≥ 2` and `p ∈ P'`.
Then every instance of (b) closes exactly in `Γ_P`.

*Proof.*
1. Given the `π`'s, `X_{n,i,p} = φ_1(X_{n−1,i−1,p})` for `i ≥ 2`.
2. An instance at size `n ≥ 3` on positions `(2,3)` is the `φ_1`-image of an instance at size
   `n−1`, so by position independence its defect is `ψ` of the smaller defect.
3. The base instance is at size 2, positions `(1,2)`, colours `p, q`.
   - One path gives `X_{2,1,p} X_{p+1,p+1,q} = φ_0(Y_p) R_p φ_1^p(Y_q)`. By Lemma T, since `r_p`
     is canonical on the last comb cell `φ_1^p Z` and maps it onto `1(2)`, this equals
     `φ_0(Y_p) φ_1(Y_q) R_p`.
   - The other path gives `X_{2,2,q} X_{q+1,1,p} = φ_1(Y_q) φ_0(Y_p) R_p`.
   - `φ_0(Y_p)` and `φ_1(Y_q)` commute (disjoint supports, (R2)), so the defect is 1. ∎

**Corollary R (sharp form of the gap, corrected).** Assume Fact O: the Ore presentation presents
`PC`. It is the MMN infinite presentation for the complete laws `Σ_P`, and its elementary proof
needs:
- validity: two trees with the same leaf set are related by (b) and (c), by induction on the root
  prime;
- Ore's theorem for ordered natural bases;
- the free `PC`-action on chart bases.

Then `K` is generated by:
- the V-core elements `π(n,p)`;
- the base colour-exchange defects `d(p,q) := d_c(1,p,q)` for `p ≠ q` in `P'`.

Instances of (c) at size `n` are `ψ^{n−1}` of `d(p,q)`, by the same compression/position argument
as in Proposition F. *Proof:* the lifts define a homomorphism from the Ore presentation to
`Γ_P / ⟨defects⟩` that is inverse to `ε` on generators, and Proposition F removes (b). ∎

**Consequence (conditional on the P = ∅ case).** The subgroup `Γ_∅ ⊆ Γ_P` generated by 2-power
transpositions is a quotient of the abstract presentation for `P = ∅`. That presentation is
Bleak–Quick's `thm:infpres` for `V` (literature: it is proved via Cannon–Floyd–Parry). If it
holds, `ε|_{Γ_∅}` is injective, so every `π(n,p) = 1`. Then:

    K = ⟨ d(p,q) : p ≠ q ∈ P' ⟩,  one central element per pair of colours.

Each `d(p,q)` is an explicit finite word in `Y_p`, `Y_q`, `R`'s, compressions and cell
permutations. `Y_p` can still be changed by any central element.

**Proposed kill (not done): the {2,p,q} cube.** The boundary of the 3-cube of elementary
expansions of `Z` by `{2, p, q}` has defect product 1 identically, because the defects are central
and telescope. With far commutation closed, this reads, up to orientation:

    d_{pq} · ψ^{a}(d_{2p}) · ψ^{b}(d_{2q}) = ψ(d_{pq}) ψ^{pq}(d_{pq}) · ∏_{j<p} ψ^{p−1+j(2q−1)}(d_{2q}) · ∏_{j<q} ψ^{q−1+j(2p−1)}(d_{2p})

Here the exponents record basis sizes, and `a` and `b` still have to be read off the cube. This is
the elementary shadow of FKPS's `N_2 = 2 − 1 = 1`: splitting by the colour with two edges doubles a
class. It kills the `d`'s once `ψ` is shown to act trivially on `⟨d⟩`, or once the exponents are
tracked exactly. Neither is done.

**Lemma C (canonical lifts of doubled elements).** Let `s = t(0(2), 1(2))`, and let `φ_a` be the
compression homomorphism `Γ_P → Γ_P`, `t(A,B) ↦ t(κ_{a(2)}A, κ_{a(2)}B)`. It is well defined because
(R1)–(R3) are preserved.
- For `g ∈ PC` choose natural ordered bases `b` and `c = g b` of the same size. Put
  `I(g) := ∏_k t(φ_0 b_k, φ_1 c_k)`. This is a product of commuting transpositions, independent of
  `(b, c)` by (R3), and a lift of the involution `2x ↔ 2g(x)+1`.
- For every `γ ∈ Γ_P`: `φ_1(γ) s φ_1(γ)^{-1} = I(ε(γ)) = φ_0(γ)^{-1} s φ_0(γ)`.
  *Proof:* by (R3), `s = ∏_k t(φ_0 b_k, φ_1 b_k)`; apply Lemma T to each factor.
- Consequently `φ_1(γ) φ_0(γ)^{-1}` depends only on `ε(γ)`. This is the first choice-free lift of a
  non-torsion family (`φ_0(g^{-1})φ_1(g)`) that we know of.
- It reproves `φ_0(z) = φ_1(z)` for `z ∈ K`. It does not by itself kill `K`: every identity it gives
  is between compressed copies, and `z` itself never appears uncompressed.

## 4. What is left, and the plan (updated in pass 3)

- **Gap 1 (Fact O), the Ore-category presentation of `PC`.** It is elementary but several pages
  long: validity, Ore localization, and covering by a free action. No literature is needed.
- **Gap 2 (the V-core).** The `π(n,p)` are relations of the 2-power subgroup. Killing them *is* the
  `P = ∅` theorem (Bleak–Quick), whose printed proof goes through Cannon–Floyd–Parry's finite
  presentation of `V`. An elementary replacement would be Higman-style normal forms for `V`.
- **Gap 3 (mixed squares).** One central element `d(p,q)` per pair of colours. The proposed route
  is the {2,p,q}-cube swindle in §3.
- **Pass 3 status.** Squares touching the first cell are closed for far commutation, conditional on
  gap 2 (Proposition F). They are not closed for colour exchange, where gap 3 remains.
- **Only then:** the finite truncation, and the Lean.
- **Lean status.** The repo now has box, swap and compression infrastructure in
  `GroupApproximation/Kourovka1759/` (Box, Swap with `transHom` = φ_N, PC). The first Lean target is:
  - the presented group `Γ_P` (`PresentedGroup` on pairs of disjoint admissible boxes, relations
    (R1)–(R3));
  - the evaluation `ε` onto `classTranspositionGroup`;
  - the compression endomorphisms φ_N.
  That is not started in this pass.

## 5. Pass 4: the colour-exchange defects die (the {2,p,q}-cube swindle)

Lane proof, not reviewed. It supersedes the "Proposed kill" and the `π` bookkeeping of §3.

**Forced lifts.** Keep only `Y_p` free (`Y_2 = 1`). Put:
- `X_{1,1,p} = Y_p`;
- `X_{n,2,p} := φ_1(X_{n−1,1,p})` for `n ≥ 2`;
- every other position by (d)-transport from position 2.

Then (a) and (d) hold exactly (Lemma P), and `X_{n,i,p} = φ_1(X_{n−1,i−1,p})` for all `i ≥ 2`,
because (d)-transport by permutations fixing cell 1 commutes with `φ_1`. So `π ≡ 1` by
construction, and a defect of an instance at size `n` is `ψ^{n−1}` (colour exchange) or
`ψ^{n−2}` (far commutation) of the base defect.

**ψ is idempotent on K.** For `z ∈ K`, `ψ(z) := φ_A(z)` does not depend on the proper box `A`
(pass 2). So `ψψ(z) = φ_A φ_A(z) = φ_{place A A}(z) = ψ(z)`. Hence `ψ = id` on `ψ(K)`.

**Far commutation.** The base defect `D_b(p,q)` (size 2, cells `0(2)`, `1(2)`) is independent of
the `Y`'s:
- each lift at size `≥ 2` carries a central change `ψ(z)`;
- after the `Y`'s are transported away (Lemma T), both paths reduce to words in comb-cell
  transpositions.

So `D_b(p,q) ∈ K ∩ Γ_∅`. **Input V:** `ε` is injective on the 2-power subgroup `Γ_∅`. This follows
from Bleak–Quick's theorem for `P = ∅`, since their relations map into ours. Given it,
`D_b(p,q) = 1`, and every far-commutation square closes.

**Colour exchange.** Write `D_{uv}` (additively; `D_{vu} = −D_{uv}`) for the root defect, at size
1, of the square "`u` then `v` on all children" against "`v` then `u`".
1. *Changing `Y`.* Under `Y_p ↦ Y_p z_p`, a path gains `z` for its size-1 step and `ψ(z)` for each
   later step. So `D_{uv}` changes by `z_u + u ψ(z_v) − z_v − v ψ(z_u)`, and in particular
   `D_{2p}` changes by `2ψ(z_p) − z_p`.
2. *The cube.* The six orderings of the splits `2, p, q` of `Z` form a hexagon of squares. Defects
   are central and telescope, so
   `D_{2p} + F_{2q}(p) + D_{pq} − F_{2p}(q) − D_{2q} − F_{pq}(2) = 0`.
   Here `F_{uv}(w)` is the sum of the `(u,v)` defects at the `w` children, all at sizes `≥ 2`,
   hence in `ψ(K)`. The far-commutation defects that interleave vanish.
3. *Step 1.* Take `z_p := D_{2p}`. Then the new `D_{2p} = 2ψ(D_{2p}) ∈ ψ(K)`, and by the cube
   `D_{pq} ≡ D_{2q} − D_{2p} ≡ 0 (mod ψ(K))`.
   - So every generator of `K` lies in `ψ(K)`, i.e. `K = ψ(K)`.
   - By idempotence, `ψ = id` on `K`.
4. *Step 2.* With `ψ = id`, take `z_p := −D_{2p}`. Now `D_{2p} = 0`, and the cube reads
   `D_{pq} = (1−q) D_{2p} + (p−1) D_{2q} = 0`.

Every defect vanishes for this choice of lifts, so `K = 1` by Corollary R. Hence:

> **Theorem (conditional).** Assume Fact O (the Ore presentation of `PC`; MMN 1609.07058, or its
> elementary proof) and Input V (Bleak–Quick: (R1)–(R3) present Thompson's `V`). Then (R1)–(R3)
> present `CT_P(Z)` for every finite `P`.

**Why it works.** The colour with two edges gives `D_{2p} ↦ D_{2p} + 2ψ(z) − z`. That is the
2-cell shadow of `[B] = 2[B]` (FKPS: `N_2 = 1`). Without a colour of arity 2 the swindle fails,
which matches `H_2 ≠ 0` when `gcd(N_i) > 1`.

**Remaining for an unconditional proof:**
- Fact O, written in full;
- Input V without Cannon–Floyd–Parry (Higman normal forms, or the same swindle on the
  far-commutation squares of `V`, which does not work as is: the far-commutation class at size 2
  is untouched by the cubes);
- then the finite truncation.

## Lesson for general BH

A presentation-by-involutions of a full group is exactly as hard as the simple connectivity of its
Stein complex. Local tools, even in exact form, reduce the question to the 2-cells of the Ore
category and no further:
- transport (Lemma T): conjugation acts correctly on everything fine enough;
- finite symmetric subgroups;
- choice-free doubled lifts.

The kernel is central and generated by the defects of the far-commutation and colour-exchange
squares. For BH host design this is the right bookkeeping. A host of type (A) built as a full group
of a complete `k`-graph-like Cantor algebra gets its finite presentation from finitely many square
checks plus self-similarity, not from global geometry. And a central defect that is
position-independent must be killed by one explicit computation per colour pair.
