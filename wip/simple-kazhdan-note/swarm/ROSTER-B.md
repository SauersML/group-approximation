# SK roster B: consequences, embeddings, frontier, explorers, exposition, verification

Each brief is a starting point, not a cage (RULES §1). Line numbers refer to `$SK/manuscript-disk-1646.tex`.

## sk-operator-algebras (the strongest true operator-algebra corollaries)
Candidates:
- Brown's exact formulation: an embedding into the unitary group of an R^ω-embeddable McDuff factor;
- L(G_X) is a II_1 factor with (T) inside R^ω;
- Kirchberg's factorization property;
- MF and quasidiagonality of C*_r(G_X), C*(G_X) and the canonical trace (Carrión–Dadarlat–Eckhardt, Schafhauser MF traces, the un-traces results).

Decide which one-sentence corollaries are TRUE, verified, and strong enough to earn their sentence. Deliverable: proposal. Peers: sk-questions-oa, sk-characters.

## sk-lef-growth (how fast must the finite models grow?)
Quantify the LEF growth of G_X (the least size of a finite group containing a partial copy of the r-ball; Bradford's definition) in terms of the recurrence function R_X.
- Upper bound from the note's models: N ≈ R_X(2r+1), size 2^{9N²}.
- Lower bound: does the r-ball contain tower groups GL_d(F_2) with d growing linearly in r, forcing large finite groups?
- For linearly recurrent X such as Fibonacci, is the LEF growth exp(Θ(r²))?
- Is there a published question on LEF growth of simple or Kazhdan groups?

Deliverable: a proposal for one sentence, or none. Peers: sk-lef-short, sk-questions-ggt.

## sk-generators (small generating sets and the Fibonacci example)
- The minimal number of generators of G_X (is it 2?).
- Generation by three involutions (`binary-pestov-groups-are-three-torsion-generated`).
- An explicit generating set of size at most 4 for the Fibonacci subshift, and its first finite model.

Useful but brief: the deliverable is at most a remark with a complete proof. Peer: sk-subgroups.

## sk-subgroups (what lives inside G_X)
- CORRECTED ~19:30: the map a ↦ diag(a, a^{-1}, 1) is NOT a homomorphism on noncommuting units (sk-subgroups). The derived group [[T]]' embeds in G_X through a ↦ diag(a,1,1), because diag(aba^{-1}b^{-1},1) is a product of Whitehead elements diag(c,c^{-1}). So the amenable simple group [[T]]' (Matui, Juschenko–Monod) sits inside the Kazhdan simple group G_X, and both come from the same dynamical system.
- Also: every finite group; every countable locally finite group?; free groups (EL_3(F_2[u^{±1}]) ⊆ G_X); lattices?

Target: one beautiful, true sentence with a complete short proof. Peers: sk-generators, sk-universal-embedding-a.

## sk-characters (characters and invariant random subgroups of G_X)
Classify the extreme characters of G_X and its ergodic IRS. Candidates:
- only 1 and δ_e (character rigidity);
- characters built from invariant measures on X through rank functions.

Compare Dudko–Medynets (characters of topological full groups), Peterson–Thom, Bekka, and un-traces. Target: a theorem with a short proof, if a true and clean one exists. Deliverable: a proposal, or a firewall node. Peer: sk-operator-algebras.

## sk-word-problem (sharpen or shorten the Turing corollary)
- The shortest correct proof that every Turing degree occurs: are Sturmian subshifts best, or substitutions, or Toeplitz subshifts with a prescribed skeleton?
- tt- or m-degree refinements; the conjugacy problem.
- Whether the corollary should stay if sk-rigidity-* gives "continuum many" more beautifully.

Deliverable: a proposal replacing l.229-262, if it is better. Peers: sk-rigidity-ring, sk-referee-2.

## sk-universal-embedding-a (every f.g. residually finite group embeds in an infinite simple Kazhdan LEF group?)
Route:
- For f.g. residually finite Γ, take a free minimal Toeplitz subshift X ⊆ A^Γ (Krieger, Cortez–Petite). It should have exact finite pattern models along a chain of finite-index normal subgroups.
- R = LC(X,F_2) ⋊ Γ is f.g. and simple.
- The tower argument gives simplicity of EL_3(R), EJZ gives (T), and the exact models give LEF.
- CORRECTED ~19:30: γ ↦ diag(u_γ, u_γ^{-1}, 1) is NOT a homomorphism for nonabelian Γ. A correct map is g ↦ diag(u_g,1,1) on [Γ,Γ]. So first embed Γ in the derived subgroup of a f.g. residually finite group (or LEF group), or find another map.

Verify every step: topological freeness versus freeness; existence of Toeplitz subshifts with a FREE action for every RF group; exactness of the models; the centre.

Then push further: every f.g. LEF group? The target is "a f.g. group is LEF iff it embeds in an infinite f.g. simple Kazhdan LEF group". Prior art: embeddings into simple (T) groups and into simple LEF groups; Kionke–Schesler Thm 1.2. Deliverable: a proposal, ideally a corollary with a few-line proof. Peers: sk-universal-embedding-b, sk-general-actions-a.

## sk-universal-embedding-b (the same target, starting from LEF groups directly)
- For a f.g. LEF group Γ, build a free minimal Γ-subshift whose finite patterns are exactly realized on finite approximating sets, starting from a LEF sequence of partial actions.
- Or embed Γ in some G_{X'}, after first embedding Γ in a f.g. group with a good action.

Aim at the iff theorem, and model-test against non-LEF groups. Peer: sk-universal-embedding-a.

## sk-fp-sofic-a (frontier: a finitely presented infinite simple Kazhdan sofic group)
An f.p. LEF group is RF (Vershik–Gordon), so an infinite simple LEF group is never f.p. The f.p. sofic question is therefore the natural next one, and an answer would transform the note.
- Confirm it is open, including the soficity status of the Caprace–Rémy Kac–Moody lattices.
- Route:
  - EL_n(R)/Z for an f.p. simple ring R whose EL_n is sofic, e.g. crossed products of aperiodic minimal Z² SFTs such as Labbé's 19 tiles;
  - St_n(R) f.p. for n ≥ 4 (EJZ);
  - finite normal generation of K_2.
- Start from the landings on main: grep `fp-simple-sofic` and `fp-kazhdan`.

Deliverable: Cairn progress. A sentence goes in the note only if something is proved. Peer: sk-fp-sofic-b.

## sk-fp-sofic-b (frontier, independent start: soficity over Z²)
Is EL_3(LC(X,F_2) ⋊ Z²) sofic or hyperlinear for an aperiodic minimal SFT X?
- Periodic pattern models fail at every scale, so exact LEF is impossible.
- Look for Hamming-metric approximations (the rank metric does not give permutation models), weak soficity, or an obstruction.

Start from the Labbé ring nodes on main (grep `labbe`). Peer: sk-fp-sofic-a.

## sk-open-1 … sk-open-6 (open explorers)
Each explorer first lands `research/artifacts/sk-open-<k>-plan-2026-09-13.md` (at most 60 lines: the target, why it is beautiful and high impact, and which running lane it does not duplicate), then pursues it.
- sk-open-1: the single most beautiful theorem this note could end with.
- sk-open-2: one page that proves everything. Radical simplification; a different ring or group with a shorter proof of all four properties is allowed.
- sk-open-3: the object itself. The Fibonacci group G_Fib: explicit computations (first models, Kazhdan constant bounds, generators, small structure) that make the note useful.
- sk-open-4: the dictionary between dynamics and the group. Which properties of X (entropy, complexity, eigenvalues, linear recurrence, orbit equivalence class) are visible in G_X?
- sk-open-5: the questions the note should end with. Sharp open problems whose answers would matter; settle any that fall quickly.
- sk-open-6: free taste.

## sk-exposition (structure and prose)
Judge the title, abstract, opening, section structure and sentence-level quality of the disk text against RULES §6 and against the best short notes (two-to-eight-page Annals and Inventiones papers). Give proposals as verbatim before/after pairs. Do not change the credit wording or the lineage. Refresh the proposal once, after sk-proof-minimal-* land. Peers: sk-proof-minimal-concrete, sk-proof-minimal-conceptual.

## sk-verify-3 (verifier: embeddings, rigidity, frontier)
Phase 1: independently review the un-* results a generalized note might rely on:
- `steinberg-elementary-groups-are-simple-mod-centre`;
- `lef-el-groups-force-exactly-matricial-simple-ring`;
- the RF Toeplitz theorem in `un-rf-beyond-free-2026-09-13-part{1,2}.md`;
- `subshift-crossed-product-k0-is-coinvariant-group`.

Phase 2: verifier for `$SK/queue/sk-verify-3.txt`, with verdicts in `research/artifacts/sk-review-3-2026-09-13-partK.md` and the same waiting rule as sk-referee-1.
