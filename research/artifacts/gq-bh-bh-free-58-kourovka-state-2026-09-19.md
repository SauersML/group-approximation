# Lane bh-free-58: state of its Kourovka lines (CT(Z) and 21.140), 2026-09-19

This is the consolidated hand-off.
- **Where to find it.** Each result is a node on main. Commits were checked with `git log` against
  origin/main, apart from the three 09-18 commits in the 21.73/21.74(b,c) row, which come from the
  lane board.
- **Status words.** "PASS" means a refereed PASS by the named commit, "open" means OPEN, and
  "unreviewed" means a lane proof not yet refereed.
- **Credit.** Kohl posed every problem here; the other credits are on the nodes.

## Kourovka 21.73 and 21.74(b),(c) (Kohl): settled, 09-18

| result | node | commit | status |
|---|---|---|---|
| conjugacy in CT(Z) is undecidable (Σ⁰₁-complete), already in CT_{3,5,7,11,13}(Z) | `ct-z-conjugacy-problem-is-undecidable` | a95cb1edf | PASS, conditional on Morita's universality (not read at source) |
| "only finite cycles" and "no finite cycles" are undecidable | `ct-z-finite-cycle-problems-are-undecidable` | 71b76e027 | lane proof |
| conjugacy is decidable when one element has finite order | `ct-z-finite-subgroups-are-classified-by-stabilizer-sets` | 99e1c5dc3 | lane proof |

## Kourovka 21.74(a) (Kohl): decidable on the one-prime and positive-ray side

| result | node | commits |
|---|---|---|
| decidable for every `g ∈ CT_∅(Z) ≅ V`, any moduli (holonomy maps `C^(−n)R^n` bound the odd depths) | `ct-empty-z-kourovka-21-74a-is-decidable` | 45788f2bd; **PASS** 19e10ad19 |
| 2-power (cone) sub-case, with explicit search bound | `ct-empty-z-cone-partition-question-is-decidable` | 8b7bc25d8; **PASS** 13263fb32; fix 20d3184c6 |
| odd moduli add YES instances (`n ↦ 4n, n+9, (n−3)/4` fixes each class mod 3) but split only at defect primes | `ct-empty-z-odd-moduli-split-only-at-defect-primes` | 8e6ab6f30; **PASS** 2daf9e1df |
| decidable for slopes in `γ^Z` when every modulus prime divides `γ` | `ct-p-z-positive-ray-kourovka-21-74a-is-decidable` | 5fb30fd1f; **PASS** for that case 782528f69; restricted 1ccef1e94 |
| barrier: YES sees only the coarse action; machine encodings touch only thin sets | `ct-z-21-74a-reductions-must-move-coarse-components` | 4f611e3b3; unreviewed |

Both decidability nodes record, since bdd1022e5, that 21.74(a) is not Kohl's "respected
partition" question.

**Open.**
- **(N) Neutral primes.** On a positive ray with `p ∤ γ` dividing a modulus, an attractor and a
  repeller can share a rational fixed point. Then radial partitions of unbounded depth occur. Is
  there a bounded certificate?
- **(H) Mixed-sign and rank-two slopes.** Is (a) decidable? A reduction from halting would need a
  family whose invariant clopen structure depends on halting, e.g. attractor basins that merge iff
  `M` halts, which would be a CT(Z) analogue of Belk–Bleak's Theorem 6.8. No such family is known.

## Kourovka 20.44 (Kohl): reduced to totally consumable groups

| result | node | commits |
|---|---|---|
| 3x+1-hard: `G_T` satisfies 20.44 iff 3x+1 has finitely many components on Z | `ct-z-orbit-transversal-dichotomy-is-collatz-hard` | 7b84a747f; unreviewed |
| infinitely many orbits of bounded size ⇒ positive density | `ct-z-orbit-transversal-counterexamples-need-unbounded-orbits` | 1c4a8a43c; unreviewed |
| true in V (frozen-tail invariant, letter tracking) | `ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy` | 2676555d5 (repair); **PASS** ab9d63e16 |
| true for slopes in `γ^Z`, `γ` an integer | `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44` | 50b7f0bf8; **PASS** 0de1f29ea |
| mixed-sign ray: frozen tails force finite orbits | `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits` | 59f44f3c5; unreviewed |
| cone-avoiding slope lattices (Stiemke level) trap tails; `G` finite ⇔ finitely many slopes, for every `G` | `ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails` | eb4bbf804; **PASS** 8cf408649; refined 0aa2f4ef2 |
| **for every `G`: a frozen tail anywhere ⇒ positive-density transversal** | `ct-z-frozen-tails-anywhere-give-kourovka-20-44` | bc9e6452b; **PASS** 643914a82 |
| totally consumable core (TC ⇐ finitely many orbits; TC ⇔ finite on a positive ray; `G_T` is TC) | `ct-z-totally-consumable-core-of-kourovka-20-44` | 06eb299b0; **PASS** e2b397604 (items 1–3); heuristic parts marked 6586450a5 |
| consolidated statement | `kourovka-20-44-holds-for-rank-one-slope-groups` | b4cbe8e26, da8e5dadd |

**Open. TC conjecture:** every totally consumable finitely generated `G ≤ CT(Z)` has finitely many
orbits. It implies 20.44. At `G_T` it is 3x+1 finiteness, and on trapped or dimension-1 lattices it
is open. The Mahler-3/2 link is an analogy only.

## Kourovka 19.45 and 19.46 (Kohl)

| result | node | commits |
|---|---|---|
| 19.45 YES ⇒ Collatz (`G_T` meets every hypothesis) | `kourovka-19-45-yes-implies-the-collatz-conjecture` | ebf9097e6; **PASS** (bh-ref-q11); 18.47 credit f8dd716a1 |
| 19.46 on a mixed ray: `G` finite ⇔ frozen everywhere; periodic infinite ⇒ sweeping orbit; hyperbolic-return lemma | `ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits` | 2c9cda58b; unreviewed |
| torsion and finiteness decidable on a positive ray, with computable order bounds | `ct-p-z-positive-ray-torsion-and-finiteness-are-decidable` | c91baed93; unreviewed |

**Open.** Is a periodic finitely generated group with a sweeping orbit possible? (Pumping fails as
in 2V.)

## Kourovka 21.140 (Witzel–Zaremsky): crux `basilica-hnn-extension-is-fp-infinity`

- **What was added to the crux node.**
  - `B ∈ H𝔉 ⇔ B′ ∈ H𝔉 ⇔ B~ ∈ H𝔉`, and self-similar induction is circular (df1d58b44).
  - `Σ²(B~) = ∅`, so Σ-theory cannot prove `FP_3` (e8e06719b).
  - A KBMAG search diverged under seven orderings, with BS(1,2) as the planted positive, in
    `gq-bh-bh-free-58-basilica-kbmag-2026-09-19` (dc6bf148a).
- **Open.** Is `B~` of type `FP_3`? Equivalently, is `π_2` of its presentation complex finitely
  generated over `Z B~`?
- **The two directions.** A negative needs Basilica `∈ H𝔉` (or the degree-3 Alexander test). A
  positive needs a geometric complex. No working method is known in either direction.

## Other

- **Gate 7** (ring-route imports). It is the Farrell–Jones conjecture itself: KH vanishes for every
  coefficient ring, and the K-gate is low-degree nil-vanishing (lane board). No lane can close it.
- **Referee check.** The P_eff kill (c0dfc4ce5) was checked and repaired in
  `gq-bh-bh-free-58-referee-lamp-centralizers` (49984b668).

## Lessons (all appended to LESSONS.md, 09-18/19)

1. The tame/wild line of an arithmetic host is the shape of its slope cocycle. Tame: a positive ray,
   or a conserved positive level. Wild: a dilation combined with a second direction, as in `G_T`.
2. Frozen information always gives tameness, and hard orbit questions live among totally
   consumable groups.
3. YES certificates are coarse, and machine encodings touch only thin sets.
4. Holonomy at attractor–repeller pairs pins hidden coordinates to bounded depth. Neutral primes
   are where it can degenerate.
5. Branch-group finitizations are Σ-invisible and resist finite rewriting. `F_∞` certificates
   need geometric complexes.
