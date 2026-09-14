# sk-free-2 plan (revised): maximal subgroups and primitive actions of G_X; generic limits (2026-09-13)

Lane sk-free-2, a free structure lane in wave 10.

**Revision.** The first plan (d093a9d574) targeted stable rank one of `R_X`. sk-free-7 landed the same target 20 s earlier ("R_X is an exchange ring of stable rank one"), so that proof is sk-free-7's. This lane keeps only its consequences:
- bounded unitriangular generation;
- `GL_n(R_X)/EL_n(R_X) ≅ K_1(R_X)`;
- the unstable K_2 layer.

They will be short conditional routes that require sk-free-7's claim, landed once its claim id exists on main. The main effort pivots to the structure targets below.

Setting: `G_X = EL_3(R_X)`, `R_X = LC(X,F_2) ⋊_T Z`, with X an infinite minimal subshift.

## Main target (M): maximal subgroups and primitive actions of G_X
Nothing on main treats maximal subgroups of G_X; the grep hits are confined-subgroup lemmas for C*-simplicity. Targets:

- **M1, independent-tuple transitivity.** For x ∈ X, let `V_x = F_2[Z]` be the orbit module (f acts on δ_n by `f(T^n x)`, u shifts). Then `G_X` acts on `V_x^3 = R_X^3 ⊗_R V_x`, and it is transitive on linearly independent k-tuples for every k. So it acts faithfully and 2-transitively on the countable set `V_x^3 ∖ {0}` = `P(V_x^3)` over F_2.
  - Proof idea: any finitely many vectors live in one pass of a Kakutani–Rokhlin tower of large height h. The note's tower embedding ψ puts `SL_{3h}(F_2)` inside G_X, acting as constant block matrices on every pass of that tower.
- **M2, continuum many maximal subgroups.** A 2-transitive action has maximal point stabilizers, of infinite index here.
  - `H_x = Stab(δ_0 e_1)` meets `e_21(LC(X,F_2))` in `e_21(𝔪_x)`, so `x ↦ H_x` is injective.
  - Each conjugacy class is countable, so G_X has continuum many conjugacy classes of maximal subgroups, and continuum many pairwise non-isomorphic faithful 2-transitive actions on countable sets.
  - Also check: are orbit modules of distinct orbits non-isomorphic, and does the G-set determine the orbit?
- **M3, maximal parabolics.** Let `P_1` be the stabilizer of the summand `e_1 R` in `R^3` (and `P_2` that of `e_1R ⊕ e_2R`). Are they maximal subgroups of G_X?
  - Route: an element `g ∉ P_1` and a small-support root element of `P_1` have a commutator landing in a finite `GL_d(F_2)` over a tower, where `P_1` restricts to a parabolic.
  - Bruhat maximality in `GL_d(F_2)` then gives `e_21(ε)`; the level-ideal covering gives `e_21(R)`, so `H = G_X`.
- **M4, stretch.** Classify the maximal subgroups of G_X that contain a root subgroup `U_12 = e_12(R_X)`. Candidates: parabolics, orbit-module stabilizers, stabilizers of non-free summands `e_V R`.
- **Model tests.** `SL_{3N}(F_2)` (the finite models: M1–M3 are classical there); `EL_3(F_2[u^{±1}])` (T with a fixed point: which steps fail?).

## Side result (B): generic limits of the finite simple models
Beyond the boundary theorem (`pestov91-four-regular-expanders-and-limits-2026-09-13.md` §3–4: the limits are the G_X over admissible X, simple iff X minimal):
- Admissible over A = infinite chain transitive = the closure T̄′[A] of infinite transitive subshifts over A (clopen in Pavlov–Schmieding's S).
- **Pavlov–Schmieding, arXiv:2203.15159, Theorem 1.3** (quote read from the arXiv PDF):
  - "A generic subshift X in the closure T̄′ of the infinite transitive subshifts has the following properties: (1) X is a regular Toeplitz subshift (and hence is minimal, uniquely ergodic, and has zero entropy) which factors onto the universal odometer (Theorem 5.15)."
  - "(3) X is strong orbit equivalent to the universal odometer, and in particular, the dimension group of X has rank one and hence no nontrivial infinitesimals (Corollary 5.32)."
- Consequences:
  - the infinite limits form a Cantor set;
  - the simple limits form a dense G_δ, and a generic limit is `G_X` over a regular Toeplitz subshift, strongly orbit equivalent to the universal odometer;
  - simplicity is Π^0_2-complete there (a dense G_δ with dense complement is not F_σ);
  - the generic limit has unsolvable word problem (the recursive languages are countable).
- Contrast, Theorem 1.2 there: in `S′` the generic subshift has every point biasymptotic to finitely many periodic orbits, so the generic `G_Y` over `S′` is not simple.

## Deliverables
- Artifact parts `research/artifacts/sk-free-2-maximal-subgroups-2026-09-13[-partK].md` and `sk-free-2-generic-limits-2026-09-13.md`.
- Claims wired to `subshift-elementary-group-simple-iff-infinite-minimal`, `subshift-algebra-groups-embed-in-marked-groups` and the boundary artifact.
- Claims queued in `$SK/queue/sk-verify-13.txt`.
