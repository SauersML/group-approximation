# Direct side of Zaremsky Problem 1.5: type F_∞ for Artin groups without the K(π,1) conjecture

Lane z1-05-artin-direct, 2026-09-13. Root: `zaremsky-1-05-artin-groups-are-type-f-infinity`
(owner lane z1-05-artin-kpi1). Positive answer claim: `every-artin-group-is-type-f-infinity`.

## 0. Question and verdict

"Are all Artin groups of type F∞?" The natural route is the K(π,1) conjecture, since the Salvetti complex is
finite. This lane looked for a proof of type `F_∞` (or `FP_∞`) that avoids asphericity.

Verdict: no route independent of the K(π,1) conjecture was found. Every cocompact-complex version of Brown's
criterion needs exactly the connectivity that the conjecture provides. What survives is:

- a sharp criterion: type `F_{k+1}` iff the first nonvanishing homotopy module of the Salvetti complex is finitely
  generated;
- a reduction to graphs with only finite labels;
- an exact dictionary between connectivity of Deligne complexes and of Artin complexes;
- an explicit ideal of `ZA` that computes the top homology of the Artin complex.

## 1. Landed claims (all established, with complete proof routes)

| id | content | SHA |
|---|---|---|
| `artin-type-f-k-plus-1-iff-salvetti-pi-k-fg` | if `π_i(Sal) = 0` for `2 ≤ i < k`: `F_{k+1}` ⇔ `FP_{k+1}` ⇔ `π_k(Sal)` f.g. over `ZA` | 88b38960c0 |
| `artin-type-f-n-reduces-to-free-of-infinity-graphs` | `F_n` for `A_Γ` follows from `F_n` for its free-of-infinity parabolic subgroups | d7568bf260 |
| `every-free-of-infinity-artin-group-is-type-f-infinity` | OPEN; equivalent to the positive answer; lists the uncovered cases and the attempts | d7568bf260 |
| `artin-f-infinity-from-free-of-infinity-case` | route into `every-artin-group-is-type-f-infinity` | d7568bf260 |
| `artin-complex-top-homology-is-intersection-of-ideals` | `H_{n−1}(Δ(A)) ≅ ⋂_s ZA·(1 − s)`; nonzero for finite `W` | c3d49d1808 |
| `deligne-connectivity-iff-artin-complex-connectivity` | `k`-connectivity of all Deligne complexes ⇔ of all Artin complexes with infinite `W` | c3d49d1808 |

Literature inputs used in the proofs:

- van der Lek injectivity of standard parabolic subgroups (Paris 2014, Theorem 5.4, read from the PDF);
- van der Lek `A_X ∩ A_Y = A_{X∩Y}` (thesis 1983; theorem number NOT checked);
- `π_1(Sal(Γ)/W) = A_Γ` (Paris 2014, Theorem 3.10, cited on p. 8);
- Björner's nerve theorem with connectivity (JCTA 102, 2003; statement from the abstract);
- the Charney–Davis equivalence `Φ(A) ≃` universal cover of the Salvetti complex (JAMS 8, 1995, as recorded in
  Paris 2014 and Boyd 2026; not re-read from the source).

## 2. What is known in general

For every Artin group `A = A_Γ` on finite `S`:

1. `A` is finitely presented. This is the only finiteness property known for all Artin groups.
2. `Sal(Γ)/W` is a finite CW complex with one cell of dimension `|T|` for each `T ⊆ S` with `W_T` finite, and
   `π_1 = A_Γ`.
3. The modified Deligne complex `Φ(A)` is simply connected. It is a cone when `W` is finite. It is contractible iff
   the K(π,1) conjecture holds for `A`.
4. The Artin complex `Δ(A)` is connected (`|S| ≥ 2`) and simply connected when `W` is infinite. For `|S| ≥ 3` this
   follows because `A` is the colimit of the `A_{S∖{s}}` along pairwise intersections, together with Tits'
   criterion (Abels–Holz 1993). For `|S| = 2` it is a tree.
5. By `deligne-connectivity-iff-artin-complex-connectivity`, 2-connectivity of all Deligne complexes (the
   K(π,1) conjecturette `π_2(Sal) = 0`) is equivalent to `H_2(Δ(A)) = 0` for all `A` with infinite `W` and
   `|S| ≥ 3`. The conjecturette is open. Boyd, arXiv:2601.08658 §2.3.7, reports that Elias–Williamson withdrew their
   claim that [DM14] proves it. This was read through a fetch summary of the HTML version and not rechecked against
   the PDF.
6. K(π,1) is known in the classes listed in the root. With the preprint arXiv:2509.06914 (Huang–Przytycki, "We prove
   the K(π,1) conjecture for Artin groups of dimension 3", v1, September 2025) and Charney–Davis in dimension ≤ 2,
   every Artin group of dimension ≤ 3 is of type F. So an uncovered group has a free-of-infinity parabolic subgroup
   of dimension ≥ 4 and rank ≥ 5.

## 3. Direct routes tried, and where each dies

**3.1 Brown on `Φ(A)`.** `A` acts cocompactly on `Φ(A)` with cell stabilizers conjugates of spherical `A_U`, which
are of type F (Deligne). Brown's criterion gives `F_n` from `(n − 1)`-connectivity. `Φ(A)` is homotopy equivalent to
the universal cover of `Sal(A)`, so `F_∞` this way needs contractibility, which is K(π,1). Dies: it is the K(π,1)
route.

**3.2 Brown on `Δ(A)` with induction on rank.** Stabilizers are the proper standard parabolic subgroups, of type `F_∞`
by induction. Brown needs `Δ(A)` highly connected. By item 1 of the connectivity claim, under K(π,1) for the proper
parabolic subgroups `Δ(A) ≃ Φ(A)`. Unconditionally the transfer holds degree by degree. Dies: the needed connectivity
of `Δ(A)` is equivalent to that of `Φ(A)`. Only simple connectivity is available, which gives `F_2`.

**3.3 Homotopy-module criterion.** Type `F_3` ⇔ `π_2(Sal(A))` f.g. over `ZA`. Finite generation is strictly weaker
than vanishing, so this is the one place where `F_∞` could differ from K(π,1). Dies: no mechanism was found that
bounds the generators of `π_2(Sal(A)) = H_2(Φ(A))` except showing it is zero. The chain modules `C_2(Φ)` are
finitely generated permutation modules, but `ZA` is not Noetherian, so `ker ∂_2` need not be finitely generated.

**3.4 Two-out-of-three for `FP_∞` modules.** `C_i(Φ(A)) = ⊕ Z[A/A_U]` with `A_U` of type F, hence `FP_∞` modules.
Kernels, cokernels and extensions among `FP_∞` modules stay `FP_∞` (two out of three in short exact sequences). So `A`
is of type `FP_∞` as soon as each `H_i(Φ(A))`, `i ≥ 2`, is an `FP_∞` module. The same holds with `Δ(A)` if the
proper parabolic subgroups are `FP_∞`. Dies as in 3.3: no handle on these homology modules other than vanishing. In
the reverse direction, `FP_∞` of `A` does not force the individual `H_i` to be `FP_∞`, since only one of the three
terms is controlled at the middle degrees.

**3.5 Retractions, subgroups, quotients.**

- `Sal(Γ_T) ↪ Sal(Γ)` has a `W_T`-equivariant retraction (Godelle–Paris; Paris 2014, Theorem 5.1). So `π_k` of a
  parabolic Salvetti complex is a retract of `π_k` of the whole one. That transfers vanishing downward (Theorem 5.5).
  It does not transfer finite generation, because restriction to an infinite-index subgroup does not preserve it.
- `ker(A → W)` is `π_1` of the hyperplane complement, a `W`-cover of `Sal`, no easier.
- No retraction of a general Artin group onto a group of known type is known.

**3.6 Geometric models (Garside, Helly, CAT(0)).** A proper cocompact action on a contractible complex gives `F_∞`.
In the sources read here, such models are established only in classes where K(π,1) is also known (spherical and
Garside-type, FC, large type, affine). This is a bounded statement from the survey sources, not a full literature
search.

## 4. The ideal `⋂_s ZA·(1 − s)`

By `artin-complex-top-homology-is-intersection-of-ideals` it is the top homology of `Δ(A)`:

- it consists of the `x ∈ ZA` whose coefficients sum to zero along every coset `g⟨s⟩`;
- for finite `W` it contains `Σ_w (−1)^{ℓ(w)} σ(w)`, the analogue of the Steinberg element;
- for infinite `W` it vanishes when K(π,1) holds for `A`, and unconditionally in dimension ≤ 2;
- for `|S| = 3` it is `H_2(Δ(A))`, and vanishing for all rank-3 groups with infinite `W` is automatic (dimension ≤ 2).

Open question worth a lane only as a test of method: does the ideal vanish for every Artin group with infinite `W`?
A support argument works for free groups, where the tree gives an extremal point. The support of a nonzero element
has no "lonely" point: no coset `g⟨s⟩` meets it in exactly one point. In general one would need a combinatorial
convexity structure on `A` along the lines `g⟨s⟩`. None is known without normal forms, and the word problem for
general Artin groups is open. It is not recorded as an open claim, since it is a consequence of K(π,1) and does not
feed type `F_∞` directly.

## 5. What is missing, and next targets

- **T1 (smallest open finiteness step).** For an uncovered free-of-infinity graph (dimension ≥ 4, rank ≥ 5), prove
  that `π_2(Sal(A_Γ))` is finitely generated over `ZA`, i.e. type `F_3`. Even `F_3` is open for such groups.
- **T2.** `H_2(Δ(A)) = 0` for the same graphs. This gives the conjecturette, and by the dictionary it is a statement
  about fillings of 2-cycles in the Artin complex. Huang's method (fillings of cycles in spherical Deligne complexes,
  arXiv:2405.12068) is the known way in. That is K(π,1) territory, owned by z1-05-artin-kpi1.
- **Recommendation.** No family of lanes on the direct side. The direct route has no traction independent of the
  K(π,1) conjecture. Effort on Problem 1.5 is better spent on the dimension-4 free-of-infinity cases through the
  Artin-complex filling problem, where both lanes' tools meet.

## 6. Sources checked (bounded)

- arXiv abstracts: 2509.06914 (Huang–Przytycki), 2607.24659 (Paolini, spherical-type notes only), 2305.16847 and
  2405.12068 (Huang), 1007.1365 (Godelle–Paris).
- L. Paris, arXiv:1211.7339 (Ann. Fac. Sci. Toulouse 2014): pp. 1–11 and 36–46 read directly (Theorems 1.2, 5.1,
  5.4, 5.5, 5.6, Corollaries 5.7–5.8, the known-cases list on p. 9).
- R. Boyd, arXiv:2601.08658v1 (January 2026), through a fetch summary: known classes, the conjecturette, and the
  free-of-infinity reduction.
- A web search for "all Artin groups of type F_∞" found no claimed proof. WebSearch quota was exhausted after this
  pass, so the check is bounded.
