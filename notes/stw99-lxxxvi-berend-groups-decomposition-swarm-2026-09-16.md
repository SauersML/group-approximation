# STW LXXXVI, Berend case: the dual-circle Rokhlin transfer is dead (swarm, 2026-09-16)

- **Target:** `stw99-lxxxvi-berend-groups-decomposition-rank` (root).
- **Lock:** held by `swarm-stw99-lxxxvi-berend-groups-dec` with TTL 180m, and
  released on completion.
- **Outcome:** obstruction to one proof strategy. The root itself is unchanged
  and still open.

## Setup

- **The ring.** `a` is a root of `f = t^3 + t^2 - 2t - 1` and `L = Z[a]`, the
  maximal order of discriminant 49. Multiplication by `a` has matrix
  `M_a = ((0,0,1),(1,0,2),(0,1,-1))`.
- **The unit group.** `Σ = <a, b> ≅ Z^2` for a unit `b` multiplicatively
  independent of `a`. The concrete cases used for data are
  `Γ_± = <a, ±(a+1)>`, where `Norm(a+1) = -1` and `Norm(-(a+1)) = +1`.
- **The algebra.** `A = C*(L ⋊ Σ) = C(T^3) ⋊ Σ`, with dual action `\hat α`
  of `T^2`. Since `a - 1` is a unit, `G^ab = Σ`, so `\hat α` is the full
  character action of `G`.

**The strategy attacked.** Suppose some closed one-dimensional `S ≤ T^2` had
`dim^c_Rok(\hat α|_S) < ∞`.

- GHS arXiv:1709.00222 Theorem 3.17(4) would give
  `dr(A^S) = dr(A ⋊ S) ≤ (d+1)(dr(A)+1) - 1`.
- Here `A^S = C*(Z^3 ⋊_h Z)` with `h` a unit of infinite order.
- This algebra is not strongly quasidiagonal (Eckhardt Theorem 3.3), so
  `dr = ∞` by Kirchberg--Winter 5.3.
- So `dr(A) = ∞` would follow.

This is the cleanest known way to push the non-strong-QD subgroups
`Z^3 ⋊ Z` up to the Berend group, which is why it was the target.

## What was proven

Full proofs are in
`research/artifacts/berend-dual-circle-rokhlin-obstruction-2026-09-16.md`.
The graph nodes are:

- `berend-dual-circles-have-infinite-rokhlin-dimension` (claim), established
  by `berend-dual-circle-rokhlin-obstruction-proof`, which requires the
  Eckhardt/Berend node;
- `berend-some-dual-circle-has-finite-rokhlin-dimension` (the hypothesis),
  now REFUTED;
- `berend-case-from-finite-dual-rokhlin-dimension`, the valid but dead route
  from that hypothesis to the root.

`check.sh` exited 0 and reports "established: ...infinite-rokhlin-dimension,
refuted: ...finite-rokhlin-dimension".

**The theorem.** Let `S ≤ T^2` be closed, and either infinite or finite with
`2 | |S|` or `3 | |S|`. Then `dim_Rok = dim^c_Rok = ∞` for `\hat α|_S`:

- on `A`,
- on every nonzero `S`-invariant ideal,
- and on `A ⊗ D` for every unital `D`.

**The steps.**

1. **Lemma 1.** A unital equivariant quotient on which some `s ≠ e` fixes
   the central sequence algebra forces infinite Rokhlin dimension.
   - The comparison map `F(I,I) → B_∞ ∩ B'` is unital, because the unit of
     `F` is the class of an approximate unit `e`, and `π_∞(e) = π_∞(e d_0) = 1`
     for any `d_0` with `π(d_0) = 1`.
   - Then choose a partition of unity with `f_i · Lt_s f_i = 0`; this gives
     `1 = 0`.
2. **Lemma 2.** On `C(Y) ⋊ Σ`, with `Y` a finite orbit, each
   `χ ∈ Stab(Y)^⊥` equals `Ad(c_χ)`, where `c_χ(γ y_0) = χ(γ)` is in `C(Y)`.
   An earlier Fourier-coefficient proof was replaced by this one-line inner
   implementation, so no faithfulness-of-expectation input is needed.
3. **Lemma 3.** For `ξ_N(w) = exp(2πi w_2/N)`, `Stab(ξ_N) = Σ ∩ (1 + NL)`,
   because the `a^2`-coordinates of `x`, `ax` and `a^2 x` are unitriangular in
   the coordinates of `x`.
4. **Lemma 4.** For `p = 2, 3`, every `Γ ≅ Z^2` in `L^×` satisfies
   `Γ ∩ (1 + p^j L) ⊆ Γ^p` for large `j`.
   - Both primes are inert.
   - `log` is valuation-preserving on `1 + p^m L_p`.
   - `Z_p`-independence of `log a^e` and `log (a+1)^e` is certified.
   - Flatness and saturation give the conclusion.
5. **Assembly.**
   - `S ∩ (Γ^p)^⊥ ≠ 1`.
   - BPP1 plus Berend put a finite orbit `ξ_{p^j}` inside the open set of
     every ideal.
   - Restriction maps the ideal onto the quotient `C(Y) ⋊ Σ`.
   - Lemmas 1 and 2 finish.

**Witnesses and certificates.** All scripts are single-threaded, run under
`timeout 600`, finish in seconds, and exit 0. They are in
`experiments/stw99-lxxxvi-berend-dual-circle-rokhlin-2026-09-16/`.

- **`stabilizers.py`** gives exact stabilizer lattices. For `p = 2` and both
  signs: `N = 4`, `v = (0,0,1)`, HNF `(2,8),(0,14)`, orbit 28. For `p = 3`:
  `b = a+1` gives HNF `(3,48),(0,78)`, orbit 234; `b = -(a+1)` gives
  `(3,9),(0,39)`, orbit 117.
- **`certificate.py`** gives hand-checkable certificates
  `(M^T)^L ≡ I mod N` together with the images of `v` under `(L/p)ε`, with
  `L = 14, 14, 78, 39`.
- **`padic_certificate.py`** computes the logs modulo `p^40`.
  - For `p = 2` (`e = 14`) all three minors have `v_2 = 4`. For `p = 3`
    (`e = 26`) the minors have `v_3 = 2, 2, 3`.
  - Additivity and `(ε^{p^K} - 1)/p^K` cross-checks both pass.
  - Exact `Γ_± ∩ (1 + p^j L)` lies in `pZ^2` from `j = 2`, for `j ≤ 8` when
    `p = 2` and `j ≤ 4` when `p = 3`.
  - It matches the matrix-side stabilizer of `v = (0,0,1)` for small `j`.
- A superseded `two_adic_certificate.py` from the same session was deleted in
  favour of `padic_certificate.py`.

## Approaches tried and exactly where each dies

1. **Dual-circle Rokhlin transfer (GHS 3.17(4)).**
   - *Where it dies:* on the finite-orbit quotients, where the dual action is
     inner. Lemmas 1 and 2 kill every infinite `S`, even without commuting
     towers.
   - *Tweaks that also die:* passing to an invariant ideal, and tensoring with
     a unital `D`. Every nonzero invariant ideal still maps onto a finite-orbit
     quotient with stabilizer in `Γ^2`.
   - *Not treated:* `A ⊗ K`, since Lemma 1 needs a unital quotient.
2. **Rokhlin dimension of the `Z^2`-action `Σ ↷ C(T^3)`.** It is infinite,
   because the trivial character is a global fixed point. In any case, the
   standard Rokhlin-dimension crossed-product theorems for `Z^d` bound nuclear
   dimension, not decomposition rank. Cao--Fang--Wu arXiv:2601.15694v2 was
   checked and preserves `dim_nuc`, not `dr`.
3. **Dynamic asymptotic dimension of the action.** It is infinite, because the
   isotropy `Z^2` at finite orbits is not locally finite. The groupoid-based
   `dr` bounds therefore do not apply.
4. **Continuous-field method of Eckhardt--Gillaspy--McKenney
   (arXiv:1706.04142v2).** It needs a large centre; here `Z(A) = C`.
5. **Strong quasidiagonality of subalgebras.** Strong QD passes to ideals and
   hereditary subalgebras, so every test of this kind is silent. The known
   non-strongly-QD algebras `C*(Z^3 ⋊ Z)` are only fixed-point subalgebras,
   and `dr` is not monotone for subalgebras.
   - Example: `C([0,1]^n) ⊆ C(Cantor) ⊆ M_{2^∞}`.
   - Milutin's lemma should even give conditional expectations for suitable
     Cantor surjections; that pointer is unverified and not used.
6. **QD traces and `Z`-stability.**
   - Every trace on `A` is quasidiagonal: faithful traces by
     Tikuisis--White--Winter (`A` is separable, nuclear and UCT), and
     non-faithful ones because they factor through subhomogeneous quotients.
     These are standard facts, not re-checked today. So the trace-based
     finite-`dr` results give no obstruction.
   - Those results need simplicity or `Z`-stability, which `A` lacks.
   - A `Z`-stabilization bound for `dr` was not verified.
7. **Tracial Rokhlin property (Mohammadkarimi--Phillips arXiv:2505.04661v1).**
   It needs simple algebras. `A` is not simple.

## Open directions (not established)

**A. Rokhlin-free descent.** By Takai duality, which is standard, for
`G = N ⋊ Z` with the gauge action of `T` on `B = C*(G) = C*(N) ⋊ Z`:
`B ⋊ T ≅ C*(N) ⊗ K(ℓ^2 Z)`.

- *What would suffice:* a bound `dr(B ⋊ T) ≤ F(dr(B))` valid for the dual
  action. Equivalently, finite `dr` would descend from `C*(G)` to `C*(N)`
  whenever `G/N ≅ Z`. With `N = Z^3 ⋊ <a>` this would prove the root.
- *Relation to the conjecture:* this descent is itself implied by Eckhardt--Wu
  Conjecture II for finitely generated `N`. It is a different formulation of
  the same difficulty, and it is recorded here only, not in the graph.
- *What this session shows:* no proof of it can go through central-sequence
  towers for the gauge action, because of the inner behaviour on finite-orbit
  quotients.

**B. Relative or "small-quotient-blind" Rokhlin conditions.** Such a condition
would ignore quotients of decomposition rank `≤ 2`. Lemma 2 says the obstruction
lives entirely on those quotients, so a transfer that is only asymptotically
Rokhlin away from them is not excluded by this note. No such theorem is known
to me; this is speculative.

**C. The order-zero lifting problem.** Lifting coloured order-zero
approximations from the norming finite-orbit quotients back to `A`, as in the
root's Attempts, is untouched.

**D. Finite `S` of order prime to 6.** This needs `Z_ℓ`-independence of the
unit logarithms: local Leopoldt, which should follow from Ax--Brumer or
Chevalley 1951. It is unverified and not needed.

## Literature gate (arXiv API and ar5iv, 2026-09-16)

A re-query at 02:03 UTC was rate-limited ("Rate exceeded"). The listing below
is from the successful queries made earlier on the same date.

- **Gardella--Hirshberg--Santiago, arXiv:1709.00222v2.** Read in text:
  Definition 1.3, Remark 1.4, Theorem 3.17(4). This is the transfer theorem
  used above.
- **Eckhardt, arXiv:1309.2205v1.** Theorem 2.4, Lemma 2.2, Theorem 3.3.
- **Eckhardt--Wu, arXiv:2408.07223v2.** Finite nuclear dimension background,
  already in the root.
- **Eckhardt--Gillaspy--McKenney, arXiv:1706.04142v2.** The
  virtually-nilpotent positive direction; its method needs a centre.
- **Gardella, arXiv:1407.1277v2, and Hirshberg--Winter--Zacharias,
  arXiv:1209.1618v2.** Rokhlin dimension background.
- **Cao--Fang--Wu, arXiv:2601.15694v2.** Nuclear dimension only.
- **Mohammadkarimi--Phillips, arXiv:2505.04661v1.** Tracial Rokhlin, simple
  algebras.
- **Checked with no bearing on the target found:** Elliott--Niu--Santiago--Tikuisis,
  arXiv:1505.06100v3; Sato, arXiv:1908.03466v2; Jacelon--Neagu,
  arXiv:2506.18352v2; Glebe--Karmakar--Moutzouris, arXiv:2605.27936v2;
  Hirshberg--Phillips, arXiv:2306.14474v2;
  Archey--Buck--Mohammadkarimi--Phillips--Seth, arXiv:2604.10080v1;
  Vaidyanathan, arXiv:2010.14034v2.
- **Correction carried over from an earlier session:** arXiv:1409.5938 is not
  Hirshberg--Phillips and must not be cited as such.

**Unverified pointers, not relied on:** Chevalley 1951 on unit congruence
subgroups; Ax 1965 and Brumer 1967 on Leopoldt for abelian fields; Milutin's
lemma.

No source found resolves `dr(C*(Z^3 ⋊ Z^2))` for the Berend groups.

## Referee (2026-09-16)

**What was checked.**

- *Sources.* I downloaded the arXiv e-print LaTeX sources of
  arXiv:1709.00222v2 and arXiv:1309.2205v1 and re-read them.
  - GHS Definition 1.3, Remark 1.4 (`dim_Rok ≤ dim^c_Rok`) and
    Theorem 3.17(4) say what the nodes cite.
  - Eckhardt Theorem 2.4, Lemma 2.2 and Theorem 3.3 say what the nodes cite.
  - I found no fabricated citations.
- *Proof.* I checked Lemmas 1–4 and the assembly by hand.
  - Lemma 1: the comparison map is unital, kills the annihilator and is
    equivariant, and the order-zero square-zero argument is correct.
  - Lemma 3: the unitriangular `a^2`-coordinate system.
  - Lemma 4: the valuation-preserving log, the flatness step and the
    saturation index.
  - Assembly: when `S` is infinite or `p | |S|`, the condition `HΓ^p ≠ Γ`
    holds.
- *Computations.* I reran all three experiment scripts. Each exited 0 with
  identical output.
- *Independent check.* I recomputed `log a^e` and `log (a+1)^e` mod `2^24`
  and `3^16`. The values agree, with minor valuations `[4,4,4]` and `[2,2,3]`.
- *Duplicates.* I found no duplicate node. The `distinct_from` entries are
  accurate.

**What was changed.**

1. *Separable became σ-unital.* Lemma 1 said "separable `I`", but `A ⊗ D`
   with a non-separable unital `D` is not separable. The lemma needs only a
   σ-unital `I`, and every unital algebra is σ-unital. I fixed this in the
   route and the artifact.
2. *(E1) removed.* The assembly used the Berend closed-invariant-set property
   (E1), which remains unverified as stated. Eckhardt states an orbit
   dichotomy, and the AMS page returned 403. I added **Lemma 3′** to the
   artifact and the route:
   - For `p ∈ {2,3}` (inert), every point of exact order `p^j` has
     stabilizer `Γ ∩ (1 + p^j L)`.
   - These points are `2p^{-j}`-dense, so every nonempty open invariant `U`
     contains a finite orbit with `Stab ⊆ Γ^p`.
   - The proof now uses only (E2), topological freeness plus ideal
     intersection, and needs no inputs at all for `I = A`.
   - New experiment files check this numerically: 146 random characters,
     0 mismatches. They are `referee_lemma3prime_check.py` and
     `referee_lemma3prime_check-output.txt`.
3. *Minor edits.*
   - The claim now says "minimal tensor product" and "nonzero unital `D`".
   - The artifact records the source re-read.

**Still unverified.**

- Kirchberg--Winter Theorem 5.3 is used only in the dead transfer route and
  in the root, not in the obstruction.
- The unit-congruence pointers listed above are not relied on.

**Verdict.** The obstruction is sound and is landed with fixes.
`berend-some-dual-circle-has-finite-rokhlin-dimension` is correctly refuted,
and the GHS transfer route is correctly dead. The root
`stw99-lxxxvi-berend-groups-decomposition-rank` remains open. Also open are
`A ⊗ K`, finite `S` of order prime to `6`, and any decomposition-rank bound
for `A ⋊ S` not based on dual Rokhlin dimension.
