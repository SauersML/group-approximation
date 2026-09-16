# Swarm note: pure-braid-bnsr-complements-are-real-resonance-varieties (2026-09-16)

Agent: `swarm-pure-braid-bnsr-complements-ar`. Lock on the target (TTL 180m), taken
about 02:37 UTC and released at the end of the lane. Nothing committed.

Outcome: partial progress plus a reduction. The target is still open. It now
reduces to one new hole: non-resonant zero-sum characters on the twist hyperplanes,
in degrees `2 <= m <= n - 3`.

## 1. Orientation

The target asks for `Sigma^m(P_n) = S \ S(R^{<=m}(P_n; R))` for all `n`, `m`.
State on entry:

- The upper bound is proved in general (`arrangement-bnsr-invariants-avoid-real-resonance`).
- `m = 1` is known (KMM with Cohen–Suciu).
- `m >= n - 2` is known (`pure-braid-top-bnsr-invariants-are-center-nonvanishing`).
- The obstructions are proved: product projections, sunflowers, and pencils meeting in two points.
- The Attempts on the target say "membership ... unproved in every middle case".

The only membership results in the middle range were Zaremsky's Proposition 5.6
(one sign, no zero coefficient: `Sigma^{n-3}`) and the central-element criterion.
So the lane looked for a membership criterion. It used the one tool that sees
more than the full twist: Meier–Meinert–VanWyk on the curve complex of `D_n`,
whose simplex stabilizers contain central Dehn twists with values
`c_A = sum_{i<j in A} a_ij`. `bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`
already suggested this tool.

Nodes read:
- the target;
- `pure-braid-product-projections-obstruct-bnsr-invariants`;
- `pure-braid-sunflower-characters-obstruct-bnsr-invariants`;
- `pure-braid-pencils-meeting-in-two-points-miss-sigma-two`;
- `pure-braid-middle-bnsr-from-resonance-sharpness`;
- `braid-arrangement-higher-resonance-varieties-computed`;
- `bf-n-r-twist-invisible-restrictions-nonresonant` and its route;
- the artifacts `zp-pure-braided-bht-sigma-2026-09-13.md` (tool quotations) and
  `zp-pure-braid-bnsr-top-range-2026-09-13.md` (Theorem T, Lemma L).

## 2. Literature gate

WebSearch was exhausted for this session. arXiv listing searches for 2024–2026 on higher
BNSR invariants, pure braid groups and resonance found no statement of the target or of the results
below. Later arXiv API calls failed with connection resets.

- Zaremsky, arXiv:1507.08597v1: Proposition 5.6 and Theorem 5.7 re-read from the
  PDF on 2026-09-16. The positive half of 5.6 is contained in Theorem M below.
- Zaremsky, arXiv:1803.02717v1: Citations 1.8 (MMV Thm 2.4), 1.9 (Meinert
  Cor 2.8) and 1.12 (MMV Thm 2.1), quoted verbatim in the artifact.
- Davis–Huang, arXiv:2003.13553v2: Theorem 5.12 and the type `A_{n-1}` remark,
  used for the connectivity of `C(S_{0,n+1})` (Harer; Harer's paper was not
  re-read).
- arXiv:2502.16026 (tropical integral jump loci, 2025-02): abstract only, upper
  bounds for BNSR invariants. Not re-fetched; unverified beyond the abstract.
- Broaddus arXiv:0711.0011: checked and not applicable.

Novelty is bounded. Theorem M is a direct application of MMV to the curve complex,
so an earlier statement may have been missed.

## 3. Mathematics

Full proofs: `research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md`.

**Theorem M** (`pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3`, direct
proof route). If `n >= 4` and `c_A != 0` for all `2 <= |A| <= n - 1`, then `[chi]` is
in `Sigma^{n-3}(P_n)`. Proof: run (T1) on `C(D_n)`, which is `(n-4)`-connected.

- Simplex stabilizers fix each curve (the types are distinct and laminar).
- Each stabilizer contains the central twists `T_c` with `chi(T_c) = c_{A(c)}`.
- Stabilizers have type `F` (cutting homomorphism).
- The action is cocompact (laminar families).

So (T2) gives `Sigma^infinity` on every stabilizer. With Theorem T, zero-sum and
all `c_A != 0` gives `Sigma^{n-3} \ Sigma^{n-2}`.

**Theorem M_d** (`pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d`, direct
proof route). Let the twist depth `d(chi)` be the largest laminar family of zero
types. If `d <= n - 4`, then `[chi]` is in `Sigma^{n-3-d}`.

- The link of an `s`-curve multicurve is a join of curve complexes of the pieces,
  and it is `(n-4-s)`-connected.
- Proof by downward induction on zero multicurves, with (T1) on the links.
- Exact on one strand block: `d = n - |A|` by counting in the rooted tree, so the
  character is in `Sigma^{|A|-3} \ Sigma^{|A|-2}`. It is not sharp in general:
  `c_12 = c_34 = 0` on `P_5` gives `d = 2`, yet the character is in `Sigma^1`.
- The level loss is the `t = 1` step of the recursion.

**Obstruction.** At a zero pair-type vertex, `Stab(c) = <T_c> x P_{n-1}` and the
restriction factors through a zero-sum character of `P_{n-1}`. By Theorem T and
(T3), it is not in `Sigma^{n-3}`. So the curve-complex criterion cannot reach
level `n - 3` on the twist hyperplanes. The splitting was not re-derived.

**Reduction** (route `pure-braid-resonance-reduces-to-zero-twist-characters` into
the target). It requires:

- the upper bound;
- KMM;
- Theorem T;
- Theorem M;
- the new hole `pure-braid-nonresonant-zero-twist-characters-in-sigma`.

The case split:

1. `sum a != 0` gives `Sigma^infinity`.
2. For `sum a = 0`, deconing gives `H^i(A) = H^i(A') ⊕ H^{i-1}(A')`, and
   `chi(A') = (-1)^{n-2}(n-2)!`. So the character is resonant in degree
   `<= n - 2`, and only `m <= n - 3` matters.
3. All `c_A != 0` is Theorem M.
4. Some `c_A = 0`: KMM for `m = 1`, the hole for `2 <= m <= n - 3`.

M_d settles the hole when `d <= n - 3 - m`. Smallest open case: `n = 5`, `m = 2`,
generic zero-sum characters with `c_12 = 0` or `c_123 = 0` (up to `S_6`).

**Lead: twist depth for bF_{n,r}.** M_d could prove parts of
`bf-n-r-twist-invisible-braid-characters-in-sigma-infinity` without the resonance
conjecture, if `k - d(Phi_k) -> infinity`.

- On the first-leaf subspace it fails. Those restrictions have `a_pq = 0` for
  `2 <= p < q <= k`, so every `A <= {2,...,k}` is a zero type and
  `d(Phi_k) >= k - 2`. This is consistent with their lying outside `Sigma^{s-1}`
  (sunflower claim).
- On all of `W_0`, intervals of `td + 1` strands are zero types (Proposition 6 of
  that lane). They force `d(Phi_k) >= floor((k-2)/(n-1))`, and that still allows
  `k - d(Phi_k) -> infinity`.
- At random points of `W_0` the depth equals this bound in every computed case
  (Section 4.1).

So twist depth cannot give the whole bF claim. It may give the claim for very
generic `phi`.

## 4. Computation

`experiments/pure-braid-bnsr-complements-are-real-res-2026-09-16/`

`twist_hyperplane_aomoto.py` writes `results.json` and `run.log`. It computes the
Aomoto complex of `P_n` over `F_p` for two primes and reports `dim H^i` for
`i <= n - 3`, plus the zero types and `d(chi)`. It reuses the Orlik–Solomon code of
`experiments/zp-bf-n-r-first-leaf-star-resonance-2026-09-16/os_resonance_bf.py`.
Characters have integer entries up to `10^4`, zero sum, and prescribed twist
hyperplanes, sampled with a triangular solve; seed 20260916. A vanishing dimension
over `F_p` is exact over `Q`.

Controls behave as expected:
- one triple in `P_5`: `H = (0, 1, 8)`;
- all rows zero in `P_5`: `(0, 0, 2)`;
- two triples in `P_6`: `(0, 0, 1, 11)`.

Every generic or twist-hyperplane sample has `H^{<=n-3} = 0`. The samples:
- `P_5`: 8 cases x 3 samples;
- `P_6`: 8 cases x 3 samples;
- `P_7`: `c_12 = 0`, one sample, 200 s.

This includes intersections of two or three twist hyperplanes. So generic points of
the twist hyperplanes are non-resonant, and the new hole is not vacuous. The
`c_12 = c_34 = 0` samples on `P_5` (`d = 2`, `H^1 = 0`) are the non-sharpness
example for M_d.

### 4.1 Twist depth of the bF_{n,r} restrictions (lead for another lane)

`bf_twist_depth.py` writes `bf_twist_depth.json` and `bf_twist_depth.log`; it
runs in under 3 s. It computes the zero types and `d(Phi_k)` of the braid
restrictions `Phi_k` (`os_resonance_bf.Phi`). The characters are two random integer
points of `W_0` (`random_W0`, scale 1000) and one first-leaf character, for
`(n, r) = (3,1), (3,2), (4,1), (4,2)` and `k` up to 13.

- Random points of `W_0`: `d(Phi_k) = floor((k-2)/(n-1))` in every case. The
  laminar search is exact (at most 150 zero types). Non-interval zero types do
  occur, for example 10 of them at `n = 3`, `k = 11`, but the depth still equals
  the interval bound. So M_d gives `[Phi_k]` in `Sigma^{k-3-floor((k-2)/(n-1))}(P_k)`
  at these points: levels 1, 2, 3, 4, 5 for `n = 3`, `r = 1`, `k = 5..13`, and
  levels 3, 5, 7 for `n = 4`, `r = 1`, `k = 7, 10, 13`. This is exact at the sampled
  `(phi, k)`.
- First-leaf characters: `d >= k - 2` (greedy lower bound for large `k`), so M_d
  gives nothing, as predicted in Section 3.
- The interval bound is provable. In the rooted tree of a laminar family of
  intervals of sizes `td + 1` (`d = n - 1`), each such node has a number of children
  `≡ 1 mod d`, hence at least `n`. That gives `(n-1) |L| <= k - 2`.
- Consequence if it extends: suppose that for very generic `phi` in `W_0` every
  laminar family of zero types of `Phi_k` has size `<= floor((k-2)/(n-1))`, or
  just `k - d(Phi_k) -> infinity`. Then Lemma 5 of `zp-pure-braided-bht-sigma-2026-09-13.md`
  would put those `chi` in `Sigma^infinity(bF_{n,r})` with no resonance input.
  The first-leaf subspace shows that twist depth cannot give the whole claim
  `bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`.
- Not proved: which subsets are identically zero types on `W_0`, and the depth
  bound for all `k`. This is only evidence. No node was written for it, because it
  belongs to the bF lane.

## 5. Files and weakest steps

New nodes (all UNREVIEWED):
- `research/pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3.md`, a claim, with its direct route
  `-proof`;
- `research/pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d.md`, a claim, with its direct route
  `-proof`;
- `research/pure-braid-nonresonant-zero-twist-characters-in-sigma.md`, a new hole with Attempts;
- `research/pure-braid-resonance-reduces-to-zero-twist-characters.md`, a route into the target.

Artifact: `research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md`.

No existing node was edited.

Weakest steps, most fragile first:

1. Lemma 5 and Lemma 3(b) of the artifact. The link of a multicurve is the join
   of the curve complexes of the pieces, and `Stab(sigma)` acts cocompactly on
   it. Both are standard, but only sketched. Harer's connectivity comes through
   Davis–Huang's identification of their `C_alg` with the curve complex, which
   was accepted from their remark.
2. Lemma 4, type `F` for stabilizers. It uses the cutting homomorphism onto
   `prod PMod(P)` with a free abelian kernel. Surjectivity onto the pure classes
   of the pieces is asserted from Farb–Margalit without re-reading.
3. Lemma 7, the downward induction. The cells of `L(sigma)` have to be
   classified correctly as "adds a nonzero curve" or "larger zero multicurve".
4. The vertex obstruction (`Stab(c) = <T_c> x P_{n-1}` by cabling) is used only
   heuristically. It is not a proof step of any route.
5. The reduction's decone identity `A = A' ⊗ Λ(e_12)` with `chi` in `A'` is
   standard (Orlik–Terao) but was not re-read.

Next steps for the swarm:
- Attack `n = 5`, `m = 2` on `c_12 = 0` directly. Morse theory on a Brady-type
  complex for `P_5`, or MMV on the curve complex with the zero pair vertices
  deleted, handling the lost connectivity by a Bestvina–Brady-style link
  condition.
- bF lane: prove that for very generic `phi` in `W_0`, every laminar family of zero
  types of `Phi_k` has size at most `floor((k-2)/(n-1))` (Section 4.1). Before
  that, identify the subsets that are zero types identically on `W_0`. The first test is the non-interval ones found at both sampled points for
  `n = 3`, `r = 1`, `k = 11, 13`. At other `k` the two samples differ, so some
  of those zero types are accidental.
