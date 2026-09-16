# Kaplansky zero-divisor conjecture: counterexample lane (2026-09-16)

Lane `hi-coun-kaplansky-zero-divisor-conject`. Target: `kaplansky-zero-divisor-conjecture`.

## Angle

This lane analysed counterexamples and minimal counterexamples. It took two sub-angles:
- **(c)** settle a literature candidate: the Bengi--Wise groups (arXiv:2602.11819v1), which the
  root lists as "not classified here";
- **(b)** derive structural constraints on a support-minimal zero divisor.

No bounded search was run. The certificate computation is a Smith normal form script, which runs
in under a second.

## State of the art (sources, dates)

- **Known cases** are as recorded in the root node: unique products; torsion-free elementary
  amenable groups (Kropholler--Linnell--Moody); Strong Atiyah in characteristic 0; virtually
  compact special and 3-manifold groups; `p`-adic congruence kernels (Farkas--Linnell). This lane
  did not re-verify them.
- **Candidate hosts already in the graph.**
  - Arzhantseva--Steenbock Kazhdan groups, arXiv:1407.2441: hosts, not classified further.
  - Generalized Rips--Segev groups: undecided.
  - `E_3(3)`: a host only in characteristics other than 0 and 3, with a SAT census up to radii
    `(3,3)` in `e33-no-unique-product-pairs-of-small-radius`.
- **Bengi--Wise, arXiv:2602.11819v1.**
  - The e-print TeX was fetched on 2026-09-16 (`main.tex`, md5
    `59cd378f4c0c341697af4015834a326c`, tarball date 2026-02-12). The abs page for v2 returned 404
    that day.
  - The main theorem (TeX l. 503--508) claims that the doubles `D(n) = G *_{Ŷ} \underline G`,
    with `G = F *_{Ĥ} \underline F`, persistently contain Promislow's group `P`.
  - The introduction (l. 156--157) claims a finitely generated, residually finite, torsion-free
    group that persistently contains `P`. That would give a group that is not virtually UP, and a
    negative answer to Kionke--Raimbault's question on virtual diffuseness.
- **Other references.** Kionke--Raimbault, Doc. Math. 21 (2016) 873--915, and Promislow, Bull.
  LMS 20 (1988) 302--304, were taken from the Bengi--Wise bibliography and not re-fetched.
  A. Ng, arXiv:2505.23269, was cited in the source at l. 162. The arXiv fetch failed on
  2026-09-16 ("Rate exceeded"), so this lane did not check whether Ng's groups are torsion-free.
- **Bass--Serre theory** is used from Serre, *Trees* (Springer 1980), Chapter I, as elsewhere in
  the graph. Section numbers were not re-checked.

## What was proven

The long form is in `research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md`. The
certificate is `experiments/bengi-wise-double-abelianization-2026-09-16/snf.py`, whose output
`snf.out` ends `ALLOK`.

1. **`doubles-of-left-orderable-groups-are-left-orderable`** (route `requires: []`).
   - A double `A *_C \underline A` of a left-orderable `A` along any `C` is left-orderable.
   - More generally, an amalgam with a homomorphism to a left-orderable group that is injective on
     both factors is left-orderable.
   - Proof: the fold kernel meets every conjugate of the factors trivially. So it acts freely on
     the Bass--Serre tree and is free. The route proves that free groups are left-orderable (full
     Magnus proof) and that extensions of orderable groups are orderable.
2. **`promislow-group-is-not-left-orderable`** (route `requires: []`).
   - The lemma: if `c > 1` and `c^-1 s c = s^-1`, then every `s^k < c`.
   - In `P`, both Klein relations survive inverting `a` or `b`. This gives the cycle
     `c < c^2 < d < d^2 < c`.
3. **`bengi-wise-groups-are-left-orderable`** (route requires 1 and 2).
   - For every sequence `n` and every choice of `Ĥ` and `Ŷ`, `G` and `D(n)` are left-orderable,
     hence UP, domains over every field, and contain no copy of `P`.
   - The source's main theorem is false.
   - The failing step is l. 191 / l. 499. The copies `P_i` are honest doubles `K *_T \underline K`
     of the Klein bottle group, isomorphic to `Z^2 x|_{-I} Z` with `H_1 = Z ⊕ (Z/2)^2`.
   - `P` is the swap-twisted amalgam, gluing the center of one factor to a non-central element of
     the other, with `H_1 = (Z/4)^2`.
4. **`support-minimal-zero-divisor-groups-have-no-up-quotient`** (route `requires: []`). Take a
   zero-divisor pair minimizing `|supp alpha| + |supp beta|`, translated so that `1` lies in both
   supports.
   - Each support generates the same group `H`.
   - Every homomorphism from `H` to a UP group is trivial. The proof decomposes by cosets, then
     takes the unique product in a crossed-product decomposition.
   - Hence `H^ab` is finite, `H` has no nontrivial left-orderable or free quotient, and `H` is not
     locally indicable.
   - So the conjecture reduces to finitely generated torsion-free groups with no nontrivial UP
     quotient.

## Approaches tried and where each dies

## What to try next

## Recommended root Attempts update
