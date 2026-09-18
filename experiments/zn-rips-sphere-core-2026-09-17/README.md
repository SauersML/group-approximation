# The sphere / balanced-dominator criterion for VR(Z^n, d_1; r)

This folder supports `research/zn-rips-sphere-balanced-dominator-criterion.md` and its consequences
`research/z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54.md`.

## The criterion in one line

A vector `x ∈ Z_{≥1}^s` is *balanced* if some integer `y` with `0 ≤ y ≤ x` and `y ∉ {0, x}` has `⟨σ,y⟩`
between `0` and `⟨σ,x⟩` for every `σ ∈ {±1}^s`. If every partition of `r` into at most `n` parts is balanced, then
`VR(Z^n, d_1; r)` is contractible. The proof is in `research/zn-rips-sphere-balanced-dominator-criterion-proof.md`.
A balanced `y` dominates `x` in every peeling link. After the top sphere `|x| = r` is deleted, every lower norm
collapses onto `e_k`.

## Programs

- `sphere_nop.cpp`: the proof-relevant checker.
  - Enumerates every partition of `N` into exactly `s` parts and decides balance: first via `x/gcd`, then rounded
    halves, then a complete search over `0 ≤ y ≤ x`, `1 ≤ |y| ≤ ⌊N/2⌋` (complete because `y ↦ x − y`
    preserves balance). Every `2^s` sign vector is tested.
  - Build and run: `g++ -O2 -o sphere_nop sphere_nop.cpp`, then `./sphere_nop s Nmin Nmax [printlimit]`.
  - Output per `(s, N)`: `shapes` is the number of partitions and `bad` the number of unbalanced ones, with
    examples.
- `crosscheck.py`: an independent reimplementation that uses the split form of balance and the full box. It agrees
  with `sphere_nop` on `s = 5`, `N = 5..14`, and on `s = 6`, `N = 15..18` (see `results.txt`, Section E).
- `sphere_check.cpp`: a point-level replay. It is not part of the proof, but it tests Lemma 3 and the code.
  - Build and run: `g++ -O2 -o sphere_check sphere_check.cpp`, then `./sphere_check n r`.
  - It builds `Lmax = {x ∈ Z^n : |x| ≤ r, x ≻ 0}`. For every sphere point it finds a balanced `u ∈ hull(0,x)`,
    `u ≻ 0`, `u ≠ x`, and checks `N[x] ∩ Lmax ⊆ N[u]` by explicit `d_1` computations. If no balanced `u` exists,
    it brute-forces any dominator in `hull(0,x)`. It also checks Stage 2 explicitly.
  - Explicit-check failures: 0 in every run. The fully balanced-dominated scales are exactly those the partition
    table predicts: `(3,4)`, `(4,6..8)`, `(5,8)`, `(5,10..12)`, `(6,12)`. At the unbalanced scales `(3,3)`, `(4,4)`, `(4,5)`, `(5,7)`
    and `(5,9)`, some sphere points have no dominator in `hull(0,x)` at all.

## Dead end kept for the record: the centre criterion (`helly.cpp`, `helly2.cpp`, `hellyf.cpp`)

The first attempt tried to certify every link at once with a *centre condition*:
- take a clique `V = B_{⌊r/2⌋}^+` (plus the half-sphere `T` for odd `r`);
- require every clique `σ` of the remaining link points to have a common centre in `V ∩ hull(0 ∪ σ)` within `r`
  of all of `σ`.

An exact branch and bound (`helly2`) shows that the condition holds at `(3,3..10)`, `(4,4..11)`, `(5,5..7)` and
`(6,7)`. It **fails at `(6,6)`**, and also at `(6,5)`, where a failure is expected because `r = n − 1`. `run6.log` lists the
bad cliques. But `(6,6)` is contractible
(`research/z6-rips-contractible-at-scales-6-to-9.md`), so the condition is not necessary. The variable-radius version
`hellyf` fails at `(6,6)` too.

`nop.cpp`, `nop2.cpp`, `nop3.cpp` and `nop567.log` record a stricter single-dominator test with `|y| ≤ |x|/2`
and a prescribed coordinate `k`. It fails up to `|x| ≈ 2^{s−1} + 1`, which is far worse than the balanced test.
`core.cpp`, `corehalf.cpp`, `coresum.cpp` and `cliquetest.py` are early exploratory probes.

## Results

`results.txt` concatenates the following, with section headers giving the exact commands:
- `sphere_s1-6.log`: `s = 1..6`, `N ≤ 54`;
- `sphere_s7.log`: `s = 7`, `N ≤ 54`;
- `sphere_s8.log`: `s = 8`, `N ≤ 41`. Every `N` from 8 to 37 has an unbalanced partition, and so do `N = 39` and
  `N = 41` (about 180 each). `N = 38` and `N = 40` have none;
- `sphere_check.log`;
- the Python cross-checks.
