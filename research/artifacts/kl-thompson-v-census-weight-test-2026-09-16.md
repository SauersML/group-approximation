# Weight-test certificates on the V census frontier (2026-09-16)

Supports `kl-thompson-v-frontier-weight-test-certificates` and its route
`kl-thompson-v-frontier-weight-test-certificates-proof`. The census and its
conventions are those of `research/artifacts/kl-thompson-v-generator-census-2026-09-13.md`.
All runs are single-threaded, each chunk under `timeout 600`.

## 1. Input: the frontier list

**Reproduction.** The frontier is rebuilt with the census scripts, unchanged:

```text
certify.py survivors67.txt theorems_out.txt -1 1
```

- `certify.py` is `experiments/kl-thompson-v-census/certify.py`, md5 `abd5af532788e5316b312e9101dd8707`.
- `survivors67.txt` has md5 `57b19f07f9f077fcd90d22c18b0e9f53`, the same as in the census artifact.
- `theorems_out.txt` has md5 `86bb744f28a0d35e1fde19ebfd70b53f`, with 97934 FRONTIER, 15204 CORNER3 and 6 POWER lines.

Keep its `FRONTIER` lines in file order. Then delete the 2164 ids of
`experiments/kl-thompson-v-census/retract_certificates.txt`.

**Result.** 95770 lines, md5 `6bf2ec0710faedddc3052805a6e9adc4`.
- The counts by `(n, m)` are 4731, 1924, 46556, 30267 and 12292, the same as
  the census frontier table.
- The md5 differs from the census's unlanded `frontier_final.txt`
  (`f080ad7195d2b0bd76ac7ebb4feffb58`). That file was assembled from job-array
  outputs, and the difference was not investigated; line order is the likely
  cause.
- Nothing below depends on it. The claim is about the listed words, each
  verified on its own.

## 2. Scripts

In `experiments/kl-violating-equation-over-thompson-v-2026-09-16/`:

| file | md5 | role |
|---|---|---|
| `weighttest.py` | `67e51c9443a2b8011cb75d3d80532565` | search (section 3); untrusted |
| `verify_weight.py` | `1b282890e3add9cf1efc93ffc9c9c38e` | independent verifier (section 4); trusted |
| `summarize.py` | `81bbd5174a9f624685b06bc8dc41d0ce` | checks outputs against the frontier order, extracts `WEIGHT` lines, tabulates |
| `weight_certificates.txt` | section 5 | the certificates |
| `run_log.txt` | none | chunk times, summary and verifier output |
| `vertexgroup.py` | `b5b585a3bf1ce431a28b4a2d64ed6a06` | the vertex-group experiment of the swarm note; not used here |

- `weighttest.py` imports `vgroup.py` (md5 `5a57c59b59c97fe27ba02d9774f1d135`)
  and `certify.py` (md5 `abd5af532788e5316b312e9101dd8707`) from
  `experiments/kl-thompson-v-census/`, unchanged.
- The run used a scratch copy of `weighttest.py` (md5
  `417f1cd271f253a5e4a45e43f5e95614`) placed next to copies of those two files.
  It differs from the landed file only by the three lines that insert the
  census directory into `sys.path`.
- `verify_weight.py` uses only the Python standard library.

**Commands.** Run in order, single-threaded, from a scratch directory:

```text
split -l 2000 -d frontier.txt pos/p_          # 48 chunks p_00 .. p_47
timeout 600 python3 weighttest.py certify pos/p_XX pos/out_p_XX pos    # each chunk in turn
python3 summarize.py pos frontier.txt weight_certificates.txt
timeout 600 python3 verify_weight.py weight_certificates.txt
```

The search result depends on wall-clock time (the 2-second limit per word), so
a rerun may certify a slightly different set. The claim is about the landed
file, which the verifier checks without any time limit.

## 3. Search (untrusted heuristics)

`weighttest.py certify IN OUT pos` processes each word as follows.
1. Build the star graph: corner `i` is the edge `t^(-e_(i-1)) -> t^(e_i)`,
   labelled `g_i`.
2. Collect the multiplicity vectors of admissible cyclically reduced closed
   paths of length at most 4. A path is admissible if its label, or its
   reversal, is the identity in exact tree-pair arithmetic.
3. Run LP prefilters (HiGHS via scipy):
   - a necessary condition with `theta >= 0`;
   - then with `theta >= 1/4`.
4. For `mu = 1/2, 1/3, 1/4`, loop up to 10 times:
   - minimize `sum theta` subject to `theta >= mu` and every collected vector
     having weight at least `2`;
   - round with `limit_denominator(24)` and clamp below at `mu`;
   - spread the remaining slack up to `n - 2` evenly over all edges;
   - run the exact verifier;
   - on failure, add up to 32 new admissible vectors.
5. Stop after 2 seconds of wall time per word.

A word with no verified `theta` is written as `FRONTIER`. None of the LP or
rounding steps is trusted: a `WEIGHT` line is emitted only after `verify()`
accepts it, and every `WEIGHT` line is then re-checked by the independent
verifier in section 4.

## 4. Verification (trusted)

`verify_weight.py` imports nothing from `vgroup.py`, `certify.py` or
`weighttest.py`. For every `WEIGHT` line it:
1. parses the word and checks:
   - `len(theta) = n` and `deg != 0`;
   - opposite-sign corners carry a letter;
   - no nontrivial rotation fixes the syllable sequence (not a proper power);
2. checks `theta >= 0`, that the zero set is at most one non-loop edge, and (WT1);
3. enumerates with an explicit stack every cyclically reduced closed path of
   weight `< 2` from both vertices;
4. for each such path, requires the letter string and its reversal to move
   one of 12 fixed 200-bit points (seed 1916) under prefix replacement, as
   explained in the route.

Any failure rejects the line.

**Tamper tests (session sample).**
- Scaling one weight by `x1`, which breaks (WT1), was rejected.
- Scaling by `x4`, which leaves a short admissible cycle under weight 2, was rejected.

## 5. Results

RESULTS-PLACEHOLDER

## 6. Samples: zero-weight edges and the ceiling of the method

These are not landed as claims. They come from a random sample of 1500
frontier classes, whose file was not landed.

- **`weighttest.py certify ... all`** also tries one zero-weight non-loop edge
  with the other weights at least `1/2` or `1/3`. On the sample it gave 215
  positive certificates and 53 one-zero certificates. All 268 passed
  `verify_weight.py`.
  - On the first 2600 frontier lines it gave 168 positive certificates and no
    one-zero ones.
  - The mode is about ten times slower, so it was not run on the whole frontier.
- **Floating-point LP profile** of the necessary condition
  (`weighttest.py profile IN OUT L`), using admissible cycles of length at most `L`:
  - 748 of 1500 feasible at `L = 4`;
  - 146 of the first 300 feasible at `L = 4`, and 116 at `L = 6`.
  - So at least about half of the frontier fails the weight test for every
    `theta`.

## 7. Trust surface

- **The weight lemma.** `kl-relative-weight-test-gives-injectivity` rests on
  the standard picture calculus: the relative van Kampen lemma and the dipole
  step. These were not re-read at source, the same trust surface as
  `kl-four-same-sign-corner-words-weight-proof`.
- **Star-graph convention.** The verifier's edge rule is the lemma's rule. The
  opposite convention `t^(e_(i-1)) -> t^(-e_i)` is the same graph with the
  vertices renamed, so it has the same closed paths and labels.
- **Generators.** The verifier's prefix maps are `a = (00 01)`,
  `b = (01 10 11)` and `c = (1 00)` with `B = b^(-1)`, read off the census
  definition. They are independent of `vgroup.py`.
- **Moved points.** A disagreement within the common prefix length is an
  exact proof of nontriviality, so no hash or float is involved in accepting
  a certificate.
- **Scope.** Only the listed words are claimed. The remaining frontier is not
  claimed to fail anything.
