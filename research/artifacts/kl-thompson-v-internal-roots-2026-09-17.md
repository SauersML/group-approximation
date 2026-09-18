# Internal roots over Thompson's V, and why they cannot prove Kervaire--Laudenbach (2026-09-17)

This artifact supports three nodes:
- `cone-diagonal-roots-miss-a-kl-word-over-thompson-v`
- `higman-thompson-roots-miss-a-kl-word-over-thompson-v`
- `thompson-v-homomorphisms-into-higman-thompson-are-coded`

It also backs Attempt 4 of `kl-violating-equation-over-thompson-v`.

Conventions follow `research/artifacts/kl-thompson-v-generator-census-2026-09-13.md`:
- Right action, with generators `a = (00 01)`, `b = (01 10 11)`,
  `c = (1 00)` and `B = b^-1`.
- A word is a sequence of syllables `g t^(+-1)`, written with `t`/`T`.

## 1. The certificate

**The certificate.** Suppose `phi : V -> V` is injective, `t0 in V`, and
`w^phi(t0) = 1`. Then `t -> t0`, `g -> phi(g)` defines a homomorphism
`V_w -> V` that restricts to `phi` on `V`. So `V -> V_w` is injective.

**Cone-diagonal endomorphisms.** The census RETRACT certificates use
`phi = delta_k` over a complete prefix code. The search below adds masked
endomorphisms: `(P, mask)`, where `phi(g)` acts as `g` in each masked cone of
`P` and as the identity elsewhere.

| index | name | code `P` | mask |
|---|---|---|---|
| 0 | `delta1` | `""` | `1` |
| 1 | `delta2` | `0, 1` | `1 1` |
| 2 | `delta3` | `0, 10, 11` | `1 1 1` |
| 3 | `delta4` | `00, 01, 10, 11` | `1 1 1 1` |
| 4 | `g+1` | `0, 1` | `1 0` |
| 5 | `g+g+1` | `0, 10, 11` | `1 1 0` |
| 6 | `g+1+1` | `0, 10, 11` | `1 0 0` |
| 7 | `1+g+g` | `0, 10, 11` | `0 1 1` |
| 8 | `delta5` | `0, 100, 101, 110, 111` | `1 1 1 1 1` |
| 9 | `g+g+g+1` | `0, 10, 110, 111` | `1 1 1 0` |
| 10 | `g+1q` | `00, 01, 1` | `1 0 0` |

**Which of these are genuinely different.**
- `phi = (P, mask)` is conjugate in `V` to any `(P', mask')` with the same
  number of masked cones, provided unmasked cones are present in both or in
  neither.
- Conjugating `phi` by `h` turns a root `t0` into the root `h^-1 t0 h`.
- So only `delta_k` (k copies, nothing left over) and `k copies + rest` can
  differ. For example, `g+1`, `g+1q` and `g+1+1` are the same up to
  conjugacy. The table keeps them all anyway, as a check that the search does
  not favour a particular code.

## 2. Scripts

In `experiments/kl-thompson-v-internal-roots-2026-09-17/`:

| file | md5 | role |
|---|---|---|
| `rootsearch.c` | `737512749e51b39c70d6e68a9c09d006` | search; untrusted |
| `verify_roots.py` | `0cb8db02d441fb8075c91cda81b158a1` | independent verifier; trusted |
| `mkfrontier.py` | `d7ef17d436ab17b1e78e34ab8fe0dbf7` | rebuilds the frontier lists |

`verify_roots.py` uses `experiments/kl-thompson-v-census/vgroup.py`, md5
`5a57c59b59c97fe27ba02d9774f1d135`.

**`rootsearch NMAX ENDOS IN OUT [node_limit]`.**
- For each word and each listed endomorphism, it ranges over pairs of
  complete prefix codes with at most `NMAX` leaves.
- It assigns the bijection `t0` lazily, by depth-first search driven by
  symbolic simulation of cones through `w^phi`.
- `node_limit` caps the search nodes per word, endomorphism and code pair.
- Output is `<id> <word> ROOT endo=<name> t0=d:r,...` or `<id> <word> NOROOT`.

**`verify_roots.py FILE...`.** For each ROOT line it checks three things.
- The domain and range of `t0` are complete prefix codes: prefix-free, with
  Kraft sum exactly `1`.
- `phi` has at least one masked cone.
- The tree-pair product `phi(g_0) t0^(e_0) phi(g_1) ...` is the identity.

It exits nonzero on the first failure.

## 3. Calibration

**Known certificates.** Take 40 words from
`experiments/kl-thompson-v-census/retract_certificates.txt`.
`rootsearch 5 0,1,2,3,8` finds a root for all 40. `verify_roots.py` verifies
the 40 roots.

**The obstructed word.** `ctataT` gives NOROOT for endomorphisms 0--8 at
`NMAX = 5`, as `cone-diagonal-roots-miss-a-kl-word-over-thompson-v` predicts.
Section 5 proves this for every endomorphism of `V`. The same run gives
NOROOT for `btataT` and `atbtBT`.

**The census S_3.** A machine check with `vgroup.py`:

```text
order of <a,c>: 6
orders a,c,ac: 2 2 3
00101 ['00101', '01101', '1101']
0110 ['0010', '0110', '110']
1001 ['00001', '01001', '1001']
000 ['000', '010', '10']
0111 ['0011', '0111', '111']
11 ['001', '011', '11']
```

## 4. Frontier search

**Input.** `frontier_after_weight.txt`: the `90550` frontier words that remain
after the weight certificates.
- md5 `66402427f4c9be563199e98a4dec6883`
- The census frontier before weight certificates has `95770` words, md5
  `332e532dd7ccabe23ed9800d98c73b37`.

**Sample runs.** On the first `500` words at `NMAX = 5` with all
endomorphisms, hits were `delta1` 1, `g+1` 8 and `g+1q` 5; every other
endomorphism found nothing. The two `g+1` variants hit the same words, as
conjugacy predicts. On `100` words, `NMAX = 6` found twice as many hits as
`NMAX = 5`.

**Production run.** `rootsearch 6 4,0` (`g+1`, then `delta1`) on 4 chunks,
with node limit `20000`.
- The run was **stopped early**, about 30 minutes of wall time on 4 cores,
  having processed `43831` of the `90550` words.
- The unprocessed words were not searched, so they carry no result.

**Results.**
- `1495` ROOT and `42336` NOROOT.
- `verify_roots.py` verified all `1495` certificates: `g+1` 1183 and `delta1` 312.
- File: `experiments/kl-thompson-v-internal-roots-2026-09-17/root_certificates.txt`,
  md5 `c0e5b172270c391b0e469d8a65deb5b6`.
- NOROOT certifies nothing: the search is capped.

| class | processed | verified roots |
|---|---|---|
| n=6, m=2 | 4189 (all) | 172 |
| n=6, m=4 | 1756 (all) | 73 |
| n=7, m=1 | 8826 of 46556 | 215 |
| n=7, m=3 | 18490 of 27479 | 742 |
| n=7, m=5 | 10570 (all) | 293 |

**What changes.**
- For `1495` frontier words, `V -> V_w` is now certified injective, so KL
  holds for them.
- The frontier after weight and root certificates has at most
  `90550 - 1495 = 89055` words.
- The hit rate is `3.4%`. Internal roots are a thin filter on the frontier,
  and Section 5 shows they cannot be the general mechanism.

## 5. The class kill

### The obstruction

Every point of `C` lies in one of the cones `00`, `01`, `1`, and one
transposition of `F = <a,c>` fixes that cone pointwise:

| transposition | fixes pointwise |
|---|---|
| `a` | cone `1` |
| `c` | cone `01` |
| `aca` | cone `00` |

**Cone-diagonal endomorphisms** keep this structure inside each copy, so every
`phi(F)`-orbit has size 1 or 3. `cantor-homeomorphisms-miss-a-unimodular-root`,
item 2, then forbids a root of `ctataT^phi`, even in `Sym(C)`. This is
`cone-diagonal-roots-miss-a-kl-word-over-thompson-v`.

**All homomorphisms `V -> V_{n,1}`.** N. Matte Bon, *Rigidity properties of
full groups of pseudogroups over the Cantor set*, arXiv:1801.10133v2.
- The file is the arXiv PDF, md5 `8997bb368c19d3b9aa41e775db0e99f0`, with
  text extracted by pypdf on 2026-09-17.
- Theorem 11.12 with Example 11.13 says that every non-trivial `rho` is given
  by an `Omega_2`-system `T_0, T_1`, via `rho(g) = ⊔ T_{v_i}^-1 T_{w_i}`.
- The coding map `q : Z -> C` is equivariant.
- Lemma 11.8 gives `s(T_p) = q^-1(C_p)`. So a transposition that is the
  identity on `C_p` acts as the identity on `q^-1(C_p)`. The stabilizer of
  every point in the support contains a transposition, and `q` maps orbits
  onto orbits of size 3.
- So the orbit type stays `{1, 3}`, and no homomorphism `V_{ctataT} -> V_{n,1}`
  is non-trivial on `V`. This is
  `higman-thompson-roots-miss-a-kl-word-over-thompson-v`.

The citation route
`thompson-v-homomorphisms-into-higman-thompson-are-coded-citation` quotes
the statements verbatim.

**Consequence.** Kervaire--Laudenbach holds for `ctataT`: its coefficients
lie in the finite group `F`, which is hyperlinear, and localization does the
rest. So no proof of `kl-holds-over-thompson-v` can consist only of internal
roots in Higman--Thompson groups. The search of Section 4 is a tool for
individual frontier words, not a route to the general statement.

**What remains possible.**
- Mixing internal roots with localization to the coefficient subgroup.
- Ambients whose homomorphisms from `V` are not spatial in Matte Bon's sense.

## 6. Reproduction

```text
cd <scratch>
# survivors67.txt (md5 57b19f07f9f077fcd90d22c18b0e9f53) and theorems_out.txt
# (md5 86bb744f28a0d35e1fde19ebfd70b53f) are outputs of the 2026-09-13 census jobs
# (not stored in the repo); copy them here
python3 experiments/kl-thompson-v-internal-roots-2026-09-17/mkfrontier.py   # frontier.txt, frontier_after_weight.txt
split -n l/4 -d -a 2 frontier_after_weight.txt fchunk
gcc -O2 -o rootsearch experiments/kl-thompson-v-internal-roots-2026-09-17/rootsearch.c
for i in 00 01 02 03; do ./rootsearch 6 4,0 fchunk$i fout6_$i.txt 20000 & done; wait
PYTHONDONTWRITEBYTECODE=1 python3 experiments/kl-thompson-v-internal-roots-2026-09-17/verify_roots.py fout6_*.txt
```

`mkfrontier.py` hardcodes the worktree path for the two certificate lists.
