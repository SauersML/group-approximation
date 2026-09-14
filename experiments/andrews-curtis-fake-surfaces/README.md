# Andrews–Curtis: fake surfaces of small complexity

Lane `hl-andrews-curtis` (2026-09-14). See
`research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md`.

**Enumeration and census.**
- `fsenum.cpp` enumerates acyclic cellular fake surfaces of complexity t from
  per-edge sheet matchings. It keeps orbit minima and prints `t graph code
  min_disk_length`.
  - Build: `g++ -O3 -std=c++17 -fopenmp fsenum.cpp -o fsenum`.
  - Run: `./fsenum <t> classes-t<t>.txt`.
- `diag2.py <t> [nosmall]` matches the published `fakesurfaces.csv` (github.com/lucasfagan/Fake-Surfaces) against
  a class file.
- `samecheck2.py`: the duplicate-test defect example.
- `autcheck.py <tmax>`: brute-force automorphism counts.

**Certificates.**
- `fsac.py` is the independent Python model and certificate producer. Modes:
  - `graphs`;
  - `certify <classes> <out> <shard> <nshards>`;
  - `rescue <glob> <out>`;
  - `rescue2 <glob> <out>`.
- `acverify.py <records...>` is the standalone certificate checker.
- `coverage.py <t> <classes> <records...>` joins classes with checked records.

**Batch scripts.** `*.sbatch` are the MSI job scripts used: calibration, certification, rescue, t = 6.

Graph lists are cached as `graphs-t<t>.json` in the working directory on first use.
