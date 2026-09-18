# Higman quotients with relators in the edge group `<a,c>` (2026-09-17, sw-053)

These computations cross-check `nilpotent-edge-images-collapse-higman-quotients`. The proof in
`higman-nilpotent-edge-collapse-proof` does not depend on them.

**Method.**
- GAP 4 coset enumeration (`CosetTableFromGensAndRels`, option `max`) on
  `H4 = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>` plus extra relators.
- Index 1 of `<a>` means the quotient is cyclic. Any quotient of `H4` is perfect, so it is then trivial.
- Index 1 of `<a,c>` under nilpotency relators means the quotient equals a nilpotent perfect group,
  so it is trivial.
- Each test runs in its own process (`run-<name>.g`, which reads `common.g`). An enumeration that hits
  the coset limit then cannot abort the other tests.

**Results** (`results-batch1.txt`; the first five rows were rerun after relaunch into `rerun-cheap.txt`;
`t1.g` gives the first two by `Size`):

| extra relators | subgroup | result |
|---|---|---|
| `[a,c]` | trivial (`Size`) | group trivial (`t1.g`) |
| `[[a,c],a], [[a,c],c]` (class 2) | trivial (`Size`) / `<a,c>` | group trivial (`t1.g`, `run-class2check.g`) |
| `(ac)^2` | `<a>` | index 1, group trivial |
| `[a,c^2]` | `<a>` | index 1, group trivial |
| `[a^2,c^2]` | `<a>` | index 1, group trivial |
| all left-normed weight-4 commutators in `a,c` (class 3) | `<a,c>` | coset limit `2*10^6` exceeded |
| `[z,z^a], [z,z^c], [z,z^(a^-1)], [z,z^(c^-1)]`, `z=[a,c]` | `<a>` | coset limit `2*10^6` exceeded |

The class-3 row is now settled by the proof: every class collapses. The metabelian-type row is not
covered by the proof, because the relators there do not make `<a,c>` virtually nilpotent. It stays
undecided by computation.

`census.g` enumerates short cyclically reduced relators `r` in `F(a,c)`, up to cyclic shift, inversion
and the swap `a <-> c`, and tests index 1 of `<a>`. Set `MAXLEN` and `LIMIT` first, e.g. prepend
`MAXLEN:=2;; LIMIT:=200000;;`. At length 2 all four canonical words give the trivial group
(`rerun-cheap.txt`); this is only a smoke test of the script.

Run a test from this directory with `nice -n 10 timeout 1200 gap -q -o 2g run-<name>.g < /dev/null`.
