# Lifted, interleaved peeling-link certificates for VR(Z^n, d_1; r)

Proof route: `research/z7-rips-contractible-at-scale-10-proof.md`. It covers the reduction (lift to link dimension
k with e_k available, the (D)/(K) moves, and uniformity over boxes).

## Programs

All are single-threaded C++17. Build each with `g++ -O2 -o <name> <name>.cpp`.

### ilv2.cpp: generator, stage 1

Usage: `./ilv2 k r certfile maxC corefile`. It works on
`Lmax_k = { x in Z^k : |x|_1 <= r, x > 0 }` in four phases.

- **A.** Each balanced sphere point is deleted by its Lemma-4 dominator.
- **A'.** Slack-one sphere dominators `y ∈ hull(0,x)`, checked against the alive sphere set.
- **B.** For norms rho = r−1 down to 2, each point `x` is deleted by some alive `w ∈ hull(0,x,e_k)`, `w > 0`.
  Validity is proved by a separable bulk test plus an explicit test against the alive points of larger norm.
- **C.** Bitset greedy (D) moves on the remaining core, with dominators in `hull(0,u,e_k)`.

The certificate lines are `A|S|B|D x | w`. The surviving core is written to `corefile`.

### kcore.cpp: generator, stage 2

Usage: `./kcore k r corefile - certfile 64 1100`. It removes the core with (D) moves and K moves.

A K move deletes u as follows:
1. Pick `w ∈ hull(0,u,e_k)` adjacent to `u`. Let `B = N(u) ∩ C \ N[w]`, with `|B| <= 64`.
2. Remove each `b ∈ B` from the link by a dominator `v ∈ hull(0,u,b,e_k)`.
3. The link is now a cone on `w`.

Certificate lines are `D x | w`, or `K u | w m` followed by m lines `b | v`.

### vcert.cpp: independent verifier

Usage: `./vcert k r certfile...`. It replays the certificate files in order on a presence bitmap of `Lmax_k`.
- It checks every move directly: membership, hulls, and an exhaustive DFS over `z` for a violation of the
  domination or cone condition.
- It then checks that exactly `{e_k}` remains.
- It uses no lemma about balanced or slack-one points.

## Reproduce (7,10)

```sh
for k in 2 3 4 5 6 7; do
  ./ilv2 $k 10 a$k.txt 120000 core$k.txt
  ./kcore $k 10 core$k.txt - b$k.txt 64 1100
  cat a$k.txt b$k.txt > cert-7-10-k$k.txt
  ./vcert $k 10 cert-7-10-k$k.txt
done
```

The certificates are in `certs/` (gzip, 1.4 MB in total). The verifier reads them with
`./vcert k 10 <(zcat certs/cert-7-10-k$k.txt.gz)`. Output is in `results.txt`. At k = 7 the generators take a few
minutes and the verifier about 50 s.
