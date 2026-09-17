# Uniform peeling certificates for VR(Z^n, d_1; r) at small scales r >= n

Worker sw-103, 2026-09-17. Zaremsky's Conjecture 1.1 in Gupta–Sarkar–Shukla, arXiv:2511.04238, says that
VR(Z^n, d_1; r) is contractible for every r >= n. GSS prove it for n <= 5 and for n = 6, r >= 10.
Zaremsky (PAMS 2025) proves r >= n^2 + n - 1 and McCarty proves r >= n(n+1). The open cases before this run
were n = 6 with r in {6,7,8,9}, and every n >= 7.

## Method (full proof in research/z6-rips-contractible-at-scales-6-to-9-proof.md)

1. VR(Z^n;r) is contractible if every VR([0,m]^n; r) is (compactness plus Whitehead).
2. Peel [0,m]^n in anti-lexicographic order. The link of the removed vertex is Flag(L(I)), where
   `L(I) = { x in I : |x|_1 <= r, x > 0 }`, `x > 0` means the last nonzero coordinate is positive, and I is
   a box that contains 0 and has some b_i >= 1.
3. **Uniform reduction.** On `Lmax = L([-r,r]^{n-1} x [0,r])`, run a sequence of moves:
   - (D) delete x if `N[x] ∩ C ⊆ N[w]` for some current w in hull(0,x), w != x;
   - (K) delete x if its link `S = N(x) ∩ C` can be emptied down to one point p in hull(0,x) by moves
     "delete y if `N[y] ∩ S ⊆ N[w]` with w in S ∩ hull(0,x,y)".

   Every point a move uses lies in a box `hull(...) ⊆ I` whenever x ∈ I. So the same sequence restricted
   to any L(I) is still valid, and `Flag(L(I)) ≃ Flag(L(I) ∩ K)` with K the set of survivors.
4. If `K = {e_1,...,e_n}`, then `L(I) ∩ K = {e_i : b_i >= 1}`. That set is nonempty and has diameter 2 <= r,
   so it spans a simplex. Every peeling link is then contractible, and so is VR(Z^n;r).

## Files

- `uniform.cpp`: the search. `g++ -O2 -o uniform uniform.cpp`, then `./uniform n r 1 K.txt cert.txt`.
  It prints |Lmax|, |K|, the move counts and the extents of K. It writes the survivors to K.txt and the
  certificate to cert.txt.
- `verify.py`: an independent numpy checker that shares no code with the search. Run
  `python3 verify.py n r cert.txt`. It rebuilds Lmax, replays every move with explicit distance checks
  (domination, hull membership, liveness, link collapse to p) and accepts only if the final set is
  {e_1..e_n}.
- `verify_fast.cpp`: a second independent checker in C++, with the same semantics as `verify.py` and no shared code.
  `g++ -O2 -o verify_fast verify_fast.cpp && ./verify_fast n r cert.txt`. It replays the n = 7 certificates in minutes.
- `typecheck.cpp`: an earlier variant. Phase 1 is D-moves only with "between" dominators. Phase 2 enumerates
  box types over K and certifies each one by greedy collapse. It is used for the D-only data and the r < n
  calibration.
- `linkcollapse.cpp`: direct recursive link collapse on boxes [0,m]^n. It gives sanity data for small boxes
  only; it is not a proof of the Z^n statement.
- `collapse.cpp`: plain domination on boxes. It makes no progress and is kept as a negative control.
- `rulecheck.py`: tests single-pass λ^{[x;S]} rules. All of them fail at n=5 r=5, which shows that
  multi-pass is needed.
- `results.txt`: the outputs of the runs, with the sha256 of each certificate.
- `certs/cert-6-{6,7,8,9}.txt.gz`: the n = 6 certificates. Gunzip one and run `python3 verify.py 6 r cert-6-r.txt`
  to check it without running the search. The n = 7 certificates (66 MB and 85 MB) are not committed. The search
  is deterministic and regenerates them. Compare the sha256 against results.txt.
- Large certificates: `python3 verify.py n r cert.txt state.npz 900` replays for at most about 900 s, saves the
  current set and its position, and resumes on rerun. The state is tied to the certificate's sha256.

## Results (see results.txt)

| n | r | Lmax | D moves | K moves | K | verifier |
|---|---|------|---------|---------|---|----------|
| 4 | 4 | 160 | 156 | 0 | e_i | ACCEPT |
| 5 | 5 | 841 | 836 | 0 | e_i | ACCEPT |
| 6 | 6 | 4494 | 4408 | 80 | e_i | ACCEPT |
| 6 | 7 | 9912 | 9782 | 124 | e_i | ACCEPT |
| 6 | 8 | 20040 | 20034 | 0 | e_i | ACCEPT |
| 6 | 9 | 37758 | 37752 | 0 | e_i | ACCEPT |
| 7 | 7 | 24319 | 23172 | 1140 | e_i | ACCEPT |
| 7 | 8 | 54272 | 53593 | 672 | e_i | ACCEPT |
| 7 | 9 | 112071 | 108368 | 3696 | e_i | ACCEPT (verify_fast only; staged search) |

**Calibration** (the method must not "prove" false statements). At r = n-1 the search stops at
K = {0,1}^n minus {0, (1,...,1)}: 6, 14, 30 and 62 points for n = 3, 4, 5, 6. The verifier replays those
certificates and prints `basis=False` with an AssertionError. Hand-corrupted dominators in a valid (5,5)
certificate are rejected with "D not dominated". On the full box I this set
spans the boundary of a cross-polytope, a sphere, so the certificate correctly fails. Scale r = n-1 is
known to be non-contractible.

D-moves alone (no K) reach e_i for (4,4), (5,5..7) and (6,8), (6,9). For (6,6) they stop at 884 survivors
and for (6,7) at 1099. The link-collapse move K is what closes those two cases.
