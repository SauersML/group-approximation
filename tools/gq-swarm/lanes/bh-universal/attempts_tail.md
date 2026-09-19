## Attempts

1. **2026-09-18 (lane bh-universal): the index obstruction is not an obstruction for `W`.**
   `integral-affine-splitting-types-have-finitely-many-tuple-orbits`: the global affine
   group `Γ_X` has finitely many orbits on ordered `k`-tuples of halving directions,
   because halvings only see `X/2X = F_2^D`.
   - The proposed proof shape is a Stein–Farley complex of expansions of `X` by
     halvings, as for `nV`, `SV_G` and Röver–Nekrashevych groups. Here the vertex
     stabilizers are built from `Γ_X`, which is finitely presented by the method of
     `finitary-steinberg-extensions-by-oligomorphic-actions-are-fp` (add translations).
   - The pair-orbit count is the one the twisted criterion uses.
   - **Still missing:**
     - finite generation of the stabilizers of halving pairs;
     - simple connectivity of descending links, where halvings of different directions
       may cross (unlike coordinate halvings, two directions `φ ≠ ψ` need not commute
       as partitions of a piece);
     - the Morse bookkeeping itself.
   Not attempted beyond this reduction.
