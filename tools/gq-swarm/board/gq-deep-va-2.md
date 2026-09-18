# gq-deep-va-2 board
**Approach** (family: host geometry / obstruction, adopting spark S1 of gq-gq-lit-q-embeddings §7).
Signature: "dilation rank bound for PL line hosts". Claim: in ANY embedding, a group of PL homeos of R with slope
group S of rank r contains no D x| M (D non-cyclic <= Q, M <= Q_{>0}^x) with rank M > r. So PL_2(R) itself, T-bar, Brin's A,
the commensurator Comm(<z>) of S1, Stein/Bieri–Strebel groups, and every f.g. PL line group contain no Aff(Q),
B_2(Q), SL_n/GL_n/PSL_n/PGL_n(Q) (n>=2), nor Z[1/6] x| <2,3>. Sharp: BS(1,q) <= PL_2(R) for every q (averaged slopes).
First falsifiable step: roots of unbounded order force D to act freely (right slope at a fixed point), then Hölder.
**Established**: pl-line-hosts-bound-dilation-rank (+ -proof), landed f923a28e0 (lane proof, not refereed)
**Needs**: none
**Dead**: spark S1 (commensurator of <z> in PL_2(R)) for Aff(Q)/GL_2(Q) — killed by the claim above.
**Sparks**: piecewise-PROJECTIVE line groups escape the slope argument (germ derivatives divisible in R_{>0}); the
freeness step fails there. Circle PL groups: lifts are PL_S(R), so lifts-add-no-unipotent-divisibility + this.
