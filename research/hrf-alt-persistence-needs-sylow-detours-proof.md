---
rg: 2
id: hrf-alt-persistence-needs-sylow-detours-proof
kind: route
title: Pass to a Sylow preimage, use a composition series, and calibrate with the binary icosahedral extension
target: hrf-alt-persistence-needs-sylow-detours
requires: []
---

If the class dies on `L <=_f G`, it also dies on the normal core `K` of
`L`. Put `R=G/K` and choose a Sylow `p`-subgroup `P` of `R`. Its preimage
`H` has index `[R:P]` prime to `p`. A composition series of the finite
`p`-group `P` pulls back to the required chain from `H` to `K`. Conversely
the endpoint of any such chain has finite index in `G`.

For trivial coefficients, corestriction followed after restriction
`H^2(G;F_p) -> H^2(H;F_p) -> H^2(G;F_p)` is multiplication by `[G:H]`.
That scalar is invertible when the index is prime to `p`, proving
injectivity. No normality of `H` in `G` is needed.

For the calibration, simplicity and nonabelianness make `A_5` perfect,
so `Hom(A_5,C_2)=0`. No nontrivial finite `2`-group is perfect, hence its
pro-2 completion is trivial. The central extension
`SL_2(F_5) -> PSL_2(F_5) ≅ A_5` is nonsplit: the only nonidentity element
of order two in `SL_2(F_5)` is `-I`. Indeed, `X^2=I` makes `X`
diagonalizable with eigenvalues in `{1,-1}`, and determinant one forces
both eigenvalues equal. A section would lift a nontrivial involution of
`A_5` to an involution outside the kernel, which is impossible. The class
is therefore nonzero, but restricts to zero on `1`. A Sylow 2-subgroup
of `A_5` is `V_4`, giving the stated indices.

This example refutes the general inference from `H^1(G;F_p)=0` to
persistence. It is a finite calibration, not an example with the
torsion-free infinite kernel hypotheses of the candidate triangles.
