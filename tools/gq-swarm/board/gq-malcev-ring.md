# gq-malcev-ring board
**Approach:** family rings/K-theory. Original idea (Toeplitz isometry + telescoping mean operator h, h - s*hs = h·s*hs,
Q in the corner 1-ss*) DUPLICATES landed work (gq-ring-fp-simple's R_T, R_L; gq-cuntz-cstar's C_h), so it is not landed.
Switched to obstructions for ring-built simple hosts.
**Established:**
- 7ce417eef harmonic-cuntz-simple-group-is-not-finitely-presented (+ -proof). EL_3(C_h) is perfect with non-f.g. central
  Q^x, so Λ_h has no finite presentation. REFUTES harmonic-cuntz-simple-group-is-finitely-presented (refuted_by added);
  routes gl-n-q-via-harmonic-cuntz-host and rational-leavitt-fp-simple-via-harmonic-host are dead.
- 449689bb2 rational-leavitt-path-k1-k2-scalar-dichotomy (+ -proof). For L_Q(E): Q^x -> K_1 has f.g. kernel iff [1] has
  infinite order, and then K_2(Q) -> K_2 has non-f.g. image. So the purely infinite host escape is paid in K_2.
**Needs:** a f.p. ring R ⊇ Q, purely infinite simple, with ker(Q^x -> K_1(R)) f.g. AND image(K_2(Q) -> K_2(R)) f.g.;
  also K_2(N,R) centrality for purely infinite simple rings (for the K_2 half to obstruct).
**Dead:** Toeplitz/Cohn corner rings as SIMPLE hosts: every simple ring with Q in a corner is a Q-algebra (centre is a
  field of char 0), so the corner trick gives no escape from central scalars.
**Sparks:** in the 2-vertex graph (1: 2 loops + 2 arrows to 2; 2: 1 arrow to 1 + 3 loops), K_0 = Z with [1] a
  generator. Try a resolvent or harmonic completion over it and compute whether K_2(Q)·[1] dies.
