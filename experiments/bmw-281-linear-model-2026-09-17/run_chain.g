# G_k = phi_{0^k}(Stab_{G_{k-1}}(0)) for the #281 automaton group K, computed from level N (file g281_N.g)
Read("chain.g");
for N in [4,5,6,7] do
  Read(Concatenation("g281_", String(N), ".g"));
  Print("N=", N, " [|K_N|, [|G_k| on level N-k, transitive?] k=1..N-1] = ", Chain(Group(gens), N), "\n");
od;
quit;
