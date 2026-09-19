# Gamma_3 is not Kazhdan: the kernels P_2 (index 27) and P_3 (index 3^6) of the
# lower exponent-3 central series; a finite-index subgroup with infinite
# abelianization refutes property (T).
F := FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
cm := function(x,y) return x^-1*y^-1*x*y; end;;
rels := [a^3,b^3,c^3, cm(cm(a,b),a), cm(cm(a,b),b), cm(cm(b,c),b), cm(cm(b,c),c),
         cm(cm(a,c),a), cm(cm(a,c),c)];;
G := F/rels;;
for cl in [1,2] do
  e := EpimorphismPGroup(G, 3, cl);;
  K := Kernel(e);;
  Print("class ", cl, "  index 3^", Log(Size(Image(e)),3),
        "  abelian invariants of kernel: ", Collected(AbelianInvariants(K)), "\n");
od;
# torsion-freeness of P_3: every finite subgroup lies in a conjugate of a
# vertex group (order 27); check the three vertex groups inject mod P_3.
e := EpimorphismPGroup(G, 3, 2);;
for pr in [[a,b],[b,c],[c,a]] do
  Print("image of vertex group ", pr, " in Gamma/P_3 has order ",
        Size(Subgroup(Image(e), List(pr, w -> Image(e, MappedWord(w, GeneratorsOfGroup(F), GeneratorsOfGroup(G)))))), "\n");
od;
QUIT;
