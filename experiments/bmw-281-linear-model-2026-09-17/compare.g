# Invariants of M_m (semilinear Iwahori Moebius group on O/s^m, O=F_3[[s]], mobgen.py) vs K_m (#281, level m)
for m in [2,3,4] do
  Read(Concatenation("mob",String(m),".g")); Read(Concatenation("g281_",String(m),".g"));
  M:=Group(mob); K:=Group(gens);
  for Y in [M,K] do
    Print(m," size ",Size(Y)," derived ",List(DerivedSeries(Y),Size)," lcs ",List(LowerCentralSeries(Y),Size)," centre ",Size(Centre(Y))," exp ",Exponent(Y)," classes ",NrConjugacyClasses(Y),"\n");
    Print("   (order,classsize) multiset hash ", Collected(List(ConjugacyClasses(Y),c->[Order(Representative(c)),Size(c)])) , "\n");
  od;
od;
quit;
