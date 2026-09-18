Read("mob3.g"); Read("g281_3.g"); M:=Group(mob); K:=Group(gens);
iso := IsomorphismGroups(M,K);
T := Image(iso, Stabilizer(M,1)); SK := Stabilizer(K,1);
A := AutomorphismGroup(K); Print("autsize ", Size(A), "\n");
found := false;
for a in A do
  if Image(a, T) = SK then
    f := iso*a;
    # point map: i -> j where f(Stab_M(i)) = Stab_K(j)
    pm := List([1..27], i -> First([1..27], j -> Image(f, Stabilizer(M,i)) = Stabilizer(K,j)));
    Print("CONJ ", pm, "\n"); found := true; break;
  fi;
od;
Print(found,"\n");
quit;
