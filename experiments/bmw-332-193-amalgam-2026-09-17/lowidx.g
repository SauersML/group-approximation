# usage: set FN, TL (index of letter to test, 1-based), N, then Read this
Read(FN);
L:=LowIndexSubgroupsFpGroup(A,G1,N);;
Print(FN," #subgroups of index<=",N," containing G1: ",Length(L),"\n");
good:=Filtered(L,H->not ag[TL] in H);;
Print("  not containing letter ",TL-1,": ",Length(good),"\n");
if Length(good)>0 then
  H:=good[1]; Print("  index ",Index(A,H),"\n");
  hom:=FactorCosetAction(A,H);
  Print("  perms: ",List(ag,g->Image(hom,g)),"\n");
fi;
