F:=FreeGroup(7);; g:=GeneratorsOfGroup(F);;
reps:=EvalString(StringFile("q2_gap.txt"));;
out:=OutputTextFile("quotients7.txt",false);; SetPrintFormattingStatus(out,false);
PrintTo(out,"{\n");
for k in [5..11] do
  G:=F/List(reps[k],t->g[t[1]+1]*g[t[2]+1]*g[t[3]+1]);
  L:=LowIndexSubgroupsFpGroup(G,7);
  perms:=[];
  for H in L do if Index(G,H)>1 then
    hom:=FactorCosetAction(G,H);
    Add(perms,List(GeneratorsOfGroup(G),x->ListPerm(Image(hom,x),Index(G,H))));
  fi; od;
  Print(k-1," ",List(L,H->Index(G,H))," ",AbelianInvariants(G),"\n");
  AppendTo(out,"\"",k-1,"\": ",perms,",\n");
od;
AppendTo(out,"\"end\":0}\n");
QUIT;
