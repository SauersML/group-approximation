Read(FILE);; G:=Group(pb,pd);; t:=Runtime();; s:=Size(G);;
Print(FILE," deg=",LargestMovedPoint(G)," log2|G|=",Log(s,2)," ord b=",Order(pb)," t=",Runtime()-t,"\n");
if s < 2^40 then P:=Image(IsomorphismPcGroup(G));; Print("  class=",NilpotencyClassOfGroup(P)," derlen=",DerivedLength(P)," exp=",Exponent(P),"\n"); fi;
QUIT;
