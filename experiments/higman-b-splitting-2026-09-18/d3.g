e:=7;; Read("ball_e7_r3.g");
n:=LargestMovedPoint([pa,pb,pd]);; sh:=MappingPermListList([1..n],[n+1..2*n]);;
GB:=Group(pb,pd);; sB:=Size(GB);; Print("log2|Bbar3|=",Log(sB,2),"\n");
sL:=Size(Group(pa,pb,pd));; Print("log2|L1bar3|=",Log(sL,2),"\n");
sB2:=Size(Group(pb*pd^sh,pd*pb^sh));; Print("log2|Bbar3 diag|=",Log(sB2,2),"\n");
QUIT;
