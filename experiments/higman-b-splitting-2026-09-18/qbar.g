# Qbar_B = (L1bar *_Bbar L2bar)/<<[a,c]^2>>, L1bar = L1/Lambda_B = image of <a,b,d> on S_r(v).
# g -> perm(g)^-1 is a homomorphism (GAP perms act on the right).  L2bar = sigma^2(L1bar): a->c, b->d, d->b.
# 2-quotients of Qbar_B are quotients of Gamma(3,2^e)/<<[a,c]^2>>; report ord(a) there.
Read(Concatenation("ball_e",String(e),"_r",String(r),".g"));
L:=Group(pa^-1,pb^-1,pd^-1);; hom:=IsomorphismFpGroupByGenerators(L,GeneratorsOfGroup(L));;
rl:=RelatorsOfFpGroup(Range(hom));; Print("e=",e," |L1bar|=2^",Log(Size(L),2)," relators ",Length(rl),"\n");
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
r1:=List(rl,w->MappedWord(w,FreeGeneratorsOfFpGroup(Range(hom)),[a,b,d]));;
r2:=List(rl,w->MappedWord(w,FreeGeneratorsOfFpGroup(Range(hom)),[c,d,b]));;
Q:=F/Concatenation(r1,r2,[Comm(a,c)^2]);;
old:=0;;
for k in [1..CMAX] do
  P:=EpimorphismPGroup(Q,2,k);; I:=Image(P);;
  Print("e=",e," class ",k," log2|P|=",Log(Size(I),2)," log2 ord(a,b,c,d)=",
        List(GeneratorsOfGroup(Q),x->Log(Order(Image(P,x)),2)),"\n");
  if Size(I)=old then Print("stable\n"); break; fi; old:=Size(I);;
od;
QUIT;
