# Qbar_B = (L1bar *_Bbar L2bar)/<<[a,c]^2>> (see qbar.g).  Abar = <a,c> has index <= |Bbar| in Qbar_B
# (Q_B = A.Bbar exactly), so coset enumeration over Abar terminates.  Report the index and the order of
# a in the permutation image and in the image group (lower bounds for ord(a) in Gamma(3,2^e)/<<[a,c]^2>>).
Read(Concatenation("ball_e",String(e),"_r",String(r),".g"));
L:=Group(pa^-1,pb^-1,pd^-1);; hom:=IsomorphismFpGroupByGenerators(L,GeneratorsOfGroup(L));;
rl:=RelatorsOfFpGroup(Range(hom));;
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
fg:=FreeGeneratorsOfFpGroup(Range(hom));;
Q:=F/Concatenation(List(rl,w->MappedWord(w,fg,[a,b,d])),List(rl,w->MappedWord(w,fg,[c,d,b])),[Comm(a,c)^2]);;
H:=Subgroup(Q,[Q.1,Q.3]);;
ix:=Index(Q,H);; Print("e=",e," |L1bar|=2^",Log(Size(L),2)," [Qbar_B:Abar]=",ix,"\n");
act:=FactorCosetAction(Q,H);; P:=Image(act);;
Print("e=",e," |perm image|=",Size(P)," ord of images of a,b,c,d=",List(GeneratorsOfGroup(Q),x->Order(Image(act,x))),"\n");
QUIT;
