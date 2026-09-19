# 2-quotients of Qbar_B = Gamma(3,2^e) / (Lambda_B <<[a,c]^2>>), with Lambda_B = ker(B -> Bbar_e).
# Lambda_B is normal in Gamma and equals the normal closure in B of the relators of Bbar_e in b,d,
# so Q_B = Gamma(3,2^e)/<<relators of Bbar_e>>. Qbar_B is a quotient of Gammabar_e, so any finite
# quotient of it in which a has order 2^e certifies ord(a in Gammabar_e) = 2^e. No (H_e) is used.
Read(Concatenation("bbar_e",String(e),".g"));; m:=2^e;;
G:=Group(BbarPerms);; if Size(G)<>BbarOrder then Error("order"); fi;
iso:=IsomorphismFpGroupByGenerators(G,BbarPerms);; P:=Range(iso);;
F:=FreeGroup("a","b","c","d");; a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;
brels:=List(RelatorsOfFpGroup(P),r->MappedWord(r,FreeGeneratorsOfFpGroup(P),[b,d]));;
if ForAny(brels,r->MappedWord(r,[b,d],BbarPerms)<>()) then Error("brels"); fi;
rels:=Concatenation([a^-1*b*a*b^-3, b^-1*c*b*c^-3, c^-1*d*c*d^-3, d^-1*a*d*a^-3,
  a^m, b^m, c^m, d^m, Comm(a,c)^2], brels);;
Q:=F/rels;; Print("e=",e," |Bbar|=2^",Log(Size(G),2)," Bbar relators ",Length(brels)," t=",Runtime(),"\n");
for k in KLIST do
  epi:=EpimorphismPGroup(Q,2,k);; I:=Image(epi);;
  o:=List(GeneratorsOfGroup(Q),x->Log(Order(Image(epi,x)),2));;
  Print("e=",e," class ",k," log2 size ",Log(Size(I),2)," log2 ord(a,b,c,d) ",o," t=",Runtime(),"\n");
  if o[1]>=e then
    im:=List(GeneratorsOfGroup(Q),x->Image(epi,x));;
    if ForAny(rels,w->MappedWord(w,GeneratorsOfGroup(F),im)<>One(I)) then Error("relator check"); fi;
    Print("CERTIFICATE e=",e,": all ",Length(rels)," relators of Qbar_B hold in a 2-group of order 2^",
      Log(Size(I),2)," in which a has order 2^",e,"\n"); break;
  fi;
od;
QUIT;
