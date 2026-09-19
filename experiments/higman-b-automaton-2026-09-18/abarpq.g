# 2-quotients of Abar_e = < a, c | a^m, c^m, S_beta (beta in Bbar_e) >  (abar_e<e>.g from relators.py).
# A 2-quotient in which a has order m = 2^e certifies ord(a) = 2^e in Gammabar_e, by the reduction
# lemma of higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7 under (H_e) (hcheck.py).
Read(Concatenation("abar_e",String(e),".g"));; m:=2^e;;
F:=FreeGroup("a","c");; rels:=Concatenation([F.1^m,F.2^m],TwistRels(F));;
Ab:=F/rels;; Print("e=",e," Abar: ",Length(rels)," relators\n");
for k in [1..KMAX] do
  epi:=EpimorphismPGroup(Ab,2,k);; I:=Image(epi);;
  o:=List(GeneratorsOfGroup(Ab),x->Log(Order(Image(epi,x)),2));;
  Print("e=",e," class ",k," log2 size ",Log(Size(I),2)," log2 ord(a,c) ",o," t=",Runtime(),"\n");
  if o[1]>=e then
    ga:=Image(epi,Ab.1);; gc:=Image(epi,Ab.2);;
    if ForAny(rels,w->MappedWord(w,[F.1,F.2],[ga,gc])<>One(I)) then Error("relator check"); fi;
    Print("CERTIFICATE e=",e,": all ",Length(rels)," relators hold in a 2-group of order 2^",Log(Size(I),2)," in which a has order 2^",e,"\n"); break;
  fi;
od;
QUIT;
