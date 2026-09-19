# (1) every beta'' = B-part of beta R beta^-1 acts trivially in the faithful rep of Bbar, so <<R>> <= A in Q_B;
# (2) Abar = < a, c | a^m, c^m, S_beta >;  2-quotients of Abar until ord(a) = m.  A 2-quotient in which
#     a has order m is a finite quotient of Abar, and Abar <= Qbar_B is a quotient-subgroup of Gammabar_e.
Read(Concatenation("bbar_e",String(e),"_gens.g"));; Read(Concatenation("twists_e",String(e),".g"));;
m:=2^e;; h:=[hb,hd];;
bad:=Number(BetaPP,w->Product(List(w,s->h[s[1]]^s[2]),())<>());;
Print("e=",e," elements beta with beta R beta^-1 not in A (in Q_B): ",bad," of ",Length(BetaPP),"\n");
if bad>0 then Error("twist not in A"); fi;
F:=FreeGroup("a","c");; rels:=Concatenation([F.1^m,F.2^m],TwistRels(F));;
Ab:=F/rels;; Print("e=",e," Abar: 2 generators, ",Length(rels)," relators\n");
for k in [1..KMAX] do
  epi:=EpimorphismPGroup(Ab,2,k);; I:=Image(epi);;
  o:=List(GeneratorsOfGroup(Ab),x->Log(Order(Image(epi,x)),2));;
  Print("e=",e," Abar 2-quotient class ",k," log2 size ",Log(Size(I),2)," log2 ord(a,c) ",o,"\n");
  if o[1]>=e then
    ga:=Image(epi,Ab.1);; gc:=Image(epi,Ab.2);;
    if ForAny(rels,w->MappedWord(w,[F.1,F.2],[ga,gc])<>One(I)) then Error("relator check"); fi;
    Print("CERTIFICATE: all ",Length(rels)," relators hold in a 2-group of order 2^",Log(Size(I),2),
          " in which a has order 2^",e,"\n"); break;
  fi;
od;
QUIT;
