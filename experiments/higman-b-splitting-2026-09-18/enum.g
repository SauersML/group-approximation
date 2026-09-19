# Enumerate Bbar = B/Lambda_B = image of <b,d> on S_r(v) (faithful by the kernel criterion), with words.
# Restrict first to a union of orbits on which Bbar still acts faithfully.  h(g) = perm(g)^-1 is a homomorphism.
Read(Concatenation("ball_e",String(e),"_r",String(r),".g"));
n:=LargestMovedPoint([pa,pb,pd]);; GB:=Group(pb,pd);; N:=Size(GB);; Print("e=",e," r=",r," |Bbar|=2^",Log(N,2),"\n");
orbs:=ShallowCopy(Orbits(GB,[1..n]));; Sort(orbs,function(x,y) return Length(x)>Length(y); end);;
S:=[];; sz:=1;;
for o in orbs do
  T:=Union(S,o);; s2:=Size(Group(List([pb,pd],p->RestrictedPerm(p,T))));;
  if s2>sz then S:=T;; sz:=s2;; fi;
  if sz=N then break; fi;
od;
Print("faithful union of degree ",Length(S),"\n");
if sz<>N then Error("not faithful"); fi;
Unbind(pa);; mp:=MappingPermListList(S,[1..Length(S)]);;
gb:=RestrictedPerm(pb,S)^mp;; gd:=RestrictedPerm(pd,S)^mp;; Unbind(pb);; Unbind(pd);; GB:=0;;
h:=[gb^-1,gd^-1];; PrintTo(Concatenation("bbar_e",String(e),"_gens.g"),"hb:=",h[1],";;\nhd:=",h[2],";;\n");
dict:=NewDictionary((),false);; AddDictionary(dict,());; elts:=[()];; wds:=[""];; i:=1;;
while i<=Length(elts) do
  for k in [1,2] do
    x:=elts[i]*h[k];;
    if not KnowsDictionary(dict,x) then AddDictionary(dict,x);; Add(elts,x);; Add(wds,Concatenation(wds[i],["bd"[k]]));; fi;
  od;
  i:=i+1;;
od;
Print("enumerated ",Length(elts)," elements, max word length ",Maximum(List(wds,Length)),"\n");
if Length(elts)<>N then Error("count"); fi;
f:=OutputTextFile(Concatenation("bbar_e",String(e),"_words.txt"),false);; SetPrintFormattingStatus(f,false);;
for w in wds do AppendTo(f,w,"\n"); od; CloseStream(f);;
QUIT;
