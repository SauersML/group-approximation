# Exact group presentation of the marked canonical K7 extension.
# Run with GAP --bare -q. Set HRF_CLASS before Read to choose p-class.
if not IsBound(HRF_CLASS) then HRF_CLASS:=5; fi;
if not IsBound(HRF_LOGORDER) then HRF_LOGORDER:=2048; fi;
F:=FreeGroup("u0","v0","u1","v1","u2","v2");;
fg:=GeneratorsOfGroup(F);;
HRFCorner:=function(gs,j,i)
  local u,v,w,sigma;
  u:=gs[2*j+1];v:=gs[2*j+2];w:=Comm(u,v);
  sigma:=[0,-1,1][j+1];
  return u^i*v^((3*i^2) mod 7)*w^((3*(sigma+3)*i^3) mod 7);
end;;
HRFFace:=function(gs,i)
  return HRFCorner(gs,0,i)*HRFCorner(gs,1,i)*HRFCorner(gs,2,i);
end;;
rels:=List(fg,x->x^7);;
Add(rels,Comm(fg[1],fg[2]));;
for j in [1,2] do
  u:=fg[2*j+1];v:=fg[2*j+2];w:=Comm(u,v);
  Append(rels,[w^7,Comm(w,u),Comm(w,v)]);
od;
r1:=HRFFace(fg,1);;
for i in [2..6] do Add(rels,HRFFace(fg,i)*r1^-1); od;
for g in fg do Add(rels,Comm(r1,g)); od;
Bc:=F/rels;;
bcgens:=GeneratorsOfGroup(Bc);;
z:=HRFFace(bcgens,1)^-1;;
SetInfoLevel(InfoQuotientSystem,1);
Print("BEGIN class=",HRF_CLASS," relators=",Length(rels),"\n");
pq:=PQuotient(Bc,7,HRF_CLASS,HRF_LOGORDER,"combinatorial");;
epi:=EpimorphismQuotientSystem(pq);;
Q:=Image(epi);;
zimage:=Image(epi,z);;
Print("RESULT class=",HRF_CLASS," log7order=",LogInt(Size(Q),7),
      " central_order=",Order(zimage),"\n");
Print("CENTRAL_CHECK ",ForAll(GeneratorsOfGroup(Q),g->Comm(g,zimage)=One(Q)),"\n");
imgs:=List(bcgens,g->Image(epi,g));;
Print("PRESENTATION_CHECK ",ForAll(rels,r->MappedWord(r,fg,imgs)=One(Q)),"\n");
if IsBound(HRF_RESULT) then
  PrintTo(HRF_RESULT,"{\"prime\":7,\"p_class\":",HRF_CLASS,
    ",\"log7_order\":",LogInt(Size(Q),7),",\"central_order\":",Order(zimage),
    ",\"layers\":",RanksOfDescendingSeries(pq),",\"source_relators_checked\":24}\n");
fi;
if IsBound(HRF_SAVE) then SaveWorkspace(HRF_SAVE); fi;
QUIT;
