# Universal noncommutative coefficient algebra for the marked collision seam on
# repeated natural PSL5(2) modules.  Requires GAP package GBNP 1.1.0.

LoadPackage("GBNP");
SetInfoLevel(InfoGBNP,1);
SetInfoLevel(InfoGBNPTime,1);

field:=GF(2);;
algebra:=FreeAssociativeAlgebraWithOne(
    field,"p11","p12","p21","p22","q");;
generators:=GeneratorsOfAlgebra(algebra);;
one:=generators[1];;
p11:=generators[2];; p12:=generators[3];; p21:=generators[4];;
p22:=generators[5];; q:=generators[6];;
zero:=Zero(algebra);;

ScalarMatrix:=function(rows)
  return List(rows,row->List(row,entry->entry*one));
end;;

t:=ScalarMatrix([
  [1,0,1,0,1],
  [1,0,0,1,1],
  [1,0,0,0,0],
  [0,1,1,1,0],
  [0,0,0,0,1]
]);;
s:=ScalarMatrix([
  [0,0,1,1,1],
  [1,0,0,1,1],
  [1,1,1,1,1],
  [0,1,1,1,0],
  [0,0,0,0,1]
]);;
c:=[
  [p11,zero,p12,zero,zero],
  [zero,p11,zero,p12,zero],
  [p21,zero,p22,zero,zero],
  [zero,p21,zero,p22,zero],
  [zero,zero,zero,zero,q]
];;
identity:=ScalarMatrix(IdentityMat(5));;

c2:=c*c+identity;;
ct3:=(c*t)^3+identity;;
collision:=t*c*s*c*(t^2)*c*s*t*c+identity;;

relations:=Filtered(Set(Concatenation(c2)),entry->not IsZero(entry));;
if not IsBound(RELATION_STAGE) or RELATION_STAGE>=2 then
  relations:=Set(Concatenation(relations,
      Filtered(Set(Concatenation(ct3)),entry->not IsZero(entry))));
fi;
if not IsBound(RELATION_STAGE) or RELATION_STAGE>=3 then
  relations:=Set(Concatenation(relations,
      Filtered(Set(Concatenation(collision)),entry->not IsZero(entry))));
fi;

Print("relation_count=",Length(relations),"\n");
npRelations:=GP2NPList(relations);;
gb:=SGrobner(npRelations);;
Print("gb_count=",Length(gb),"\n");
Print("groebner_basis=\n");
GBNP.ConfigPrint("p11","p12","p21","p22","q");
PrintNPList(gb);
Print("normal_forms=\n");
for target in [p11-one,p12,p21,p22-one,q-one] do
  PrintNP(StrongNormalFormNP(GP2NP(target),gb));
od;
if IsBound(PRINT_COLLISION_MOD_STAGE2) and PRINT_COLLISION_MOD_STAGE2 then
  reducedCollision:=Set(List(GP2NPList(Filtered(
      Set(Concatenation(collision)),entry->not IsZero(entry))),
      current->StrongNormalFormNP(current,gb)));;
  reducedCollision:=Filtered(reducedCollision,current->current<>[[],[]]);
  Print("collision_mod_stage2=\n");
  PrintNPList(reducedCollision);
fi;
QUIT;
