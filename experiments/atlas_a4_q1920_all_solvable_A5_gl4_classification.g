# Exhaust perfect split solvable-by-A5 action images on F3^4.  Structural
# Fitting arguments reduce the possible orders to 60*2^a*3^b with
# 0<=a<=7, 0<=b<=5.  A nontrivial 3-core acts trivially on every irreducible
# module in characteristic three, so only zero-3-core candidates need a
# four-dimensional representation calculation.

field:=GF(3);;
candidateCount:=0;;
nontrivial3CoreCount:=0;;
zero3CoreCount:=0;;
faithfulNontrivialRadicalCount:=0;;
profiles:=[];;

for exponent2 in [0..7] do
  for exponent3 in [0..5] do
    order:=60*2^exponent2*3^exponent3;;
    for identifier in [1..NrPerfectGroups(order)] do
      group:=PerfectGroup(order,identifier);;
      radical:=SolvableRadical(group);;
      if Size(radical)=2^exponent2*3^exponent3 and
         Size(group/radical)=60 and IsSimple(group/radical) and
         Length(ComplementClassesRepresentatives(group,radical))>0 then
        candidateCount:=candidateCount+1;
        core3Order:=Size(PCore(group,3));;
        imageOrders:=[];
        if core3Order>1 then
          nontrivial3CoreCount:=nontrivial3CoreCount+1;
        else
          zero3CoreCount:=zero3CoreCount+1;
          moduleData:=IrreducibleModules(group,field);;
          modules4:=Filtered(moduleData[2],module->module.dimension=4);;
          imageOrders:=List(modules4,
                            module->Size(Group(module.generators)));
          if Size(radical)>1 and order in imageOrders then
            faithfulNontrivialRadicalCount:=
                faithfulNontrivialRadicalCount+1;
          fi;
        fi;
        Add(profiles,[order,identifier,Size(radical),core3Order,
                      Length(ComplementClassesRepresentatives(group,radical)),
                      imageOrders]);
      fi;
    od;
  od;
od;

Print("candidate_count=",candidateCount,"\n");
Print("nontrivial_3core_count=",nontrivial3CoreCount,"\n");
Print("zero_3core_count=",zero3CoreCount,"\n");
Print("profile_[order,id,radical,3core,complements,4d_image_orders]=\n");
for profile in profiles do Print(profile,"\n"); od;
Print("faithful_nontrivial_solvable_radical_count=",
      faithfulNontrivialRadicalCount,"\n");
QUIT;
