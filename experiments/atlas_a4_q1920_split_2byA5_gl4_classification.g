# Exhaust the possible perfect split 2-by-A5 images on a four-dimensional
# F3 chief factor.  The 2-part of |GL(4,3)| is 2^9, while |A5|_2=2^2, so the
# normal 2-kernel has order at most 2^7.

field:=GF(3);;
ambient:=GL(4,3);;
if FactorsInt(Size(ambient)){[1..9]}<>ListWithIdenticalEntries(9,2) then
  Error("unexpected 2-part of GL(4,3)");
fi;

candidateCount:=0;;
faithfulNontrivialCount:=0;;
profiles:=[];;
for exponent in [0..7] do
  order:=60*2^exponent;;
  for identifier in [1..NrPerfectGroups(order)] do
    group:=PerfectGroup(order,identifier);;
    radical:=FittingSubgroup(group);;
    if Size(radical)=2^exponent and Size(group/radical)=60 and
       IsSimple(group/radical) and
       Length(ComplementClassesRepresentatives(group,radical))>0 then
      candidateCount:=candidateCount+1;
      moduleData:=IrreducibleModules(group,field);;
      modules4:=Filtered(moduleData[2],module->module.dimension=4);;
      imageOrders:=List(modules4,module->Size(Group(module.generators)));;
      faithfulCount:=0;;
      for imageOrder in imageOrders do
        if imageOrder=order then faithfulCount:=faithfulCount+1; fi;
      od;
      if exponent>0 then faithfulNontrivialCount:=
          faithfulNontrivialCount+faithfulCount; fi;
      Add(profiles,[order,identifier,Size(radical),
                    Length(ComplementClassesRepresentatives(group,radical)),
                    Length(modules4),faithfulCount,imageOrders]);
    fi;
  od;
od;

Print("GL4_3_order=",Size(ambient),"\n");
Print("GL4_3_2part=",2^9,"\n");
Print("split_perfect_candidate_count=",candidateCount,"\n");
Print("profile_[order,id,radical,complements,modules4,faithful4,image_orders]=\n");
for profile in profiles do Print(profile,"\n"); od;
Print("faithful_nontrivial_2kernel_count=",faithfulNontrivialCount,"\n");

# Calibrate the nearby nonsplit extraspecial exception explicitly.
nonsplit:=PerfectGroup(1920,6);;
nonsplitRadical:=FittingSubgroup(nonsplit);;
nonsplitModules:=Filtered(IrreducibleModules(nonsplit,field)[2],
                          module->module.dimension=4);;
Print("nonsplit_1920_profile_[radical,complements,image_orders]=",
      [Size(nonsplitRadical),
       Length(ComplementClassesRepresentatives(nonsplit,nonsplitRadical)),
       List(nonsplitModules,module->Size(Group(module.generators)))],"\n");
QUIT;
