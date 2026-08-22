# Among all low-index permutation quotients of the minimal forward-collision
# presentation, test whether the first missing large-component core involution
# can be adjoined in the same symmetric group while preserving its
# H=S3 x S3 support.

if not IsBound(MAX_INDEX) then MAX_INDEX := 12; fi;

free := FreeGroup("r", "z", "c", "t", "s");;
r0 := free.1;; z0 := free.2;; c0 := free.3;; t0 := free.4;; s0 := free.5;;
b0 := s0*t0;;
q0 := t0*c0*s0*c0*t0^-1*c0*s0*t0*c0;;
gamma := free/[
  r0^3,z0^3,Comm(z0,r0),c0^2,Comm(c0,r0),c0*z0*c0*z0,
  t0^3,s0^2,(s0*t0)^2,(r0^-1*b0)^3,(z0*b0)^3,q0
];;
gg := GeneratorsOfGroup(gamma);;
subgroups := LowIndexSubgroupsFpGroup(gamma,MAX_INDEX);;

faithfulCount := 0;;
directCount := 0;;
jRecords := [];;
largeMaskRecords := [];;
bestScore := 0;;
for subgroup in subgroups do
  cosets := RightCosets(gamma,subgroup);;
  action := ActionHomomorphism(gamma,cosets,OnRight);;
  images := List(gg,generator -> Image(action,generator));;
  r:=images[1];; z:=images[2];; c:=images[3];;
  t:=images[4];; s:=images[5];; b:=s*t;;
  if Order(Group([r,z,b]))=144 and Order(Group([r,z,c]))=18
     and Order(Group([t,s]))=6 then
    faithfulCount:=faithfulCount+1;
    F:=Group([r,z,c]);;
    J:=Group([r,z,c,t]);;
    Add(jRecords,[Order(J),Order(Intersection(F,F^t))]);

    ambient:=SymmetricGroup(Length(cosets));;
    centralizer:=Centralizer(ambient,Group([z,c]));;
    transporter:=RepresentativeAction(centralizer,r,r^-1);;
    if transporter<>fail then
      stabilizer:=Centralizer(centralizer,r);;
      for x in Elements(stabilizer) do
        u:=x*transporter;
        if Order(u)=2 and IsOne((u*t^-1)^3)
           and Order(Group([r,z,c,u]))=36 then
          directCount:=directCount+1;
          Q:=Group(Concatenation(images,[u]));;
          y:=t^-1;;
          checks:=[
            IsOne((r^-1*b)^3),
            IsOne((u*y)^3),
            IsOne(((u*r)*y^-1)^3),
            IsOne((r*b*y)^3)
          ];;
          mask:=Sum(Filtered([1..4],index->checks[index]),
                    index->2^(index-1));;
          Add(largeMaskRecords,mask);
          score:=Number(checks,value->value);;
          if score>bestScore then
            bestScore:=score;
            Print("NEW_BEST score=",score," mask=",mask,
                  " degree=",Length(cosets)," Q_order=",Order(Q),
                  " J_order=",Order(J),
                  " intersection=",Order(Intersection(F,F^t)),"\n");
            Print("images=",List(Concatenation(images,[u]),
                  permutation -> ListPerm(permutation,Length(cosets))),"\n");
          fi;
          break;
        fi;
      od;
    fi;
  fi;
od;

Print("summary low_index=",Length(subgroups),
      " faithful=",faithfulCount," direct_next_edge=",directCount,"\n");
Print("J_order_intersection_histogram=",Collected(jRecords),"\n");
Print("large_core_mask_histogram=",Collected(largeMaskRecords),
      " best_score=",bestScore,"\n");
