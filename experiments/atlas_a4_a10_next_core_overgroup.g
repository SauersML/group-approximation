# Search finite symmetric overgroups of the A10 forward-collision certificate
# for the first missing large-component core edge.  A10 fixes any padded
# points.  The new first-chart involution u must complete
# <r,z,c,u>=S3 x S3 and satisfy (u*t^-1)^3=1.

if not IsBound(MAX_DEGREE) then MAX_DEGREE := 14; fi;

baseLists := [
 [1,3,5,6,2,7,4,8,9,10],
 [1,3,5,7,2,4,6,8,9,10],
 [1,4,6,2,7,3,5,8,10,9],
 [1,2,5,4,9,7,10,8,3,6],
 [2,1,3,8,9,6,10,4,5,7]
];;

Pad := function(list,degree)
  if degree=10 then return PermList(list); fi;
  return PermList(Concatenation(list,[11..degree]));
end;;

for degree in [10..MAX_DEGREE] do
  images := List(baseLists,list -> Pad(list,degree));;
  r := images[1];; z := images[2];; c := images[3];;
  t := images[4];; s := images[5];;
  A10 := Group(images);;
  ambient := SymmetricGroup(degree);;
  centralizer := Centralizer(ambient,Group([z,c]));;
  transporter := RepresentativeAction(centralizer,r,r^-1);;
  candidates := [];;
  if transporter <> fail then
    stabilizer := Centralizer(centralizer,r);;
    candidates := List(Elements(stabilizer),x -> x*transporter);;
  fi;
  candidates := Set(candidates);;
  involutions := Filtered(candidates,u -> Order(u)=2);;
  nextEdge := Filtered(involutions,u -> IsOne((u*t^-1)^3));;
  faithful := Filtered(nextEdge,u -> Order(Group([r,z,c,u]))=36);;
  Print("degree=",degree," centralizer=",Order(centralizer),
        " transporter_candidates=",Length(candidates),
        " involutions=",Length(involutions),
        " next_edge=",Length(nextEdge),
        " faithful_H=",Length(faithful));
  if Length(faithful)>0 then
    u := faithful[1];;
    Q := Group(Concatenation(images,[u]));;
    Print(" quotient_order=",Order(Q),
          " u=",ListPerm(u,degree));
  fi;
  Print("\n");
od;
