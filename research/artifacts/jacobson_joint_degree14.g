# Exact degree-14 permutation-completion probe for the two joint cells.
# Run remotely on MSI; not a Cairn proof artifact.

x12 := (2,3)(6,7);;
x23 := (4,6)(5,7);;
x31 := (1,5)(3,7);;
x13 := (4,5)(6,7);;
x32 := (2,6)(3,7);;
b23 := (2,4)(3,5);;
rho3 := (1,2,4)(3,6,5);;

HeadPerm := function(p)
  local l, i;
  l := [1..14];
  for i in [1..7] do l[i] := i^p; od;
  return PermList(l);
end;
TailPerm := function(p)
  local l, i;
  l := [1..14];
  for i in [1..7] do l[7+i] := 7+i^p; od;
  return PermList(l);
end;

K := Group(HeadPerm(x13),HeadPerm(x31));;
Cen := Centralizer(SymmetricGroup(14),K);;
Print("centralizer size ",Size(Cen),"\n");
u := HeadPerm(x12)*TailPerm(x12);;
b := HeadPerm(b23)*TailPerm(b23);;
r := HeadPerm(rho3)*TailPerm(rho3);;
c := HeadPerm(b23);;

invol := 0;; braid := 0;; joint := 0;;
for h in Elements(Cen) do
  if h^2=() then
    invol := invol+1;
    if (h*b)^3=() then
      braid := braid+1;
      a := h*u;
      prod := (r^2*a*r^-2)*(r*a*r^-1)*a;
      if prod=c then
        joint := joint+1;
        Print("JOINT h=",h," image size=",Size(Group(HeadPerm(x12),HeadPerm(x23),HeadPerm(x31),TailPerm(x12),TailPerm(x23),TailPerm(x31),h)),"\n");
      fi;
    fi;
  fi;
od;
Print("involutions ",invol," braid ",braid," joint ",joint,"\n");
QUIT;
