# Exact low-index quotient screen for the one-relator A4 forward-collision
# carrier.  Run with GAP and set MAX_INDEX before Read() to override 16.

if not IsBound(MAX_INDEX) then
  MAX_INDEX := 16;
fi;

free := FreeGroup("r", "z", "c", "t", "s");;
r := free.1;; z := free.2;; c := free.3;; t := free.4;; s := free.5;;
b := s*t;;
q := t*c*s*c*t^-1*c*s*t*c;;
rels := [
  r^3, z^3, Comm(z,r),
  c^2, Comm(c,r), c*z*c*z,
  t^3, s^2, (s*t)^2,
  (r^-1*b)^3, (z*b)^3,
  q
];;
gamma := free/rels;;
gg := GeneratorsOfGroup(gamma);;

subgroups := LowIndexSubgroupsFpGroup(gamma, MAX_INDEX);;
Print("max_index=", MAX_INDEX, " low_index_subgroups=", Length(subgroups), "\n");

b_survival := 0;;
faithful := 0;;
for subgroup in subgroups do
  cosets := RightCosets(gamma, subgroup);;
  action := ActionHomomorphism(gamma, cosets, OnRight);;
  image := Image(action);;
  images := List(gg, generator -> Image(action, generator));;
  ir := images[1];; iz := images[2];; ic := images[3];;
  it := images[4];; is := images[5];; ib := is*it;;
  order_b := Order(ib);;
  order_C := Order(Group([ir,iz,ib]));;
  order_F := Order(Group([ir,iz,ic]));;
  order_K := Order(Group([it,is]));;
  if order_b = 2 then b_survival := b_survival+1; fi;
  if order_C = 144 and order_F = 18 and order_K = 6 then
    faithful := faithful+1;
    Print("FAITHFUL degree=", Length(cosets),
          " quotient_order=", Order(image),
          " C=", order_C, " F=", order_F, " K=", order_K, "\n");
    Print("generator_images_one_based=", List(images,
          permutation -> ListPerm(permutation, Length(cosets))), "\n");
  fi;
od;
Print("b_survival=", b_survival, " faithful=", faithful, "\n");

