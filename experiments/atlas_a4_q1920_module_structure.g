# Exact extension/module structure of the two faithful order-1920
# large-K2,2 markings in the complete degree-at-most-twelve local census.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
G:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
gg:=GeneratorsOfGroup(G);;

DescribeMarkedGroup:=function(images)
  local Q,normals,N,quot,hom,A,B,pcgs,basis,actionMatrices,g,matrix,row,
        conjugate,complements,K,k,affineVectors,affine,edgeData,classes,
        quotientA,quotientB,aInvolutions,bInvolutions,pairs,pair,mismatch;
  Q:=Group(images);
  normals:=NormalSubgroups(Q);
  Print("structure=",StructureDescription(Q)," derived_order=",
        Size(DerivedSubgroup(Q))," center_order=",Size(Center(Q)),"\n");
  Print("normal_profiles=",Collected(List(normals,n->
        [Size(n),IsElementaryAbelian(n),StructureDescription(Q/n)])),"\n");
  N:=First(SortedList(
       Filtered(normals,n->Size(n)>1 and Size(n)<Size(Q) and
                           IsElementaryAbelian(n) and IsNormal(Q,n)),
       function(a,b) return Size(a)>Size(b); end),n->true);
  if N=fail then Error("no nontrivial elementary abelian normal subgroup"); fi;
  quot:=Q/N;
  hom:=NaturalHomomorphismByNormalSubgroup(Q,N);
  Print("module_order=",Size(N)," quotient=",StructureDescription(quot),"\n");
  A:=Group([images[1],images[3]]);
  B:=Group([images[2],images[4]]);
  edgeData:=List([A,B],H->[Size(H),Size(Intersection(H,N)),
                              Size(Image(hom,H))]);
  Print("radial_edges_[order,kernel,quotient_image]=",edgeData,"\n");
  quotientA:=Image(hom,A);
  quotientB:=Image(hom,B);
  Print("quotient_radial_[intersection,join]=",
        [Size(Intersection(quotientA,quotientB)),
         Size(Group(Concatenation(GeneratorsOfGroup(quotientA),
                                  GeneratorsOfGroup(quotientB))))],"\n");
  aInvolutions:=[images[3],images[1]*images[3]*images[1]^-1,
                 images[1]^-1*images[3]*images[1]];
  bInvolutions:=[images[4],images[2]*images[4]*images[2]^-1,
                 images[2]^-1*images[4]*images[2]];
  pairs:=[];
  for pair in Cartesian([1..3],[1..3]) do
    if Image(hom,aInvolutions[pair[1]])=
       Image(hom,bInvolutions[pair[2]]) then
      Add(pairs,pair);
    fi;
  od;
  if Length(pairs)<>1 then Error("shared quotient involution not unique"); fi;
  mismatch:=aInvolutions[pairs[1][1]]*bInvolutions[pairs[1][2]]^-1;
  Print("radial_mismatch_[A_label,B_label,order,central,orbit,normal_closure]=",
        [pairs[1][1],pairs[1][2],Order(mismatch),mismatch in Center(Q),
         Size(ConjugacyClass(Q,mismatch)),Size(NormalClosure(Q,Group(mismatch)))],
        "\n");
  Print("radial_join_order=",
        Size(Group(Concatenation(GeneratorsOfGroup(A),GeneratorsOfGroup(B)))),
        "\n");

  pcgs:=Pcgs(N);
  basis:=List(pcgs,x->x);
  Print("module_rank=",Length(basis),"\n");
  actionMatrices:=[];
  for g in images do
    matrix:=[];
    for conjugate in List(basis,x->x^g) do
      row:=ExponentsOfPcElement(pcgs,conjugate);
      Add(matrix,row);
    od;
    Add(actionMatrices,matrix);
  od;
  Print("conjugation_matrices_[r,y,u,b]=",actionMatrices,"\n");

  classes:=ConjugacyClasses(Q);
  Print("module_conjugacy_orbits=",Collected(List(
      Filtered(classes,class->Representative(class) in N),
      class->[Size(class),Size(Group(Elements(class)))])),"\n");

  complements:=ComplementClassesRepresentatives(Q,N);
  Print("complement_orders=",List(complements,Size),"\n");
  if Length(complements)>0 then
    K:=complements[1];
    affineVectors:=[];
    for g in images do
      k:=First(Elements(K),h->g*h^-1 in N);
      if k=fail then Error("complement decomposition failed"); fi;
      affine:=g*k^-1;
      Add(affineVectors,ExponentsOfPcElement(pcgs,affine));
    od;
    Print("affine_vectors_[r,y,u,b]=",affineVectors,"\n");
  fi;
end;;

count:=0;;
for sub in LowIndexSubgroupsFpGroup(G,MAX_INDEX) do
  cosets:=RightCosets(G,sub);;
  action:=ActionHomomorphism(G,cosets,OnRight);;
  images:=List(gg,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    count:=count+1;
    Print("=== marking ",count," ===\n");
    DescribeMarkedGroup(images);
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
