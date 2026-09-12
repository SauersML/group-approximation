# Classify the local-vertex kernels which can survive after a faithful finite
# full-large carrier is passed to a nonabelian simple composition factor.

# F'=S3(r,u) x S3(z,c).
fFree:=FreeGroup("r","z","c","u");;
fr:=fFree.1;; fz:=fFree.2;; fc:=fFree.3;; fu:=fFree.4;;
fFp:=fFree/[
  fr^3,fz^3,fc^2,fu^2,
  Comm(fr,fz),Comm(fc,fr),(fc*fz)^2,
  (fu*fr)^2,Comm(fu,fz),Comm(fu,fc)
];;
fIso:=IsomorphismPermGroup(fFp);; fGroup:=Image(fIso);;
fR:=Image(fIso,fFp.1);; fZ:=Image(fIso,fFp.2);;
fC:=Image(fIso,fFp.3);; fU:=Image(fIso,fFp.4);;
fFirstS3:=Group(fR,fU);;
fCompatible:=Filtered(NormalSubgroups(fGroup),n->
  Size(Intersection(n,fFirstS3))=1 and not fZ in n);;
if List(fCompatible,Size)<>[1] then
  Error("unexpected compatible F' kernels");
fi;

# J=S4 with K=<t,s>=S3 and marked c in its normal V4.
jFree:=FreeGroup("t","s","c");;
jt:=jFree.1;; js:=jFree.2;; jc:=jFree.3;;
jq:=jt*jc*js*jc*jt^-1*jc*js*jt*jc;;
jFp:=jFree/[jt^3,js^2,jc^2,(js*jt)^2,(jc*jt)^3,jq];;
jIso:=IsomorphismPermGroup(jFp);; jGroup:=Image(jIso);;
jT:=Image(jIso,jFp.1);; jS:=Image(jIso,jFp.2);;
jC:=Image(jIso,jFp.3);; jK:=Group(jT,jS);;
jCompatible:=Filtered(NormalSubgroups(jGroup),n->
  Size(Intersection(n,jK))=1 and not jC in n);;
if List(jCompatible,Size)<>[1] then
  Error("unexpected compatible J kernels");
fi;

# C=C2^4:C3^2, with injected overlaps A=<r,z> and H=<r,b>=A4.
cFree:=FreeGroup("r","z","b");;
cr:=cFree.1;; cz:=cFree.2;; cb:=cFree.3;;
cFp:=cFree/[
  cr^3,cz^3,cb^2,Comm(cr,cz),(cr^-1*cb)^3,(cz*cb)^3
];;
cIso:=IsomorphismPermGroup(cFp);; cGroup:=Image(cIso);;
cR:=Image(cIso,cFp.1);; cZ:=Image(cIso,cFp.2);;
cB:=Image(cIso,cFp.3);;
cA:=Group(cR,cZ);; cH:=Group(cR,cB);;
cCompatible:=Filtered(NormalSubgroups(cGroup),n->
  Size(Intersection(n,cA))=1 and Size(Intersection(n,cH))=1);;
if List(cCompatible,Size)<>[1,4,4] then
  Error("unexpected compatible C144 kernels");
fi;
if List(cCompatible,n->StructureDescription(FactorGroup(cGroup,n)))<>
   ["A4 x A4","C3 x A4","C3 x A4"] then
  Error("unexpected compatible C144 quotient structures");
fi;

k1:=(cFp.1*cFp.2^-1*cFp.3^-1)^3;;
k2:=(cFp.1*cFp.2^-1*cFp.3^-1)^4*cFp.2*cFp.1^-1;;
k1Image:=Image(cIso,k1);; k2Image:=Image(cIso,k2);;
if not Set([Size(NormalClosure(cGroup,Group(k1Image))),
            Size(NormalClosure(cGroup,Group(k2Image)))])=Set([4]) then
  Error("kernel representative normal closures changed");
fi;
if NormalClosure(cGroup,Group(k1Image))=
   NormalClosure(cGroup,Group(k2Image)) then
  Error("kernel representatives do not distinguish the two kernels");
fi;

Print("{\n");
Print("  \"Fprime_order\": ",Size(fGroup),",\n");
Print("  \"Fprime_compatible_kernel_orders\": ",List(fCompatible,Size),",\n");
Print("  \"J_order\": ",Size(jGroup),",\n");
Print("  \"J_compatible_kernel_orders\": ",List(jCompatible,Size),",\n");
Print("  \"C144_order\": ",Size(cGroup),",\n");
Print("  \"C144_compatible_kernel_orders\": ",List(cCompatible,Size),",\n");
Print("  \"C144_compatible_quotients\": ",
      List(cCompatible,n->StructureDescription(FactorGroup(cGroup,n))),",\n");
Print("  \"C144_order4_kernel_normal_generators\": [",
      "\"(r*z^-1*b^-1)^3\", ",
      "\"(r*z^-1*b^-1)^4*z*r^-1\"","]\n");
Print("}\n");
QUIT;
