p:=5;
mk:=function(p)
local F,a,b,c,cm,rels,G,w;
F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
cm:=function(x,y) return x^-1*y^-1*x*y; end;;
rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(cm(a,c),c),a),cm(cm(cm(a,c),c),c)];;
G:=F/rels;;
w:=(cm(G.2,G.1)*cm(G.2,G.3))^p;;
return [G,w];
end;;
wab:=function(Hs,w)
local iso,H2,q2,img;
iso:=IsomorphismFpGroup(Hs);; H2:=Image(iso);;
q2:=MaximalAbelianQuotient(H2);;
img:=Image(q2,Image(iso,w));;
return [Collected(AbelianInvariants(Image(q2))), Order(img)];
end;;


XX:=mk(p); G:=XX[1]; w:=XX[2];
Q:=ElementaryAbelianGroup(p^3);;
hom:=GroupHomomorphismByImages(G,Q,GeneratorsOfGroup(G),Pcgs(Q));;
K:=Kernel(hom);;
Print("p=",p," ker(Gamma->C_p^3) index ",Index(G,K)," ",wab(K,w),"\n");
QUIT;
