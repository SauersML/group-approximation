p:=3;
F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
cm:=function(x,y) return x^-1*y^-1*x*y; end;;
rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(cm(a,c),c),a),cm(cm(cm(a,c),c),c)];;
G:=F/rels;;
r:=cm(G.2,G.1);; s:=cm(G.2,G.3);;
w:=(r*s)^p;;
words:=[["[r,s,r]",cm(cm(r,s),r)],["[r,s,s,r]",cm(cm(cm(r,s),s),r)],["[r,s,s,s]",cm(cm(cm(r,s),s),s)],["[s,r,s]",cm(cm(s,r),s)],["[s,r,r,s]",cm(cm(cm(s,r),r),s)],["[s,r,r,r]",cm(cm(cm(s,r),r),r)],["w",w],["(rs)",r*s]];;
for cl in [3..7] do
  epi:=EpimorphismPGroup(G,p,cl);; Q:=Image(epi);;
  Print("class<=",cl," p^",LogInt(Size(Q),p)," ", List(words, x->[x[1],Order(Image(epi,x[2]))]),"\n");
od;
QUIT;
