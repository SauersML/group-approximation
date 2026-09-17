# Lower p-central tower of Gamma^A2_p (edge A2) and Gamma_p (edges A2,A2,B2) far beyond class 3p.
# Prints the increments dim P_k/P_{k+1} and whether w_p = ([b,a][b,c])^p dies in the class-cl quotient.
run:=function(edge, p, cl)
  local F,a,b,c,cm,rels,G,epi,Q,r,s,w,pc,t0;
  F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
  cm:=function(x,y) return x^-1*y^-1*x*y; end;;
  rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a)];;
  if edge="A2" then Add(rels,cm(cm(a,c),c)); else Append(rels,[cm(cm(cm(a,c),c),a),cm(cm(cm(a,c),c),c)]); fi;
  G:=F/rels;;
  r:=cm(G.2,G.1);; s:=cm(G.2,G.3);;
  t0:=Runtime();;
  epi:=EpimorphismPGroup(G,p,cl);; Q:=Image(epi);;
  pc:=PCentralSeries(Q,p);;
  w:=Image(epi,(r*s)^p);;
  Print(edge," p=",p," class<=",cl," |Q|=p^",LogInt(Size(Q),p)," time=",Runtime()-t0,"ms ord w=",Order(w),"\n");
  Print("  increments: ",List([1..Length(pc)-1],i->LogInt(Index(pc[i],pc[i+1]),p)),"\n");
end;;
