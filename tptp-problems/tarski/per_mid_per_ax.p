fof(ax_8_1_1,axiom,(![A,B,C]:((per(A,B,C))=>(?[C1]:(cong(A,C,A,C1)&is_midpoint(B,C,C1)))))).
fof(ax_8_1_2,axiom,(![A,B,C,C1]:((cong(A,C,A,C1)&is_midpoint(B,C,C1))=>per(A,B,C)))).
fof(ax_7_1,axiom,(![A,M,B]:((is_midpoint(M,A,B))=>(bet(A,M,B)&cong(M,A,M,B))))).
fof(ax_7_2,axiom,(![A,M,B]:((bet(A,M,B)&cong(M,A,M,B))=>is_midpoint(M,A,B)))).
fof(ax_2_10_1,axiom,(![A,B,C,D,A1,B1,C1,D1]:(afs(A,B,C,D,A1,B1,C1,D1)=>(bet(A,B,C)&bet(A1,B1,C1)&cong(A,B,A1,B1)&cong(B,C,B1,C1)&cong(A,D,A1,D1)&cong(B,D,B1,D1))))).
fof(ax_2_10_2,axiom,(![A,B,C,D,A1,B1,C1,D1]:((bet(A,B,C)&bet(A1,B1,C1)&cong(A,B,A1,B1)&cong(B,C,B1,C1)&cong(A,D,A1,D1)&cong(B,D,B1,D1))=>afs(A,B,C,D,A1,B1,C1,D1)))).