fof(ax_5_4_1,axiom,(![A,B,C,D]:(le(A,B,C,D)=>(?[Y]:(bet(C,Y,D)&cong(A,B,C,Y)))))).
fof(ax_5_4_2,axiom,(![A,B,C,D,Y]:((bet(C,Y,D)&cong(A,B,C,Y))=>(le(A,B,C,D))))).
fof(ax_4_4_1,axiom,(![A,B,C,A1,B1,C1]:((cong3(A,B,C,A1,B1,C1))=>(cong(A,B,A1,B1)&cong(A,C,A1,C1)&cong(B,C,B1,C1))))).
fof(ax_4_4_2,axiom,(![A,B,C,A1,B1,C1]:((cong(A,B,A1,B1)&cong(A,C,A1,C1)&cong(B,C,B1,C1))=>cong3(A,B,C,A1,B1,C1)))).