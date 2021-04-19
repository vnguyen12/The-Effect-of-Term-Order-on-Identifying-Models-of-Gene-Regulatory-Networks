-------------------------------------------------------
--Computation of ALL functions w/o CT using gfan
--Author: Brandy Stigler
--November 13, 2006
--------------------------------------------------------

-------------------------------------------------------
--Packages
--------------------------------------------------------
load "PolynomialDynamicalSystems.m2"
needsPackage "Points"

-------------------------------------------------------
--Parameters
--------------------------------------------------------
p = 2;
n = 3;
K = ZZ/p;


-------------------------------------------------------
--New functions
--------------------------------------------------------

getGB = method(TypicalValue => BasicList) 
getGB(FunctionData, List) := (FD, L) -> (
    --FD is a hashtable of input-output data
    --L is a list of variables (ring elements); gb will be in terms of these variables 

    kk:= coefficientRing ring first L;
    m := matrix keys FD;
    cols := apply(L, v-> index v);
    V := submatrix(m, cols);
    R := kk[L];
    (SM, LT, GB) := points(transpose V, R);
    GB
)


getGbsWithWeights = method(TypicalValue=>List)
getGbsWithWeights(List, ZZ, String) := (L, p, outfile) -> (
    --L is a list of GBs in terms of xi's
    
    kk:= coefficientRing ring first L;
    pp := char kk;                                                      --char of field
    vbs := unique flatten (L/support);                                  --support of gb
    
    file := openOut "1gb.txt";                                          --file needed to put gb in gfan format
    file << toSequence vbs << "("; 
    apply(#L-1, i->file << toString L_i << ", "); 
    file << toString last L << ")" << close;                            --file is in gfan_substitute input format
    
    run ("gfan_substitute < "|toString file|" | gfan --mod "|pp|" | gfan_weightvector -e -m --mod "|pp|" > "|toString outfile);
       -- gfan_substitute < N2-ms-CT-1gb-19.txt | gfan -g --mod 7 | gfan_weightvector -e -m --mod 7 > testwt.txt  --change vars, compute gb fan, compute wt vectors
   
    removeFile toString file;
    
    GFO := get outfile;                                                 --GFO is gfan output
    GFV := unique characters GFO;                                       --GFV is the list of variables gfan used
    GFV = (sort select(GFV, c->member(first ascii c, 97..122)))/value;  --a to z only
    
    tempR:=kk[GFV];
    GFO = value GFO;
    
    apply(GFO, l->(
        S := kk[GFV, MonomialOrder=>Weights=>reverse last l];
        T := kk[vbs, MonomialOrder=>Weights=>reverse last l];
        phi := map(T, S, gens T);
        apply(first l, f->phi sub(f,S))
    ))
)

computeNF = method()
computeNF(RingElement, List) := (f, L) -> (
    apply(L, p->(        
        sub(f, ring first p)%matrix{p}
    ))
)

-------------------------------------------------------
--Getting minsets
--------------------------------------------------------
R = K[makeVars n];
T = readTSData({"../N2-pc.st", "../ms-pc.st"},{},K);

ms = lines get "../../N2-ms-CT.dot";
ms = drop(ms, 26);
ms = drop(ms,-2);
ms = select(ms, l->#l!=0);
ms = flatten apply(ms, l->drop(separate("->",l),-1));
ms = apply(ms, l->replace(";" , "," , l))/value;    --ms is in R


-------------------------------------------------------
--Compute normal forms for all reduced GBs
--------------------------------------------------------
apply(n, i->(
    data = functionData(T, i+1);
    f = findFunction(data, ms_i);
    G = getGB(data, ms_i); 
    Gs = getGbsWithWeights(G, p, concatenate("gbs-",toString(i+1),".out"));
    fs = computeNF(f, Gs);
    ff = apply(fs, h->sub(h, ring f));

    outf = openOut concatenate("fs-",toString(i+1),".out");
    outf << #unique ff << " " << #ff << endl;
    tf = pairs tally ff;
    tf = rsort apply(tf, p->(p_1, toString p_0)); 
    apply(tf, h->outf << h << endl);
    outf << close;

    statf = openOut concatenate("stat-",toString(i+1),".out");
    statf << "# NFs: " << #ff << endl;
    statf << "# unique NFs: " << #unique ff << endl;
    tm = pairs tally flatten apply(unique ff, h->select(unique((flatten entries monomials h)/support), m->#m>=1));
    tm = rsort apply(tm, p->(p_1, p_0)); 
    apply(tm, m-> statf << m << endl); 
    statf << close;
))

end

-------------------------------------------------------
--END
--------------------------------------------------------


--to see the polys and check for factorization, do
i = 17;
data = functionData(T, i+1);
f = findFunction(data, ms_i);
G = getGB(data, ms_i); 
Gs = getGbsWithWeights(G, p, concatenate("gbs-",toString(i+1),".out"));
fs = computeNF(f, Gs);
ff = apply(fs, h->sub(h, ring f));
tf = tally ff;
j = position(ff, f->f==first select(keys tf, k->tf#k==max values tf));

--use the next lines for f18
--J = positions(ff, f->member(f,select(keys tf, k->tf#k==max values tf)));
--fs_(first J)

--fs_j is the poly with highest tally count
use ring fs_j
fs_j%ideal(x9)

--note that f8,f9,f19 have unique polys with highest tally counts
--f18 has two; so be careful with computation of j

