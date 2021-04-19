newPackage(
    "PolynomialDynamicalSystems",
        Version => "0.2", 
        Date => "January 4, 2006",
        Authors => {
         {Name => "Brandy Stigler", Email => "bstigler@mbi.osu.edu", HomePage => "http://users.mbi.ohio-state.edu/bstigler"},
         {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~mike"}
         },
        Headline => "Utilities for polynomial dynamical systems",
        DebuggingMode => true
        )

needs "Points.m2"

export{getVars,
       makeVars,
       TimeSeriesData, 
       FunctionData, 
       readTSData,
       functionData,
       subFunctionData,
       minRep,
       findFunction,
       checkFunction,
       WildType
      }

---------------------------------------------------------------------------------------------------
-- Declaration of new data types
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- TimeSeriesData: This hashtable stores time series data with values in a set k.
-- The data is (txn)-dimensional, where t=#timepoints-1, n=#variables.
-- keys   = time series labels
-- values = time series
--    key = Wildtype:    value = list of (txn)-matrices of wildtype time series
--    key = (i, file_i): value = list of (txn)-matrices of time series for ith knockout 

TimeSeriesData = new Type of HashTable
 
---------------------------------------------------------------------------------------------------
-- FunctionData: This hashtable defines a function f:k^n->k, where k is a finite field.
-- keys   = points in k^n (in domain of f)
-- values = points in k (in codomain of f)

FunctionData = new Type of HashTable


---------------------------------------------------------------------------------------------------
-- Utilities for working with polynomial dynamical systems
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- Given an integer n, makeVars returns a list of n variables of type xi.

makeVars = method(TypicalValue => List)
makeVars(ZZ) := (n) -> apply(1..n, i -> value ("x"|i))

---------------------------------------------------------------------------------------------------
-- Given an element of a polynomial ring, getVars returns the list of variables in the polynomial.

getVars = method(TypicalValue => List)
getVars(ZZ) := (n) -> ({})
getVars(RingElement) := (f) -> (
    -- standard form of the monomials of f, i.e., no coefficients
    SF := apply(terms f, m -> first keys standardForm m);
    Vars := {};
    select(SF, h->if keys h!={} then Vars=append(Vars, keys h));
    Vars = sort unique flatten Vars;
    apply(Vars, e->e+1)
)

---------------------------------------------------------------------------------------------------
-- Given a list of elements, see prints out each element on a single line, followed by a hard return.

see = method()
see(List) := (fs) -> scan(fs, (g -> (print g; print "")))


---------------------------------------------------------------------------------------------------
-- Utilities for data processing
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- Internal to "readTSData"
-- Given a data file and a coefficient ring, readMat returns the (txn)-matrix of the data (t=time, n=vars). 

readMat = method(TypicalValue => Matrix)
readMat(String,Ring) := (filename,R) -> (
     ss := select(lines get filename, s -> length s > 0);
     matrix(R, apply(ss, s -> (t := separateRegexp(" +", s); 
                 t = apply(t,value);
                     select(t, x -> class x =!= Nothing))))
)

---------------------------------------------------------------------------------------------------
-- Given a list of wildtype and a list of knockout time series data files, as well as a coefficient ring,
-- readTSData returns a TimeSeriesData hashtable of the data.
-- Uses "readMat"

readTSData = method(TypicalValue => TimeSeriesData)
readTSData(List,List,Ring) := (wtfiles, knockouts, R) -> (
     -- wtfiles: list of file names for wild type data series
     -- knockouts: list of pairs (i,filename), where
     --  i is an integer with which node gets knocked out (first variable has index 1).
     --  filename is the corresponding time series data
     -- output: TimeSeriesData

     wtmats := apply(wtfiles, s -> readMat(s,R));
     H := new MutableHashTable;
     scan(knockouts, x -> (
           m := readMat(x#1,R);
           i := x#0;
           if H#?i then H#i = append(H#i,m)
           else H#i = {m}));
     H.WildType = wtmats;
     new TimeSeriesData from H
)

---------------------------------------------------------------------------------------------------
-- Given time series data and an integer i, functionData returns the FunctionData hashtable for function i,
-- that is the input-output (vector-scalar) data pairs corresponding to node i, if consistent; 
-- else it returns an error statement.

functionData = method(TypicalValue => FunctionData)
functionData(TimeSeriesData, ZZ) := (tsdata,v) -> (
     H := new MutableHashTable;

     -- first make the list of matrices
     mats := tsdata.WildType;
     scan(keys tsdata, x -> if class x === ZZ and x =!= v then mats = join(mats,tsdata#x));

     -- now make the hash table
     scan(mats, m -> (
           e := entries m;
           for j from 0 to #e-2 do (
            tj := e#j;
            val := e#(j+1)#(v-1);
            if H#?tj and H#tj != val then
              error ("function inconsistent: point " | 
                   toString tj| " has images "|toString H#tj|
                   " and "|toString val);           
            H#tj = val;
            )));
     new FunctionData from H
)

---------------------------------------------------------------------------------------------------
-- Given function data (data for a function) and a list L of integers between 1 and n(=dim pds), 
-- corresponding to a subset of the set of variables, 
-- subFuunctionData returns the function data projected to the variables in L, if consistent; 
-- else it returns an error statement.

subFunctionData = method(TypicalValue => FunctionData)
subFunctionData(FunctionData, List) := (fcndata,L) -> (
     H := new MutableHashTable;
     L = apply(L, j -> j-1);
     scan(keys fcndata, p -> (
           q := p_L;
           val := fcndata#p;
           if H#?q and H#q != val
           then error ("sub function inconsistent: point " | 
            toString q| " has images "|toString H#q|
            " and "|toString val);
           H#q = val;
           ));
     new FunctionData from H
)

---------------------------------------------------------------------------------------------------
-- Internal to getdiffs
-- Given 2 lists of points in k^n and a polynomial ring, getdiffs1 returns a monomial

getdiffs1 = method(TypicalValue => RingElement)
getdiffs1(List, List, Ring) := (p,q,R) -> ( 
     m := 1_R;
     scan(#p, i -> if p#i =!= q#i then m = m*R_i);
     m)

---------------------------------------------------------------------------------------------------
-- Internal to minRep; uses getdiffs1
-- Given 2 lists of lists of points in k^n, getdiffs returns a monomial ideal

getdiffs = method(TypicalValue => MonomialIdeal)
getdiffs(List, List, Ring) := (P,Q,R) -> ( 
     L := flatten apply(P, p -> apply(Q, q -> getdiffs1(p,q,R)));
     monomialIdeal L)

---------------------------------------------------------------------------------------------------
-- Previously called "sparseSets"

-- Given function data D for f_i, and a polynomial ring, minRep returns a monomial ideal.
-- Purpose of ideal: set of variables, one from each gen of the ideal, is the smallest #vars 
-- required for a consistent function; that is, the sets of vars needed for a minimal representation 
-- of the polynomial function defined by D.
-- If ideal is gen by m monomials, then sets have at most m elements

minRep = method(TypicalValue => MonomialIdeal)
minRep(FunctionData, Ring) := (fcndata,R) -> (
     Ps := apply(unique values fcndata, j -> select(keys fcndata, k -> fcndata#k === j));

     -- the next 2 commented lines were used for testing purposes
    -- print apply(Ps, a-> #a);
    -- time Ls := apply(subsets(Ps,2), x -> getdiffs(x#0,x#1,R));

     --the last 2 lines were replaced with
     print apply(Ps, a-> #a);
     Ls := apply(subsets(Ps,2), x -> getdiffs(x#0,x#1,R));

     sum Ls
)

---------------------------------------------------------------------------------------------------
-- This function doesn't always work. ???

-- Uses subFunctionData
-- Given function data D for f_i and a list L of variables xi, i=1..n, (returned from minRep)
-- findFunction computes a polynomial in the vars in L that fit D.

findFunction = method(TypicalValue => RingElement, Options => {MonomialOrder=>null})
findFunction(FunctionData, List) := o -> (fcndata,L) -> (

-- need to let user specify a term order. may have to remove "monoid"
-- if L=={}, then perhaps default should be the whole ring;
-- in this case, perhaps "findFunction" should be redefined to accept only one input (FunctionData) 
-- need to check if the order of variables given matters.

     if #L === 0 then error "expected positive number of variables";
     R := ring L#0;
     Lindices := apply(L, x -> index x + 1);
     F := subFunctionData(fcndata,Lindices);
     S := (coefficientRing R)(monoid [L]);
     pts := transpose matrix keys F;
     vals := transpose matrix {values F};
     (A,stds) := pointsMat(pts,S);
     f := ((transpose stds) * (vals // A))_(0,0);
     substitute(f,R)
)

---------------------------------------------------------------------------------------------------
-- Given function data D for f_i and a polynomial g, check evaluates g on D and 
-- returns true if g fits D and false otherwise; in this case, it returns an error statement.
-- Used to check the results of findFunction

checkFunction = method(TypicalValue => Boolean)
checkFunction(FunctionData, RingElement) := (fcndata,f) -> (
     pts := transpose matrix keys fcndata;
     Fs := makeRingMaps(pts,ring f);
     k := keys fcndata;
     s := select(0..#k-1, i -> Fs#i(f) != fcndata#(k#i));
     sp := apply(s, i -> k#i);
     if #s === 0 then true
     else (print ("function FAILS on points "|toString sp); false)
)

     
---------------------------------------------------------------------------------------------------
--+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++--
---------------------------------------------------------------------------------------------------

beginDocumentation()

document { Key => PolynomialDynamicalSystems,
     Headline => "Utilities for polynomial dynamical systems",
     EM "PolynomialDynamicalSystems", " is a package for the algebraic 
     manipulation of polynomial dynamical systems.",
     PARA,
     "The following example describes the basic usage of this package.",
     PARA,
     "In this example, the file 'wt1.dat' contains 7 time series data points for 5 nodes.
     The format of this file is: each row contains the (integer) data levels for a single node,
     separated by white space (spaces, tabs, but all on the same line).  Each row should contain 
     the same number of data points.  The knockout files have the same format.  The only difference
     is that knockout's for the i th node won't be used to determine functions for that node.",
     PARA,
     "First, we read the time series and knockout data using ", TO readTSData, ".  This produces
     a TimeSeriesData object, which is just a Macaulay2 hash table.",
     EXAMPLE {
      ///T = readTSData({"wt1.dat"}, {(1,"ko1.dat")}, ZZ/5)///,
      },
     "Suppose we wish to understand which nodes might affect node 2.  First, we determine
     what any such function must satisy.",
     EXAMPLE {
      "fT = functionData(T,2)"
      },
     "In this example, there are only seven constaints on the function.  Consequently, there are
     many functions which will satisfy these constraints.",
     PARA,
     "Next, we create a monomial ideal which encodes all of the possible sparsity patterns
     of all such functions satisfying these constraints.",
     EXAMPLE {
      "R = ZZ/5[makeVars 7];",
      "I = minRep(fT,R)",
      },
     "The monomial ideal I has the property that there is a function involving 
     variables x_i1, ..., x_ir if and only if I is contained in the ideal (x_i1, ..., x_ir).
     For example, each generator of I is divisible by either x2 or x4, so there is a function 
     involving just x2 and x4 which satisfies the data.",
     PARA,
     "In order to find all minimal such sets, we use the Macaulay2 built-in function ",
     TO minimalPrimes, ".  Each monomial generator of the result encodes a minimal set.",
     EXAMPLE {
      "minimalPrimes I"
      },
     "The first generator tells us that there is a function involving only x2 and x4.",
     EXAMPLE {
      "findFunction(fT,{x2,x4})"
      },
     "The second generator tells us that there is a function involving only x3 and x4.",
     EXAMPLE {
      "findFunction(fT,{x3,x4})"
      }
}

document {
    Key => (checkFunction, FunctionData, RingElement),
    Headline => "given function data D and a polynomial g, evaluates g on D and returns true if g fits D and false otherwise"
}


document {
    Key => (findFunction, FunctionData, List),
    Headline => "given function data D and a list L of variables xi, i=1..n, computes a polynomial in the variables in L that fit D"
}

document {
    Key => (functionData,TimeSeriesData, ZZ),
    Headline => "given time series data and an integer i, returns a hashtable of type FunctionData for function i, that is the input-output (vector-scalar) data pairs corresponding to node i, if consistent; else returns an error statement"
}

document {
    Key => (getVars, RingElement),
    Headline => "returns the variables in a given polynomial"
}

document {
    Key => (makeVars, ZZ),
    Headline => "given an integer n, returns a list of variables {x1..xn}"
}

document {
    Key => (minRep, FunctionData, Ring),
    Headline => "given function data D and a polynomial ring, returns a monomial ideal, where the set of variables, one from each generator of the ideal, is the smallest # variables required for a consistent function; that is, the sets of variables needed for a minimal representation of the polynomial function defined by D; to be used with primaryDecomposition"
}

document { 
     Key => {readTSData, (readTSData,List,List,Ring)},
     Headline => "read time series data from a set of wild and knockout files",
     Usage => "readTSData(WT,KO,kk)",
     Inputs => {
      "WT" => " a list of file names, containing wild type data",
      "KO" => {" a list (i, L), where i is the variable being knocked out, and
            L is a list of file names containing knock out data for variable i."},
      "kk" => "the coefficient ring (usually a finite field)"
      },
     Outputs => {
      TimeSeriesData => "a hash table"
      },
     Caveat => {},
     SeeAlso => {}
     }

document {
    Key => (subFunctionData,FunctionData, List),
    Headline => "given function data and a list L of integers between 1 and n(=dim pds), corresponding to a subset of the set of variables, returns the function data projected to the variables in L, if consistent; else it returns an error statement"
}

--       TimeSeriesData, 
--       FunctionData, 

end
document { 
     Key => (borel,Matrix),
     Headline => "",
     Usage => "",
     Inputs => {
      },
     Outputs => {
      },
     Consequences => {
      },     
     "description",
     EXAMPLE {
      },
     Caveat => {},
     SeeAlso => {}
     }
