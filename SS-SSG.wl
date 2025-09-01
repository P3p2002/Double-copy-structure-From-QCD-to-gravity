(* ::Package:: *)

<<FeynGrav`\.08


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*I will compute scalar scalar -> scalar scalar graviton*)


(* ::Text:: *)
(*I will follow the order of diagrams: the coupling of 2 scalars and 2 gravitons, the bremstraulgh of the initial scalar, the bremstraulgh of the final scalar, the coupling of 3 gravitons, and the same as the 3 initial, but with the bottom scalar.*)


(* ::Text:: *)
(*First of all, some functions will be defined. These functions have different purposes, such as defining the Sudakov variables.*)


(*Sudakov parameters definition*)
SudakovVariables[expr_] := (expr/.Pair[Momentum[k0], Momentum[k1]] -> -s*(\[Alpha]2 + \[Beta]2)/2 /.Pair[Momentum[k2], Momentum[k1]] -> s*(\[Alpha]1 + \[Beta]1)/2
/.Pair[Momentum[k0], Momentum[p1]] -> -s*\[Beta]1/2 /.Pair[Momentum[k2], Momentum[p2]] -> s*\[Alpha]2/2
/. Pair[Momentum[k1], Momentum[p1]] -> s*(\[Beta]1 - \[Beta]2)/2 /. Pair[Momentum[k1], Momentum[p2]] -> s*(\[Alpha]1 - \[Alpha]2)/2 
/. Pair[Momentum[k2], Momentum[p1]] -> s*(1 + \[Beta]2)/2 /. Pair[Momentum[k0], Momentum[p2]] -> s*(1 - \[Alpha]1)/2 
/. Pair[Momentum[k0], Momentum[k2]] -> s*(1 - \[Alpha]1 + \[Alpha]2 - \[Beta]1 + \[Beta]2)/2 /. Pair[Momentum[p1], Momentum[p2]] -> s/2
/. Pair[Momentum[p1], Momentum[p1]] -> 0 /. Pair[Momentum[p2], Momentum[p2]] -> 0 
/. Pair[Momentum[k0], Momentum[k0]] -> 0 /. Pair[Momentum[k1], Momentum[k1]] -> 0
/. Pair[Momentum[k2], Momentum[k2]] -> 0//Simplify)


(*The main idea behind the following functions is to generate all the possible pairs, detect which of them are
in the expression, and then collect them.*)
(*This first function generates the polarizarion structures from the given momentum list*)
ClearAll[GeneratePolStructures]
GeneratePolStructures[momList_List] := Module[
  {singles, pairs},
  
  singles = Pair[Momentum[#], Momentum[Polarization[k1, Complex[0, 1]]]] & /@ momList;
  
  pairs = Times @@@ Subsets[singles, {2}];
  Join[singles, pairs]
]

(*This one makes the filter in the given expression*)
ClearAll[FilterPresentStructures]
FilterPresentStructures[expr_, structList_List] := Select[
  structList,
  (* Check if pattern appears inside expr *)
  ! FreeQ[expr, #] &
]

(*This one collects the polarization structures previously filtered*)
ClearAll[CollectByPolStructures]
CollectByPolStructures[expr_, momList_List] := Module[
  {allStructs, presentStructs},
  
  allStructs = GeneratePolStructures[momList];

  presentStructs = FilterPresentStructures[expr, allStructs];
  
  Collect[expr, presentStructs, Simplify]
]

(*This function will collect the momentas, which may be useful for the GI check*)
Momentumlist = {Pair[LorentzIndex[\[Nu]1],Momentum[p1]], Pair[LorentzIndex[\[Nu]1],Momentum[p2]], Pair[LorentzIndex[\[Nu]1],Momentum[k0]],
Pair[LorentzIndex[\[Nu]1],Momentum[k1]], Pair[LorentzIndex[\[Nu]1],Momentum[k2]]};
Clear[Collectmomentum];
Collectmomentum[expr_, list_] := 
	Collect[expr, list, Simplify]

(*This function separates the terms like (k1 -2p1)\nu_1 into k1\nu_1 - 2p1\nu_1.
This is needed for the function Collect momentum, in order to work properly.*)
ClearAll[expandAndWrapMomenta];
expandAndWrapMomenta[expr_] := Module[
  {
    expandMomentum,
    momExpr, expandedMomExpr, finalExpr, nu
  },
  
  (* Recursive expansion inside Momentum *)
  expandMomentum[Momentum[a_ + b_]] := expandMomentum[Momentum[a]] + expandMomentum[Momentum[b]];
  expandMomentum[Momentum[c_ * d_ /; NumericQ[c]]] := c * expandMomentum[Momentum[d]];
  expandMomentum[Momentum[x_]] := Momentum[x];
  expandMomentum[x_Plus] := Plus @@ (expandMomentum /@ List @@ x);
  expandMomentum[x_Times] := Times @@ (expandMomentum /@ List @@ x);
  expandMomentum[x_] := x;
  
  (* Step 1: Extract momenta from Pair[LorentzIndex[\[Nu]1], ...] *)
  momExpr = expr /. Pair[LorentzIndex[\[Nu]1], mom_] :> mom;
  
  (* Step 2: Expand sums inside Momentum *)
  expandedMomExpr = expandMomentum[momExpr];
  
  (* Step 3: Wrap back into Pair *)
  finalExpr = expandedMomExpr /. Momentum[m_] :> Pair[LorentzIndex[\[Nu]1], Momentum[m]];
  
  finalExpr
]

(*This function does a similar function to the one before, but it outputs a list, which will be useful to approxiamte*)
ClearAll[CollectPolarizationStructures];
SetAttributes[CollectPolarizationStructures, HoldAll];

CollectPolarizationStructures[expr_] := Module[
  {
    terms, grouped, getKey, getCoeff, key,
    flattenFactors, sortedKey
  },

  (* Fully flatten all Times chains into a list *)
  flattenFactors[x_] := FixedPoint[List @@ # /. Times -> List &, x];

  (* Extract polarization-related objects like Momentum[Polarization[...]] *)
  getKey[term_] := Module[{factors, polTerms},
    factors = flattenFactors[term];
    polTerms = Select[factors, 
      ! FreeQ[#, Polarization] &&
      FreeQ[#, LorentzIndex] &
    ];
    polTerms
  ];

  (* Sort the polarization terms for consistent keying *)
  sortedKey[key_List] := Sort[key, OrderedQ[{ToString[#1], ToString[#2]}] &];

  (* Get coefficient by canceling the polarization factors *)
  getCoeff[term_, key_] := Module[{num, den, denKey},
    num = Numerator[term];
    den = Denominator[term];
    denKey = Times @@ key;
    Cancel[num / (den * denKey)]
  ];

  (* Expand the expression and break into terms *)
  terms = If[Head[expr] === Plus, List @@ Expand[expr], {Expand[expr]}];

  (* Group by polarization structures *)
  grouped = <||>;
  Do[
    key = sortedKey[getKey[Numerator[term]]];
    If[KeyExistsQ[grouped, key],
      grouped[key] += getCoeff[term, key],
      grouped[key] = getCoeff[term, key]
    ],
    {term, terms}
  ];

  (* Reconstruct expression from grouped terms *)
  Table[
    Module[{factors = ReleaseHold[hk]},
      grouped[hk] *
        Which[
          ListQ[factors], Times @@ factors,
          Head[factors] === Times, factors,
          True, factors
        ]
    ],
    {hk, Keys[grouped]}
  ]
];

(*The following functions are used to approximate each different amplitude. They are copy pasted from the QCD code.*)
ClearAll[approxByEpsilonHierarchy]
approxByEpsilonHierarchy[expr_, paramHierarchy_List, epsilon_: \[CurlyEpsilon], maxOrder_: 20] := Module[
  {
    subsRules, reverseRules, exprSubbed, expanded, minEpsOrder, leadingTerms
  },

  (* 1. Create substitution rules and reverse substitution rules *)
	{subsRules, reverseRules} = Transpose[
	  MapIndexed[
	    Function[{group, idx},
	      With[{power = First[idx] - 1},
	        Module[{consts, sub, rev},
	          consts = Table[
	            Symbol["c" <> ToString[power] <> ToString[i]],
	            {i, Length[group]}
	          ];
	          sub = Thread[group -> (consts * epsilon^power)];
	          rev = Thread[consts -> (group * epsilon^-power)];
	          {sub, rev}
	        ]
	      ]
	    ],
	    paramHierarchy
	  ]
	] // Map[Flatten];
	
  (* 2. Substitute and expand *)
  exprSubbed = expr /. subsRules;
  expanded = Series[exprSubbed, {epsilon, 0, maxOrder}] // Normal;

  (* 3. Get leading \[CurlyEpsilon] order *)
	expanded = Series[exprSubbed, {epsilon, 0, maxOrder}] // Normal // Expand;
	
	termsList = If[Head[expanded] === Plus, List @@ expanded, {expanded}];
	
	minEpsOrder = Min[Exponent[expanded, epsilon, List]];
	
	leadingTerms = Select[termsList, Exponent[#, epsilon] === minEpsOrder &];

  (* 4. Restore original variables *)
  Simplify[Total[leadingTerms] //. reverseRules]
]

OrderList = {
  {},              (* constants \[LongDash] group 0 *)
  {\[Alpha]1, \[Beta]2},        (* group 1 *)
  {\[Alpha]2, \[Beta]1}         (* group 2 *)
};

(*To make an approximation of something like: A/B, it approximates A, then B, and then I have approx(A)/approx(B)*)
ClearAll[approxRationalByepsilon]
approxRationalByepsilon[expr_, orderHierarchy_List] := Module[
  {num, den, approxNum, approxDen},
  
  (* Decompose rational expression *)
  {num, den} = {Numerator[expr], Denominator[expr]};
  
  (* Approximate each part individually *)
  approxNum = approxByEpsilonHierarchy[num, orderHierarchy];
  approxDen = approxByEpsilonHierarchy[den, orderHierarchy];
  
  (* Reconstruct *)
  approxNum / approxDen
]

ClearAll[factorAndSumSplit]
factorAndSumSplit[expr_] := Module[{f, s},
  Which[
    Head[expr] === Plus,
    {1, expr}, (* already a sum *)

    Head[expr] === Times && Head[Last[List @@ expr]] === Plus,
    (* A * (term1 + term2 + ...) *)
    f = Times @@ Most[List @@ expr];
    s = Last[List @@ expr];
    {f, s},

    True,
    {1, expr} (* not a sum at all *)
  ]
]

Finalapprox[expr_] := Module[{moms, step1, step2, num, den, finalstep},
  
  If[TrueQ[factorAndSumSplit[expr][[1]] == 1],  (* Check if sum or single term *)
	(* Single term case *)
    approxRationalByepsilon[expr, OrderList],
    
    (* If sum: *)
    moms = factorAndSumSplit[expr][[1]];          (* Common factor *)
    step1 = List @@ factorAndSumSplit[expr][[2]]; (* The sum itself *)
    
    (* Simplify each term in the sum *)
    step2 = Total[approxRationalByepsilon[#, OrderList] & /@ step1] // FullSimplify;

    (* Apply SU(N) commutation rule *)
    num = approxByEpsilonHierarchy[Numerator[step2], OrderList]//Expand // commRule // FullSimplify;
    den = Denominator[step2];
    
    (* Combine all parts *)
    finalstep = approxByEpsilonHierarchy[num, OrderList] * moms / den
  ]
]

(*Now the functions to extract the polarization are given*)\[CCedilla]
Clear[PolToFreeIndices]
(* Usage: PolToFreeIndices[expr, {mu, nu}] *)
PolToFreeIndices[expr_, inds_List] := Module[{i = 0, take, coreRules, pairQ},

  (* Safely fetch the next index; if you ever run out, generate a fresh one *)
  take[j_] := If[j <= Length[inds], inds[[j]], Unique["li"]];

  (* Predicate for the specific Pair forms we want to replace *)
  pairQ[e_] := MatchQ[e,
     Pair[Momentum[_, ___], Momentum[Polarization[___], ___]] |
     Pair[Momentum[Polarization[___], ___], Momentum[_, ___]] |
     Pair[Momentum[_, ___], Polarization[___]] |
     Pair[Polarization[___], Momentum[_, ___]]
  ];

  (* Core replacements: each matched Pair consumes one new free index *)
  coreRules = {
    Pair[u : Momentum[_, ___], Momentum[Polarization[___], ___]] :> (i++; Pair[u, LorentzIndex[take[i]]]),
    Pair[Momentum[Polarization[___], ___], v : Momentum[_, ___]] :> (i++; Pair[v, LorentzIndex[take[i]]]),
    Pair[u : Momentum[_, ___], Polarization[___]] :> (i++; Pair[u, LorentzIndex[take[i]]]),
    Pair[Polarization[___], v : Momentum[_, ___]] :> (i++; Pair[v, LorentzIndex[take[i]]])
  };

  (* 1) First, explode only the relevant powers into repeated factors, assigning indices per factor *)
  (* 2) Then, apply the core rules to any remaining linear occurrences *)
  (expr //. Power[pair_ /; pairQ[pair], n_Integer?Positive] :> Times @@ Table[pair /. coreRules, {n}])
    /. coreRules
]

Clear[PolToFreeIndicesSym]
(* PolToFreeIndicesSym[expr, {mu, nu}] 
   Produces (ReplacedExpr + ReplacedExpr with mu<->nu)/2
   Works with Powers (e.g. Pair[...]^2) because it calls PolToFreeIndices. *)
PolToFreeIndicesSym[expr_, {mu_Symbol, nu_Symbol}] := Module[
  {repl, tmp, swapped},
  (* get the expression with LorentzIndex[mu], LorentzIndex[nu] assigned *)
  repl = PolToFreeIndices[expr, {mu, nu}];
  
  (* perform a safe swap LorentzIndex[mu] <-> LorentzIndex[nu] using a unique temp *)
  tmp = Unique["tmpIndex"];
  swapped = repl /. LorentzIndex[mu] -> LorentzIndex[tmp];
  swapped = swapped /. LorentzIndex[nu] -> LorentzIndex[mu];
  swapped = swapped /. LorentzIndex[tmp] -> LorentzIndex[nu];
  
  (* symmetrize *)
  Simplify[(repl + swapped)/2]
]



(* ::Input:: *)
(*Null*)


(* ::Input:: *)
(*Null*)


(* ::Subsection:: *)
(*Now I will start to compute each diagram*)


(*Coupling of 2 scalars and 2 gravitons, top scalar*)
Clear[M1];
M1[p1_, p2_, k0_, k1_, k2_] = (Calc[GravitonScalarVertex[{\[Mu]1, \[Nu]1, \[Mu]2, \[Nu]2}, p1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p2-k2]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2, -k2, 0]]/. D -> 4/. Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m1, M1contracted];
m1[p1, p2, k0, k1, k2] = (SudakovVariables[M1[p1, p2, k0, k1, k2]])//ExpandScalarProduct;

M1contracted = (Contract[m1[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M1combined = CollectByPolStructures[Expand[M1contracted], {p1, p2, k0, k1, k2}]

(*Testing Gauge Invariance*)
m1GI = Contract[M1[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify; 
M1GI = SudakovVariables[m1GI]//Simplify;
M1GIcombined = Collectmomentum[expandAndWrapMomenta[M1GI], Momentumlist]


(*Initial bremstraulgh, top scalar*)
M2[p1_, p2_, k0_, k1_, k2_] = (Calc[GravitonScalarVertex[{\[Mu]1, \[Nu]1}, p1, - p1 + k1, 0]*
FeynAmpDenominatorExplicit[ScalarPropagator[p1 - k1, 0]]*
GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1 - k1, -k0, 0]
*FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p2-k2]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2, -k2, 0]]/. D -> 4 /. Momentum[k0] -> Momentum[p1] + Momentum[p2]
- Momentum[k1] - Momentum[k2])//ExpandScalarProduct//Simplify

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m2, M2contracted];
m2[p1, p2, k0, k1, k2] = (SudakovVariables[M2[p1, p2, k0, k1, k2]]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct;

M2contracted = (Contract[m2[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;
M2combined = CollectByPolStructures[Expand[M2contracted], {p1, p2, k0, k1, k2}]

(*Testing Gauge Invariance*)
m2GI = Contract[M2[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify; 
M2GI = SudakovVariables[m2GI]//Simplify;
M2GIcombined = Collectmomentum[expandAndWrapMomenta[M2GI], Momentumlist]


(*Final bremstraulgh, top scalar*)
M3[p1_, p2_, k0_, k1_, k2_] = (Calc[GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1,  - k0 - k1, 0]*
FeynAmpDenominatorExplicit[ScalarPropagator[k0 + k1, 0]]*
GravitonScalarVertex[{\[Mu]1, \[Nu]1}, k0 + k1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p2 - k2]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2, -k2, 0]]/. D -> 4/. Momentum[k0] -> Momentum[p1] + Momentum[p2]
- Momentum[k1] - Momentum[k2])//ExpandScalarProduct//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m3, M3contracted];
m3[p1, p2, k0, k1, k2] = (SudakovVariables[M3[p1, p2, k0, k1, k2]]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct//Simplify;

M3contracted = (Contract[m3[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M3combined = CollectByPolStructures[Expand[M3contracted], {p1, p2, k0, k1, k2}]//Simplify

(*Testing Gauge Invariance*)
m3GI = Contract[m3[p1, p2, k0, k1, k2] Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify;
M3GI = SudakovVariables[m3GI]//Simplify;
M3GIcombined = Collectmomentum[expandAndWrapMomenta[M3GI], Momentumlist]


(*Three graviton emission*)
M4[p1_, p2_, k0_, k1_, k2_] = (Calc[GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]2, \[Nu]2, \[Alpha]1, \[Beta]1, p1 - k0]]*
GravitonVertex[\[Alpha]1, \[Beta]1, p1 - k0, \[Alpha]2, \[Beta]2, p2 - k2, \[Mu]1, \[Nu]1, -k1 ]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Alpha]2, \[Beta]2, p2 - k2]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2, -k2, 0]]/. D -> 4/. Momentum[k0] -> Momentum[p1] + Momentum[p2]
- Momentum[k1] - Momentum[k2])//ExpandScalarProduct//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m4, M4contracted];
m4[p1, p2, k0, k1, k2] = (SudakovVariables[M4[p1, p2, k0, k1, k2]]/.Momentum[k0] -> Momentum[p1] + Momentum[p2]
- Momentum[k1] - Momentum[k2])//ExpandScalarProduct;

M4contracted = (Contract[m4[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0
/. Pair[Momentum[k1],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M4combined = CollectByPolStructures[Expand[M4contracted], {p1, p2, k0, k1, k2}]

M4test = (M4[p1, p2, k0, k1, k2]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct;

(*Testing Gauge Invariance*)
m4GI = Contract[M4[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify;
M4GI = SudakovVariables[m4GI]//Simplify;
M4GIcombined = Collectmomentum[expandAndWrapMomenta[M4GI], Momentumlist]


(*Coupling of 2 scalars and 2 gravitons, bottom scalar*)
M5[p1_, p2_, k0_, k1_, k2_] = (Calc[GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p1-k0]]*
GravitonScalarVertex[{\[Mu]1, \[Nu]1, \[Mu]3, \[Nu]3}, p2, -k2, 0]]/. D -> 4/.Momentum[k0] -> Momentum[p1] + Momentum[p2]
- Momentum[k1] - Momentum[k2])//ExpandScalarProduct//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m5, M5contracted];
m5[p1, p2, k0, k1, k2] = (SudakovVariables[M5[p1, p2, k0, k1, k2]]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct//Simplify;

M5contracted = (Contract[m5[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M5combined = CollectByPolStructures[Expand[M5contracted], {p1, p2, k0, k1, k2}]

(*Testing Gauge Invariance*)
m5GI = Contract[M5[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify; 
M5GI = SudakovVariables[m5GI]//Simplify;
M5GIcombined = Collectmomentum[expandAndWrapMomenta[M5GI], Momentumlist]


(*Initial bremstraulgh, bottom scalar*)
M6[p1_, p2_, k0_, k1_, k2_] = Calc[GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p1-k0]]*
GravitonScalarVertex[{\[Mu]1, \[Nu]1}, p2, -p2 + k1, 0]*
FeynAmpDenominatorExplicit[ScalarPropagator[p2 - k1, 0]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2 - k1, -k2, 0]]/. D -> 4//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m6, M6contracted];
m6[p1, p2, k0, k1, k2] = (SudakovVariables[M6[p1, p2, k0, k1, k2]]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct//Simplify;

M6contracted = (Contract[m6[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M6combined = CollectByPolStructures[Expand[M6contracted], {p1, p2, k0, k1, k2}]

(*Testing Gauge Invariance*)
m6GI = Contract[M6[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify;
M6GI = SudakovVariables[m6GI]//Simplify
M6GIcombined = Collectmomentum[expandAndWrapMomenta[M6GI], Momentumlist]


(*Final bremstraulgh, bottom scalar*)
M7[p1_, p2_, k0_, k1_, k2_] = Calc[GravitonScalarVertex[{\[Mu]2, \[Nu]2}, p1, -k0, 0]*
FeynAmpDenominatorExplicit[GravitonPropagator[\[Mu]3, \[Nu]3, \[Mu]2, \[Nu]2, p1-k0]]*
GravitonScalarVertex[{\[Mu]3, \[Nu]3}, p2,  -k1 - k2, 0]*
FeynAmpDenominatorExplicit[ScalarPropagator[k1 + k2, 0]]*
GravitonScalarVertex[{\[Mu]1, \[Nu]1}, k1 + k2, -k2, 0]]/. D -> 4//Simplify;

(*Now I make the sudakov parametrization, and also conctract with the polarization tensor*)
Clear[m7, M7contracted];
m7[p1, p2, k0, k1, k2] = (SudakovVariables[M7[p1, p2, k0, k1, k2]]/.Momentum[k1] -> Momentum[p1] + Momentum[p2]
- Momentum[k0] - Momentum[k2])//ExpandScalarProduct//Simplify;

M7contracted = (Contract[m7[p1, p2, k0, k1, k2] PolarizationTensor[\[Mu]1, \[Nu]1, k1]]
/. Pair[Momentum[Polarization[k1,Complex[0,1]]],Momentum[Polarization[k1,Complex[0,1]]]] -> 0)//Simplify;

M7combined = CollectByPolStructures[Expand[M7contracted], {p1, p2, k0, k1, k2}]

(*Testing Gauge Invariance*)
m7GI = Contract[M7[p1, p2, k0, k1, k2]Pair[LorentzIndex[\[Mu]1,4],Momentum[k1,4]]]//Simplify;
M7GI = SudakovVariables[m7GI]//Simplify
M7GIcombined = Collectmomentum[expandAndWrapMomenta[M7GI], Momentumlist]


(*I want to check the Gauge Invariance*)
(*MGItotal = (Collectmomentum[expandAndWrapMomenta[(M1GIcombined + M2GIcombined + M3GIcombined +M4GIcombined + M5GIcombined + 
M6GIcombined + M7GIcombined)/. k0 -> p1 + p2 - k1 - k2], Momentumlist])//Simplify*)
Momentumlist2 = {Pair[LorentzIndex[\[Nu]1],Momentum[p1]], Pair[LorentzIndex[\[Nu]1],Momentum[p2]], Pair[LorentzIndex[\[Nu]1],Momentum[kperp]], Pair[LorentzIndex[\[Nu]1],Momentum[kprimeperp]]};

MGItotal = Collectmomentum[expandAndWrapMomenta[(M2GIcombined + M3GIcombined + \[Beta]1*(2*M1GIcombined + M4GIcombined)/(\[Beta]1 + \[Alpha]2)
/.Momentum[p2] -> Momentum[k0] + Momentum[k1] + Momentum[k2] - Momentum[p1])], Momentumlist]//Simplify

MGItotal2 = Collectmomentum[expandAndWrapMomenta[(M6GIcombined + M7GIcombined + \[Alpha]2*(2*M5GIcombined + M4GIcombined)/(\[Beta]1 + \[Alpha]2)
/.Momentum[k0] -> Momentum[p1] + Momentum[p2] - Momentum[k1] - Momentum[k2])], Momentumlist]//Simplify


(* ::Input:: *)
(**)


Mcombinedtotal = ExpandScalarProduct[((2*M1combined + M2combined + M3combined + M4combined + 2*M5combined + M6combined + M7combined)
/.Momentum[k0] -> Momentum[p1]*(1 - \[Alpha]1) - Momentum[p2]*\[Beta]1 - Momentum[kperp]
/.Momentum[k2] -> Momentum[p1]*(\[Alpha]2) + Momentum[p2]*(1 + \[Beta]2) + Momentum[kprimeperp])]//Simplify;
CollectByPolStructures[Mcombinedtotal, {p1, p2, kperp, kprimeperp}];

Mcombinedtotal2 = ExpandAll[ExpandScalarProduct[ReplaceAll[Mcombinedtotal, 
{Momentum[kprimeperp] -> (Momentum[kperp] + Momentum[kprimeperp] + (\[Alpha]1 - \[Alpha]2)*Momentum[p1] + (\[Beta]1 - \[Beta]2)*Momentum[p2])/2,
Momentum[kperp] ->  (Momentum[kperp] + Momentum[kprimeperp] - (\[Alpha]1 - \[Alpha]2)*Momentum[p1] - (\[Beta]1 - \[Beta]2)*Momentum[p2])/2}]]];

(*As we always have something like kperp + kprimerperp, I put them together in qperp*)
Mcombinedtotal3 = ExpandAll[ExpandScalarProduct[Mcombinedtotal2/.Momentum[kperp] -> Momentum[qperp] - Momentum[kprimeperp]]];

Mfinal = CollectByPolStructures[Mcombinedtotal3, {p1, p2, qperp}]//Simplify


finalList = CollectPolarizationStructures[Mfinal//Expand]//Simplify;

(*Here I define the k*eps structures, to substract them and check*)
ksquared = \!\(TraditionalForm\`Power[Pair[Momentum[kperp], Momentum[Polarization[k1, Complex[0, 1]]]], 2]\);
kprime2 = \!\(TraditionalForm\`Power[Pair[Momentum[kprimeperp], Momentum[Polarization[k1, Complex[0, 1]]]], 2]\);
kkprime = Times[Pair[Momentum[kperp],Momentum[Polarization[k1,Complex[0,1]]]], Pair[Momentum[kprimeperp],Momentum[Polarization[k1,Complex[0,1]]]]];
pk = Times[Pair[Momentum[kperp],Momentum[Polarization[k1,Complex[0,1]]]], Pair[Momentum[p1],Momentum[Polarization[k1,Complex[0,1]]]]];
pkprime = Times[Pair[Momentum[kprimeperp],Momentum[Polarization[k1,Complex[0,1]]]], Pair[Momentum[p1],Momentum[Polarization[k1,Complex[0,1]]]]];
p2k = Times[Pair[Momentum[kperp],Momentum[Polarization[k1,Complex[0,1]]]], Pair[Momentum[p2],Momentum[Polarization[k1,Complex[0,1]]]]];
p2kprime = Times[Pair[Momentum[kprimeperp],Momentum[Polarization[k1,Complex[0,1]]]], Pair[Momentum[p2],Momentum[Polarization[k1,Complex[0,1]]]]];
psquared = \!\(TraditionalForm\`Power[Pair[Momentum[p1], Momentum[Polarization[k1, Complex[0, 1]]]], 2]\);
qsquared = \!\(TraditionalForm\`Power[Pair[Momentum[qperp], Momentum[Polarization[k1, Complex[0, 1]]]], 2]\);

finalList[[1]] + finalList[[2]] + finalList[[3]]//FullSimplify;

finalList[[1]];
(*This checks are usefull when I have kperp and kprimeperp. Once that I have put them together are not useful anymore.*)
(*
If[finalList[[1]]/ksquared - finalList[[3]]/kprime2 =!= 0,
Print["Something went wrong"],
Print["We are going in the right path"]]

If[finalList[[4]]/pk - finalList[[5]]/pkprime =!= 0,
Print["Something went wrong"],
Print["We are going in the right path"]]

If[finalList[[7]]/p2k - finalList[[8]]/p2kprime =!= 0,
Print["Something went wrong"],
Print["We are going in the right path"]]*)

(*I defined the amplitudes that I will be comparing with*)
Amplitudkk = I*Power[\[Kappa]2, 3]*(1/(\[Beta]1*\[Alpha]2) - (1 + \[Beta]1)/(\[Beta]1*(\[Alpha]1 + \[Beta]1)) - (1  - \[Alpha]2)/(\[Alpha]2*(\[Alpha]2 + \[Beta]2)))/8;
Amplitudkp = I*Power[\[Kappa]2, 3]*(-(\[Alpha]1 - \[Alpha]2)^2/(\[Alpha]1*\[Alpha]2*\[Beta]1) - (\[Alpha]1 - 1)*(\[Alpha]1 + \[Alpha]2)/(\[Alpha]1*(\[Alpha]1 + \[Beta]1)) 
+ (\[Alpha]2 - 1)*(\[Alpha]1 + \[Alpha]2 - 2)/(\[Alpha]2*(\[Alpha]2 + \[Beta]2)))/8;
Amplitudkp2 = I*Power[\[Kappa]2, 3]*(-(\[Beta]1 - \[Beta]2)^2/(\[Alpha]2*\[Beta]1*\[Beta]2) - (\[Beta]1 + 1)*(\[Beta]1 + \[Beta]2 + 2)/(\[Beta]1*(\[Alpha]1 + \[Beta]1)) 
+ (\[Beta]2 + 1)*(\[Beta]1 + \[Beta]2)/(\[Beta]2*(\[Alpha]2 + \[Beta]2)))/8;
Amplitudpp = I*Power[\[Kappa]2, 3]*((\[Alpha]1 - \[Alpha]2)^3/(\[Alpha]1*\[Alpha]2*\[Beta]1) + 4*(\[Alpha]1 -1)*(\[Alpha]1 - \[Alpha]2 - 1)/(\[Alpha]2*(\[Beta]2 - \[Beta]1)) 
- (\[Alpha]1 -1)*(\[Alpha]1 + \[Alpha]2)^2/(\[Alpha]1*(\[Alpha]1 + \[Beta]1)) + (\[Alpha]2 -1)*(\[Alpha]1 + \[Alpha]2 -2)^2/(\[Alpha]2*(\[Alpha]2 + \[Beta]2)))/8;
Amplitudp2p =  I*Power[\[Kappa]2, 3]*((\[Alpha]1 + \[Alpha]2 - 2)*(\[Beta]1 - \[Alpha]2) + (\[Alpha]1 + \[Alpha]2)*(\[Beta]2 + \[Alpha]2))*((\[Alpha]1 - \[Alpha]2)/(\[Alpha]1*\[Alpha]2*\[Beta]1) + (1 - \[Alpha]1)/(\[Alpha]1*(\[Alpha]1 + \[Beta]1)) +
(\[Alpha]2 - 1)/(\[Alpha]2*(\[Alpha]2 + \[Beta]2)))/8;
Amplitudp2p2 =  I*Power[\[Kappa]2, 3]*(-(\[Beta]1 - \[Beta]2)^3/(\[Alpha]2*\[Beta]1*\[Beta]2) - 4*(\[Beta]1 - \[Beta]2 - 1)*(\[Beta]2 + 1)/((\[Alpha]1 - \[Alpha]2)*\[Beta]1) 
-(\[Beta]1 + 1)*(\[Beta]1 + \[Beta]2 +2)^2/(\[Beta]1*(\[Alpha]1 + \[Beta]1))  + (\[Beta]2 + 1)*(\[Beta]1 + \[Beta]2)^2/(\[Beta]2*(\[Alpha]2 + \[Beta]2)))/8;

If[(\!\(TraditionalForm\`2*finalList[\([6]\)]/ksquared\) - Amplitudkk) =!= 0,
Print["Something went wrong"],
Print["We are going in the right path"]]

finalList[[1]]/Amplitudpp//Simplify

finalList[[2]]/Amplitudp2p//Simplify

finalList[[3]]/Amplitudp2p2//Simplify

finalList[[4]]/(Amplitudkp)//Simplify

finalList[[5]]/Amplitudkp2//Simplify

finalList[[6]]/Amplitudkk//Simplify


(* ::Input:: *)
(**)


Ampaproxpp = \[Alpha]1^2 - 4*\[Alpha]1*\[Beta]1/\[Beta]2 + 4*\[Beta]1^2/\[Beta]2^2 + 4*\[Alpha]2*\[Beta]1/\[Beta]2^2;
Ampaproxp2p2 = \[Beta]2^2 + 4*\[Alpha]2*\[Beta]2/\[Alpha]1 + 4*\[Alpha]2*\[Beta]1/\[Alpha]1^2 + 4*\[Alpha]2^2/\[Alpha]1^2;
Ampaproxp2p = \[Alpha]1*\[Beta]2 - 2*\[Beta]1 + 2*\[Alpha]2;
Ampaproxpk = -\[Alpha]1 + 2*\[Beta]1/\[Beta]2;
Ampaproxp2k = - \[Beta]2 - 2*\[Alpha]2/\[Alpha]1;

FinalListapprox = Finalapprox /@ finalList /(Finalapprox[finalList[[6]]]/qsquared)//Simplify;

FinalListapprox[[1]]/Ampaproxpp//Simplify

FinalListapprox[[2]]/Ampaproxp2p//FullSimplify

FinalListapprox[[3]]/Ampaproxp2p2//Simplify

FinalListapprox[[4]]/Ampaproxpk//Simplify

FinalListapprox[[5]]/Ampaproxp2k//Simplify
Finalapprox[finalList[[6]]]


expr = Times[a, Pair[Momentum[kperp],Momentum[Polarization[k1,Complex[0,1]]]],
Pair[Momentum[kprimeperp],Momentum[Polarization[k1,Complex[0,1]]]]];

FinalListMomenta = PolToFreeIndicesSym[#, {\[Mu], \[Nu]}] & /@ FinalListapprox;
Total[FinalListMomenta]

Omega[mu_] := ((\[Alpha]1 - 2*\[Beta]1/\[Beta]2)Pair[Momentum[p1], LorentzIndex[mu]] + (\[Beta]2 + 2*\[Alpha]2/\[Alpha]1)*Pair[Momentum[p2], LorentzIndex[mu]] 
- Pair[Momentum[qperp], LorentzIndex[mu]])

Npaper[mu_] := -2*I*Sqrt[\[Beta]1*\[Alpha]2]*(Pair[Momentum[p1], LorentzIndex[mu]]/\[Beta]2 + Pair[Momentum[p2], LorentzIndex[mu]]/\[Alpha]1)

Resultcomparison = Omega[\[Mu]]*Omega[\[Nu]] - Npaper[\[Mu]]*Npaper[\[Nu]]//Simplify;
Resultcomparison - Total[FinalListMomenta]//Simplify



