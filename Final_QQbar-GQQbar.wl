(* ::Package:: *)

(* :Title: GlGl-QQbar                                                     	*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 1990-2024 Rolf Mertig
	Copyright (C) 1997-2024 Frederik Orellana
	Copyright (C) 2014-2024 Vladyslav Shtabovenko
*)

(* :Summary:  Gl Gl -> Q Qbar, QCD, matrix element squared, tree           	*)

(* ------------------------------------------------------------------------ *)



(* ::Title:: *)
(*Quark-antiquark pair production from gluon-gluon annihilation*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Gl Gl -> Q Qbar, QCD, matrix element squared, tree";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynArts"};
<<FeynCalc`
$FAVerbose = 0;

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Generate Feynman diagrams*)


(* ::Text:: *)
(*Nicer typesetting*)


MakeBoxes[pa,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(a\)]\)";
MakeBoxes[pb,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(b\)]\)";
MakeBoxes[k0,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(0\)]\)";
MakeBoxes[k1,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(1\)]\)";
MakeBoxes[k2,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(2\)]\)"


diags = InsertFields[CreateTopologies[0, 2 -> 3], {F[3], F[3]}->
		{F[3],  V[5], F[3]}, InsertionLevel -> {Classes},
		Model -> "SMQCD", ExcludeParticles -> {S, U, V[1], V[2]}];

Paint[diags, FieldNumbers -> True, ColumnsXRows -> {2, 1}, Numbering -> Simple,
	SheetHeader->None,ImageSize->{512,256}];


(* ::Section:: *)
(*Obtain the amplitude*)


(*We will focus on changing the labbels of the amplitude in order to have something nicer.*)
(*Format[DiracGamma[LorentzIndex[x_]]] := Superscript["\[Gamma]", ToString[x]];*)
ClearAll[q1]
ClearAll[Amp, amp]
amp[0] = FCFAConvert[CreateFeynAmp[
    diags], IncomingMomenta->{pa,pb},
	OutgoingMomenta->{k0, k1, k2},UndoChiralSplittings->True, ChangeDimension->4,
	TransversePolarizationVectors->{k1}, List->True, SMP->True,
	Contract->True, DropSumOver->True];

(*Nicer output*)
Amp[0] = amp[0] /. {
    SUNIndex[Glu6] -> \[Alpha], 
    SUNIndex[Glu4] -> \[Beta], 
    SUNIndex[Glu5] -> \[Gamma], 
    SUNFIndex[Col1] -> a,
    SUNFIndex[Col2] -> b,
    SUNFIndex[Col3] -> c,
    SUNFIndex[Col5] -> d,
    SUNFIndex[Col6] -> e,
    MQU[Index[Generation, _]] -> 0,
    SP[k1,k1] -> 0,
    Index[Generation, 1] -> 1,  (* Gen1 -> i *)
    Index[Generation, 3] -> 1,  (* Gen3 -> i *)
    Index[Generation, 2] -> 2,  (* Gen2 -> j *)
    Index[Generation, 5] -> 2  (* Gen5 -> j *)

};

momentumConservationRules = {
   k2 + k1 - pb -> pa - k0,
   pb - k2 - k0 -> k1 - pa
  (* More can be added if needed *)
};

replaceDen[p_, name_] := 
  FeynAmpDenominator[
    PropagatorDenominator[Momentum[expr_], 0]
  ] /; Simplify[expr^2 - p^2] === 0 -> 1/name;

Amp[0] = Amp[0]/. momentumConservationRules;
(*This is important to put because the later function will not be able to recognize the denominator *)
Amp[0] = Amp[0] /. {
					replaceDen[k2 - pb, Subscript[t, 2]],
					replaceDen[k1 - pb, -Subscript[s, b1]],
					replaceDen[pa - k0, -Subscript[s, a0]],
					replaceDen[pa - k1, -Subscript[s, a1]],
					replaceDen[-k0 - k1, Subscript[s,01]],
					replaceDen[-k1 - k2, Subscript[s,12]]
					
					}
					
t1 = SP[pa - k0, pa - k0];
t2 = SP[k2 - pb, k2 - pb];


replaceSP[p1_, q1_, name_] := SP[p1, q1] -> name;

Mup = (Amp[0][[7]] + Amp[0][[10]] + t1/(t1-t2)*Amp2)/. {
					replaceSP[k2 - pb, k2 - pb, Subscript[t, 2]],
					replaceSP[k1 - pb, k1 - pb, -Subscript[s, b1]],
					replaceSP[pa - k0, pa - k0, -Subscript[s, a0]],
					replaceSP[pa - k1, pa - k1, -Subscript[s, a1]]
					};
					
Mup = FactorCommonTerm[Mup, SUNTF[{\[Alpha]}, d, b]][[1]]
Tcosas1 = FactorCommonTerm[Mup, SUNTF[{\[Alpha]}, d, b]][[2]]
Mdown = (Amp[0][[1]] + Amp[0][[3]] - t2/(t1-t2)*Amp2)/. {
					replaceSP[k2 - pb, k2 - pb, Subscript[t, 2]],
					replaceSP[k1 - pb, k1 - pb, -Subscript[s, b1]],
					replaceSP[pa - k0, pa - k0, -Subscript[s, a0]],
					replaceSP[pa - k1, pa - k1, -Subscript[s, a1]]
					};


(* ::Section:: *)
(*Function to compute the effective vertex*)


(*I will start by listing and explaining the different function that I have defined, and then apply them. Note
that I did not work with these functions directly, I have undergone a process to reach this point.*)
(*First of all, we want to unconctract all the Lorentz indices. In order to do so, we have the function Uncontract.
However, this function does not work as we want. We want to unconctract things nicely, and for example
((p+q)\cdot \gamma --> (p+q)_\mu \gamma^\mu). The function Uncontract would do
((p+q)\cdot \gamma --> p_\mu gamma^\mu + q_\mu \gamma^\mu). In order to solve this, I have defined the function
NiceUncontract (NU)
*)
SetAttributes[NiceUncontract, HoldFirst];

NiceUncontract[expr_, momenta___] := Module[
  {preprocessed},
  
  (* If momenta are given, Uncontract *)
  preprocessed = If[
    {momenta} === {},
    expr,
    Uncontract[expr, momenta]
  ];
  
  (* Now preprocess gammas *)
  preprocessed = preprocessed //. {
    
    (* Gamma with single momentum *)
    DiracGamma[Momentum[p_]] :> Module[{mu},
      Dot[
        Momentum[p, LorentzIndex[mu = Unique["mu"]]],
        DiracGamma[LorentzIndex[mu]]
      ]
    ],
    
    (* Gamma with sum of two momenta *)
    DiracGamma[Momentum[Plus[p1_, p2_]]] :> Module[{mu},
      Dot[
        Plus[
          Momentum[p1, LorentzIndex[mu = Unique["mu"]]],
          Momentum[p2, LorentzIndex[mu]]
        ],
        DiracGamma[LorentzIndex[mu]]
      ]
    ],
    
    (* Gamma with minus momentum *)
    DiracGamma[Momentum[Times[-1, p_]]] :> Module[{mu},
      Dot[
        -Momentum[p, LorentzIndex[mu = Unique["mu"]]],
        DiracGamma[LorentzIndex[mu]]
      ]
    ]
    
  };
  
  (* Final output *)
  preprocessed
];
(*However, this leaves the Lorentz indices in a bad way (we can define a function to leave them nicer). We have defined
the function AutoRenameLorentzIndices (ARLI) in order to get the better indices*)
AutoRenameLorentzIndices[expr_] := Module[
  {indices, greekNames, rules},
  
  (* Step 1: Find all Lorentz dummy indices *)
  indices = FCGetDummyIndices[expr, {LorentzIndex}];
  
  (* Step 2: Define the list of Greek letters you want *)
  greekNames = {\[Mu], \[Nu], \[Rho], \[Sigma], \[Lambda], \[Kappa], \[Alpha], \[Beta], \[Gamma], \[Delta], \[Xi], \[Eta], \[Tau]};
  
  (* Step 3: Build the replacement rules *)
  rules = Thread[indices -> greekNames[[;; Length[indices]]]];
  
  (* Step 4: Replace and simplify *)
  expr /. rules // Simplify
];
(* This functions work well with gammas and all of the spinor stuff. It should be tested out with scalars.
I am planing to do as soon as I can. We have seen a problem with these. What if we have the sum of two terms?
For example, \phi(p1)\gamma \cdot p4 \phi(p2)\phi(p3)\gamma \cdot p1 \phi(p4) 
+ \phi(p1)\gamma \cdot p3 \phi(p2)\phi(p3)\gamma \cdot p2 \phi(p4) . Tipycally, we find 
expressions like these in the amplitudes. To solve this, we have defined two functions. The first one applies
ARLI and NU together to each term, which is called ProcessTerm (PT). The second one will just detect if I have
a sum in any of the amplitudes, and if there is any, it will separate each summand. When done, it will aplly
PT to each summand. This function has been called ProcessAmplitude (PA).
*)

(* Function to apply NiceUncontract and AutoRenameLorentzIndices to each term *)
ProcessTerm[term_] := Module[{uncontractedTerm, renamedTerm},
    
    (* Apply NiceUncontract to each Dot term *)
    uncontractedTerm = term /. dot:Dot[___] :> NiceUncontract[dot];
    
    (* Apply AutoRenameLorentzIndices to the uncontracted term *)
    renamedTerm = AutoRenameLorentzIndices[uncontractedTerm];
    
    (* Return the processed term *)
    renamedTerm
]

ProcessAmplitude[term_] := 
  If[Head[term] === Plus, 
    (* If the term contains Plus, apply the processing steps *)
    ProcessTerm[term], 
    (* If no Plus, apply the NiceUncontract and AutoRenameLorentzIndices steps *)
    Module[{uterm, LIuterm},
      uterm = NiceUncontract[term];
      LIuterm = AutoRenameLorentzIndices[uterm];
      LIuterm
    ]
  ]
  
(* Now we want to separate the polarization of the external photons or gluons. In order to do so, we have first
to notice the internal structure of the contractions. For example, if we have \eps(q) \cdot p1 it will be much
different than \gamma \cdot \eps(q). This is how interanlly it can be treated with the function
Pair (how the \eps(q) \cdot p works) or Dot (how \gamma \cdot \eps(q) works). 
Both functions do the same, but in order to define a unique way to exctract the polarization from all the terms we 
first need to change from Pair to Dot. In order to do so we defined ConvertPairToDot (CPD). This function is bound
to first apply the ARLI and NU (or equivalently PA), by how it is defined. *)
ConvertPairToDot[expr_] := expr /. {
    Pair[Momentum[Polarization[k_, c_, opts___]], Momentum[p_]] :> 
      Dot[Momentum[Polarization[k, c, opts], LorentzIndex[\[Mu]]], Momentum[p, LorentzIndex[\[Mu]]]],
    
    Pair[Momentum[p_], Momentum[Polarization[k_, c_, opts___]]] :> 
      Dot[Momentum[Polarization[k, c, opts], LorentzIndex[\[Mu]]], Momentum[p, LorentzIndex[\[Mu]]]]
};
(*As before, we separate the cases in which we have a sum or not. In order to do so, we have defined the functions
FactorOutPolarizationSingle (FPS) and FactorOutPolarization (FP). How these function works, is to define a fixed
index for ALL the polarization in ALL the amplitudes (in our case \tau), and put \eps^\mu -> \eps_\tau g^(\mu \tau).
This is why we need to apply first ARLI and NU, so that we have separated the indices.
*)

FactorOutPolarizationSingle[expr_, lorentzIndex_: \[Tau]] := Module[
  {newExpr, pol, factor},
  
  (* Replace all Polarization vectors and force Lorentz index to lorentzIndex *)
  newExpr = expr /. 
    Momentum[Polarization[k_, c_, opts___], LorentzIndex[i_]] :> 
      Momentum[Polarization[k, c, opts], LorentzIndex[lorentzIndex]] *
      MetricTensor[LorentzIndex[i], LorentzIndex[lorentzIndex]];
  
  (* Extract unique polarization vector(s) *)
  pol = Cases[newExpr, 
    Momentum[Polarization[_, _, ___], LorentzIndex[lorentzIndex]], 
    All
  ] // DeleteDuplicates;
  
  (* Factor out if exactly one unique polarization *)
  If[Length[pol] == 1,
    factor = First[pol];
    factor * (newExpr /. factor -> 1),
    newExpr
  ]
]

FactorOutPolarizations[expr_, lorentzIndex_: \[Tau]] := Module[
  {newExpr, terms},
  
  (* If the expression is a sum (Plus) *)
  If[Head[expr] === Plus,
    terms = List @@ expr;
    newExpr = Plus @@ (FactorOutPolarizationSingle[#, lorentzIndex] & /@ terms),
    newExpr = FactorOutPolarizationSingle[expr, lorentzIndex]
  ];
  
  newExpr
]

(*We are at the last step. Now we want to rename some indices in a clear way, in order to do things nicer and
leave the expression a simplified way. For example, as we have done everything, we may have
\eps^\tau(\phi(p1)\gamma^\tau\phi(p2)\phi(p3)\gamma^\mu p1_\mu\phi(p4) +\.08 
\phi(p1)\gamma^\mu \phi(p2)\phi(p3)\gamma^\mu p1_\tau\phi(p4)), 
and we want to have the first index to be the same
in order to obtain
\eps^\tau\phi(p1)\gamma^\mu\phi(p2)(g^{\mu \tau}\phi(p3)\gamma^\nu p1_\nu\phi(p4) +\.08 \phi(p3)\gamma^\mu p1_\tau\phi(p4))
As we will obtain the effective vertex this way. 
This is done in the function: ReplaceGammaIndexInLastSimpleSpinorChain.
*)

ClearAll[ReplaceGammaIndicesInSpinorChain]
ReplaceGammaIndicesInSpinorChain[expr_, {kin_, pin_}, dummyIndex_] := Module[
  {pattern, replaceInTerm, gammaChain, muList, dummyList, metricFactors},

  (* Match spinor chain with arbitrary gamma chain between spinors *)
  pattern = Dot[
    Spinor[Momentum[kin], 0, 1],
    ___,
    DiracGamma[LorentzIndex[mu__]],
    ___,
    Spinor[Momentum[pin], 0, 1]
  ];

  (* Replacement function for one spinor chain *)
  replaceInTerm[term_] := term /. Dot[
    Spinor[Momentum[kin], 0, 1],
    seq___,
    Spinor[Momentum[pin], 0, 1]
  ] :> Module[
    {
      gammas = Cases[{seq}, DiracGamma[LorentzIndex[mu_]] :> mu, \[Infinity]],
      dummies, metrics, newSeq
    },
    (* Create general dummy indices using the provided dummyIndex *)
    dummies = Table[Symbol[ToString[dummyIndex] <> ToString[i]], {i, Length[gammas]}];
    
    (* Create the metric factors for each pair of gammas *)
    metrics = MapThread[
      MetricTensor[LorentzIndex[#1], LorentzIndex[#2]] &,
      {gammas, dummies}
    ];
    
    (* Replace the gamma indices with the corresponding dummy index *)
    newSeq = Replace[{seq}, DiracGamma[LorentzIndex[mu_]] :> DiracGamma[LorentzIndex[dummies[[Position[gammas, mu][[1, 1]]]]]], {1}];
    
    (* Reassemble the spinor chain and apply the metric factors *)
    Dot[Spinor[Momentum[kin], 0, 1], Sequence @@ newSeq, Spinor[Momentum[pin], 0, 1]] * Times @@ metrics
  ];

  (* Apply the replacement function to the whole expression *)
  Which[
    Head[expr] === Plus, Plus @@ (replaceInTerm /@ List @@ expr),
    Head[expr] === Times && MemberQ[List @@ expr, _Plus],
    Module[{plusPart, otherParts},
      plusPart = Select[List @@ expr, Head[#] === Plus &];
      otherParts = Select[List @@ expr, Head[#] =!= Plus &];
      Times @@ Join[
        otherParts,
        {Plus @@ (replaceInTerm /@ List @@ First[plusPart])}
      ]
    ],
    True, replaceInTerm[expr]
  ]
]



(*Finally this function what does is to separate the spinors that I want. I would like to just make
it a bit more clear, but that is what I wanted.*)
ClearAll[FactorSpinorChain];
FactorSpinorChain[expr_, k_, p_] := Module[{terms, opsTerms, opsSum},
  (* Expand the expression to isolate terms *)
  terms = List @@ Expand[expr];
  
  (* Extract terms that match the pattern for spinor chains *)
  opsTerms = Cases[
    terms,
    coeff_.*Dot[Spinor[Momentum[k], 0, 1], ops___, Spinor[Momentum[p], 0, 1]] :> coeff*spinorChain[Dot[ops]]
  ];
  
  (* Combine extracted spinor chain terms *)
  opsSum = Total[opsTerms /. spinorChain[x_] :> x];
  
  (* Return the result as a dot product *)
  Dot[Spinor[Momentum[k], 0, 1], opsSum, Spinor[Momentum[p], 0, 1]]
]

(*This function removes the Fermion Bilinear that has \phi(momL)\gamma\mu \phi(momR).*)
removeFermionBilinear[expr_, momL_, momR_, mu_] := 
  expr /. 
    Dot[Spinor[Momentum[momL], 0, 1], DiracGamma[LorentzIndex[mu]], Spinor[Momentum[momR], 0, 1]] :> Sequence[]
    
(*Same as before but for polarizations*)
removePolarization[expr_, mom_, lor_] := 
  expr /. 
    Momentum[
      Polarization[mom, Complex[0, -1], Rule[Transversality, True]], 
      LorentzIndex[lor]
    ] :> Sequence[]

    
(*Same as before, but for a general expression as \phi(momL) A \phi(momR) which will return A*)
removeOuterSpinors[expr_, momL_, momR_] := 
  expr /. Dot[
    Spinor[Momentum[momL], 0, 1], 
    mid_, 
    Spinor[Momentum[momR], 0, 1]
  ] :> mid
  
(*Changes our expr with the Sudakov variables*)
SudakovVariables[expr_] := (expr/. Subscript[t,2] -> -s*\[Alpha]2 /. Subscript[s, a0] -> -t/.t -> +s*\[Beta]1 
/.Subscript[s, a1] -> s*(\[Beta]1 - \[Beta]2)/. Subscript[s, 01] -> -s*(\[Alpha]2 + \[Beta]2)/. Subscript[s, 12] -> s*(\[Alpha]1 + \[Beta]1)
/.Subscript[s, b1] -> s*(\[Alpha]1 - \[Alpha]2)
/. Momentum[k0, idx_] :> (1 - \[Alpha]1)*Momentum[pa, idx] - \[Beta]1*Momentum[pb, idx] - Momentum[kperp1, idx]
/. Momentum[k2, idx_] :>  \[Alpha]2*Momentum[pa, idx] + (1 + \[Beta]2)*Momentum[pb, idx] + Momentum[kperp2, idx]
/. Momentum[k1, idx_] :> (\[Alpha]1 - \[Alpha]2)*Momentum[pa, idx] + (\[Beta]1 - \[Beta]2)*Momentum[pb, idx] + (Momentum[kperp1, idx]- 
Momentum[kperp2, idx])
/. Momentum[q1, idx_] :> \[Alpha]1*Momentum[pa, idx] + \[Beta]1*Momentum[pb, idx] + Momentum[kperp1, idx]
/. Momentum[q2, idx_] :>  \[Alpha]2*Momentum[pa, idx] + \[Beta]2*Momentum[pb, idx] + Momentum[kperp2, idx]//Simplify)

(*This function helps us with computation. It just changes a bit of the internal structure to work better*)
ClearAll[ExpandMomentumSums]

ExpandMomentumSums[expr_] := FixedPoint[
  ReplaceAll[#, Momentum[Plus[a_, b_], mu_] :> Plus[Momentum[a, mu], Momentum[b, mu]]] &,
  expr
]

(*This just expands a*(b + c) -> a*b + a*c. This cannot be directly done with FeynCalc functions as it has a 
different internal structure*)
ClearAll[ExpandDotProducts]
ExpandDotProducts[expr_] := expr /. {
  Dot[a___, Plus[b_, c_], d___] :> Dot[a, b, d] + Dot[a, c, d],
  Dot[a___, Times[b_, c_], d___] :> b Dot[a, c, d]
}

(*Applies the last two functions simultanieuosly*)
PreprocessExpr[expr_] := 
  ExpandDotProducts @ ExpandMomentumSums[expr]
  
(*Uses the Gordon decomposition directly, by changing \gamma^\nu -> p^\nu. Note
that before I have already applied some functions to get rid of the spinorial structure.*)
ClearAll[GordonDecom]

GordonDecom[expr_, p_] := 
  expr /. DiracGamma[LorentzIndex[nu_]] :> 
    2*Momentum[p, LorentzIndex[nu]]

(*This is the Eikonal approximation, which works by making k0 \approx p1, k2 \approx p2, p1 *a k1 \approx p1, \.08
p2 + b*k1 \approx p2*)
EikonalApprox[expr_] := Module[{a, b, c, d, e, f, g},
a = expr/. k2 -> pb + q2//ExpandMomentumSums;
b = a/. k0 -> pa - q1//ExpandMomentumSums;
c = b/.k1 :> q1 - q2//ExpandMomentumSums;
d = c/.Plus[Momentum[pa,LorentzIndex[rho1_]],Times[alpha1_., Momentum[q2,LorentzIndex[rho1_]]]] :> 
Momentum[pa,LorentzIndex[rho1]];
e = d/.Plus[Momentum[pa,LorentzIndex[rho2_]],Times[alpha2_., Momentum[q1,LorentzIndex[rho2_]]]] :> 
Momentum[pa,LorentzIndex[rho2]];
f = e/.Plus[Momentum[pb,LorentzIndex[rho3_]],Times[alpha3_., Momentum[q2,LorentzIndex[rho3_]]]] :> 
Momentum[pb,LorentzIndex[rho3]];
g = f/.Plus[Momentum[pb,LorentzIndex[rho4_]],Times[alpha4_., Momentum[q1,LorentzIndex[rho4_]]]] :> 
Momentum[pb,LorentzIndex[rho4]] ;
g//Simplify
 ]
 
(*This function works to replace: \overline{u}(p)\gamma^\nu \slashed{p}\gam\.08ma^\mu u(p) = 4p^\mu p^\nu. 
However, it is made so that it can detect some other objects in the middle and only care about what I have written.*)
replaceInList[list_List, p_] := Module[
  {i, n = Length[list], posMom, posGamma, posGamma2, nu, rho, mu},
  
  For[i = 1, i <= n, i++,
    If[MatchQ[list[[i]], DiracGamma[LorentzIndex[nu_]]],
      
      (* Look for Momentum[p1, LorentzIndex[rho]] after i *)
      posMom = Select[Range[i + 1, n], MatchQ[list[[#]], Momentum[p, LorentzIndex[rho_]]] &];
      
      (* Look for DiracGamma[LorentzIndex[rho]] after i *)
      posGamma = Select[Range[i + 1, n], MatchQ[list[[#]], DiracGamma[LorentzIndex[rho_]]] &];
      
      (* Proceed only if both positions were found *)
      If[posMom =!= {} && posGamma =!= {},
        
        (* safe access to First[posGamma] *)
        posGamma2 = Select[
          Range[posGamma[[1]] + 1, n],
          MatchQ[list[[#]], DiracGamma[LorentzIndex[mu_]]] &
        ];
        
        If[posGamma2 =!= {},
          (* Extract matched positions *)
          posMom = First[posMom];
          posGamma = First[posGamma];
          posGamma2 = First[posGamma2];
          
          (* Extract Lorentz indices *)
          nu = list[[i, 1, 1]];
          rho = list[[posMom, 2, 1]];
          mu = list[[posGamma2, 1, 1]];
          
          (* Perform replacement *)
          Return[
            ReplacePart[
              list,
              {
                i -> 4 * Momentum[p, LorentzIndex[nu]],      (* \[Gamma]^\[Nu] \[RightArrow] 4 p1^\[Nu] *)
                posMom -> Sequence[],                         (* delete p1^\[Rho] *)
                posGamma -> Sequence[],                       (* delete \[Gamma]^\[Rho] *)
                posGamma2 -> Momentum[p, LorentzIndex[mu]]   (* \[Gamma]^\[Mu] \[RightArrow] p1^\[Mu] *)
              }
            ]
          ]
        ]
      ]
    ]
  ];
  
  list (* No match \[RightArrow] return original *)
]

(*This function works together with the above one. The idea is to look for the structrues that have some Dot, 
which we will apply the relation that has been stated just above.*)
replaceDotRecursively[expr_, p_] := Module[{head, args},
  head = Head[expr];
  
  (* If it's Dot, do the replacement *)
  If[head === Dot,
    Dot @@ replaceInList[List @@ expr, p],
    
    (* If atomic (no args), return as is *)
    If[AtomQ[expr],
      expr,
      
      (* Otherwise recursively map over arguments *)
      head @@ (replaceDotRecursively[#, p] & /@ List @@ expr)
    ]
  ]
];

(*This helps to work with Scalar products better, as the interal interpretation of them is a bit conflictive*)
Clear[FixScalarProducts];

FixScalarProducts[expr_] := Module[{rules},
  rules = {
    Dot[a___, Plus[x_, y_], b___] :> Dot[a, x, b] + Dot[a, y, b],
    Dot[a___, Times[c_, v_], b___] :> c Dot[a, v, b],

    (* Core scalar product contractions *)
    Dot[a___, Momentum[x_, LorentzIndex[mu_]], Momentum[y_, LorentzIndex[mu_]], b___] :> 
      SP[x, y] Dot[a, b],

    Momentum[x_, LorentzIndex[mu_]] * Momentum[y_, LorentzIndex[mu_]] :> SP[x, y],

    (* NEW: handle Pair contraction inside Dot *)
    Dot[Pair[LorentzIndex[mu_], LorentzIndex[nu_]], Momentum[x_, LorentzIndex[mu_]], Momentum[y_, LorentzIndex[nu_]]] :> SP[x, y]
  };

  Expand[expr] //. rules // Expand
]

ClearAll[CollectLorentzStructures];
SetAttributes[CollectLorentzStructures, HoldAll];

CollectLorentzStructures[expr_] := Module[
  {
    terms, grouped, getKey, getCoeff, key,
    normalizePair, flattenFactors, sortedKey
  },

  (* Normalize metric symmetry: g^{\[Mu]\[Nu]} = g^{\[Nu]\[Mu]} *)
  normalizePair[Pair[LorentzIndex[a_], LorentzIndex[b_]]] := 
    If[OrderedQ[{a, b}],
      Pair[LorentzIndex[a], LorentzIndex[b]],
      Pair[LorentzIndex[b], LorentzIndex[a]]
    ];
  normalizePair[p_] := p;

  (* Fully flatten all Times chains into a list *)
  flattenFactors[x_] := FixedPoint[(# /. Times -> List) &, x];

  (* Extract Lorentz structures *)
  getKey[term_] := Module[{factors, lorentzTerms},
    factors = flattenFactors[term];
    
    lorentzTerms = Select[factors,
      MatchQ[#, 
        Pair[LorentzIndex[_], Momentum[_]] |
        Pair[Momentum[_], LorentzIndex[_]] |
        Pair[LorentzIndex[_], LorentzIndex[_]] |
        Momentum[_, LorentzIndex[_]]
      ]&
    ];
    (* Normalize metric tensors only *)
    lorentzTerms /. p : Pair[LorentzIndex[_], LorentzIndex[_]] :> normalizePair[p]
  ];

  (* Sort the Lorentz structure *)
  sortedKey[key_List] := Sort[key, OrderedQ[{ToString[#1], ToString[#2]}] &];

  (* Extract coefficient by dividing out Lorentz factors *)
  getCoeff[term_, key_] := Module[{num, den, denKey},
  num = Numerator[term];
  den = Denominator[term];

   (* The momenta that I want to cancel *)
  denKey = Times @@ key;

  (* Now divide numerator by denominator key, and multiply back by remaining denominator *)
  (* To avoid mismatch, divide only if denKey divides den *)
  
  Cancel[num/(den*denKey)]
];


  (* Expand the input expression and break into terms *)
  terms = If[Head[expr] === Plus, List @@ Expand[expr], {Expand[expr]}];

  (* Group similar Lorentz structures *)
  grouped = <||>;
	Do[
	(*I put Numerator[term] because to get the momenta the denominator is not needed
	and it causes some errors because I have terms like a*b + c*d*e*)
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

(*This function works correctly, it uses something like alpha_1 -> c11*\epsilon, etc... and then viceversa. 
It works better for the cases that the other function put in the end does not.*)
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

(*yans4[[8]]//factorAndSumSplit;*) (*This is the only case where I should not do factorandSumSplit, as it will not separate
anything.*)

(* Define the commutator as a replacement rule *)
commRule[expr_] := ReplaceAll[expr, {SUNTF[List[SUNIndex[a_]], SUNFIndex[i_], SUNFIndex[k_]] 
*SUNTF[List[SUNIndex[b_]], SUNFIndex[k_], SUNFIndex[j_]] :> (SUND[SUNIndex[a], SUNIndex[b], SUNIndex[\[Gamma]]]/2 + 
I SUNF[SUNIndex[a], SUNIndex[b], SUNIndex[\[Gamma]]]/2)*SUNTF[List[SUNIndex[\[Gamma]]], SUNFIndex[i], SUNFIndex[j]]}]
           
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


\.08(*Let us take a look at some examples, in order to see how all the functions work. If you think that 
some complicated expression may find some error in all of these functions, you are more than welcome 
to put the expression in the way it should and try it out for yourself. An example of how it should be defined is
(*expr3 = Times[Dot[Spinor[Momentum[k3],0,1],DiracGamma[Momentum[Plus[p1,p2]]],Spinor[Momentum[p2],0,1]],Dot[Spinor[Momentum[k1],0,1],DiracGamma[Momentum[k2]],Spinor[Momentum[p1],0,1]]]*)
I obtained the language from using FullForm[Amp[0][[7]]] (you may change the 7 for any number you like).
*)
ClearAll[expr3, expr2];(*In case I had already defined some expresions*)
expr3 = Amp[0][[10]];
expr2 = Amp[0][[7]];

expr3 = NiceUncontract[expr3]; (*Take out the ; if you want to see the full result*)
expr2 = NiceUncontract[expr2];

(*It is recomeneded that you print this out once at least, in order to see why we have defined ARLI.*) 

expr3 = AutoRenameLorentzIndices[expr3];(*Take out the ; if you want to see the full result*)
expr2 = AutoRenameLorentzIndices[expr2];
(*Also print this out, and check the difference and why it is useful :) *)

Exprfinal = expr3 + expr2;
Exprfinal//Simplify;
(*
Notice that now we have already a spinor term factor out. However, we will want to include another amplitude
which will make things more complicated.
*)


ClearAll[expr3, expr2, expr];

expr = Amp2;(* *t1/(t1-t2) *) (*If I put the last factor it does not compile well. I would have to make the 
change of variable once again*)
\.08(*Also notice that we are working with Amp2 and not Amp[0][[2]] because we have already made
some little relabellings that are usefull.*)
expr2 = Amp[0][[7]];


AMP = Amp[0];
processedAmplitudes = ProcessAmplitude /@ AMP;

(*What we had done before with ARLI and NU for two terms, is now applied directly to the list.*)
processedAmplitudes = ConvertPairToDot[processedAmplitudes];
processedAmplitudes = FactorOutPolarizations[processedAmplitudes];

Amp2 = AMP[[2]]/.{\[Alpha] -> \[Gamma],
  Glu7 -> \[Alpha]};
  
AMP2 = ProcessAmplitude[Amp2];

AMP2 = ConvertPairToDot[AMP2]; (*Take a look at what happens if you do not put this function
and you will see why it is necessary.*)

AMP2 = FactorOutPolarizations[AMP2];
AMP2  = Contract[AMP2]//Simplify;

Mup = processedAmplitudes[[7]] + processedAmplitudes[[10]];
Mup//Simplify;

MUP = ReplaceGammaIndicesInSpinorChain[Mup + t1/(t1-t2)*AMP2, {k2, pb}, \[Chi]]//Simplify;

Muptless = ReplaceAll[MUP, {SUNTF[List[\[Alpha]],d,b] -> 1, 
SUNTF[List[SUNIndex[\[Alpha]]],SUNFIndex[d],SUNFIndex[b]]-> 1}];(*This is to eliminate the common T*)

(*At this point it will be useful to introduce relations with 3 gammas to simplify things
and then use the Gordon decomposition in the Eikonal approximation (k1 \aprox p1 and k3 \aprox p2).*)
Mupsimplified =  FactorSpinorChain[Muptless, k0, pa]//FullSimplify;
Print["M_up = ",Mupsimplified];

(*I make some relabbeling for M_down, as it will be more useful like this*)
AMP2down = ReplaceAll[AMP2, {\[Alpha] -> \[Sigma]}];
AMP2down2 = ReplaceAll[AMP2down, {\[Gamma] -> \[Alpha]}];
AMP2down3 = ReplaceAll[AMP2down2, {\[Sigma] -> \[Gamma]}];


Mdown = processedAmplitudes[[1]] + processedAmplitudes[[3]];
Mdown//Simplify;

MDOWN = ReplaceGammaIndicesInSpinorChain[Mdown - t2/(t1-t2)*AMP2down3, {k0, pa}, \[Chi]]//FullSimplify;

Mdowntless = ReplaceAll[MDOWN, {SUNTF[List[\[Alpha]],c,a] -> 1, 
SUNTF[List[SUNIndex[\[Alpha]]],SUNFIndex[c],SUNFIndex[a]]-> 1}];(*This is to eliminate the common T*)

Mdownsimplified = FactorSpinorChain[Mdowntless ,k2, pb]//FullSimplify;
Print["M_down = ", Mdownsimplified ];


(* ::Subsection:: *)
(*Now we want to obtain the effective vertex, which will be applied to the MRK limit*)


(*Change of momenta and simplification to obtain the effective vertex*)
MUPfermioneless = removeFermionBilinear[Mupsimplified, k2, pb, \[Chi]1];
MDOWNfermioneless = removeFermionBilinear[Mdownsimplified, k0, pa, \[Chi]1];
    
MUPpolaless = removePolarization[MUPfermioneless, k1, \[Tau]];
MDOWNpolaless = removePolarization[MDOWNfermioneless, k1, \[Tau]];

Mupsimple = (removeOuterSpinors[MUPpolaless, k0, pa]/.SP[Plus[Times[-1,k0],pa],Plus[Times[-1,k0],pa]] -> t 
/.SP[Plus[k2,Times[-1,pb]],Plus[k2,Times[-1,pb]]] -> Subscript[t,2]);
Mdownsimple = (removeOuterSpinors[MDOWNpolaless, k2, pb]/.SP[Plus[Times[-1,k0],pa],Plus[Times[-1,k0],pa]] -> t 
/.SP[Plus[k2,Times[-1,pb]],Plus[k2,Times[-1,pb]]] -> Subscript[t,2]);

Mupeikonal =  EikonalApprox[Mupsimple]/. Times[2, Momentum[q2, LorentzIndex[\[Tau]]]] -> 
Plus[Momentum[q2, LorentzIndex[\[Tau]]], Momentum[q1, LorentzIndex[\[Tau]]]]
Mdowneikonal =  EikonalApprox[Mdownsimple]/. Times[2, Momentum[q2, LorentzIndex[\[Tau]]]] -> 
Plus[Momentum[q2, LorentzIndex[\[Tau]]], Momentum[q1, LorentzIndex[\[Tau]]]]


MupEikGord = GordonDecom[replaceDotRecursively[PreprocessExpr[Mupeikonal], pa], pa]//SudakovVariables//Contract;
MdownEikGord = GordonDecom[replaceDotRecursively[PreprocessExpr[Mdowneikonal], pb], pb]//SudakovVariables//Contract;

Print["Mup with fixed SP"];
MupfixedSP = ReplaceAll[MupEikGord//ExpandScalarProduct, 
{Pair[Momentum[kperp1],Momentum[pa]] -> 0 , 
Pair[Momentum[kperp2],Momentum[pa]]-> 0 , Pair[Momentum[pa],Momentum[pa]] -> 0 , Pair[Momentum[pb],Momentum[pa]]-> s/2,
Power[Momentum[pa,LorentzIndex[a_]],2] :> 0, 
Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c],
Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[kperp2, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[kperp1, LorentzIndex[b_]], c_] :> 0}]

Print["Mdown with fixed SP"];
MdownfixedSP = ReplaceAll[MdownEikGord//ExpandScalarProduct, 
{Pair[Momentum[kperp1],Momentum[pb]] -> 0 , 
Pair[Momentum[kperp2],Momentum[pb]]-> 0 , Pair[Momentum[pb],Momentum[pb]] -> 0 , Pair[Momentum[pb],Momentum[pa]]-> s/2,
Power[Momentum[pb,LorentzIndex[a_]],2] :> 0, 
Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c],
Times[a_, Momentum[pb, LorentzIndex[b_]], Momentum[kperp2, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[pb, LorentzIndex[b_]], Momentum[kperp1, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[pb, LorentzIndex[b_]], Momentum[Plus[kperp1, kperp2], LorentzIndex[b_]], c_] :> 0}]

yans = SudakovVariables[PreprocessExpr[Mupsimple]]//AutoRenameLorentzIndices//Simplify;


(* ::Subsection:: *)
(*Now we define the MRK limit, with different functions, and the final result is the correct one*)


OrderList = {
  {},              (* constants \[LongDash] group 0 *)
  {\[Alpha]1, \[Beta]2},        (* group 1 *)
  {\[Alpha]2, \[Beta]1}         (* group 2 *)
};

(*Collect the Lorentz structures in a List*)
MupLorList = CollectLorentzStructures[MupfixedSP//ExpandAll];
MdownLorList = CollectLorentzStructures[MdownfixedSP//ExpandAll];

(*Apply the approximation to each element and them sum them*)
Mupapprox = Total[Finalapprox[#]& /@ MupLorList]//FullSimplify;
Mdownapprox = Total[Finalapprox[#]& /@ MdownLorList]//FullSimplify;


(*I am contracting with the other spinor here, which in the Gordon decomposition gives 2*pb*)
Mupotherspinor = ReplaceAll[Mupapprox*2*Momentum[pb, LorentzIndex[\[Chi]1]]//Contract, 
{Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c],
Times[a_, Momentum[pb, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[kperp1, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[kperp2, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> 0}]//FullSimplify;

(*For M_down I contract with pa, obviosuly*)
Mdownotherspinor = ReplaceAll[Mdownapprox*2*Momentum[pa, LorentzIndex[\[Chi]1]]//Contract, 
{Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c],
Times[a_, Momentum[pa, LorentzIndex[b_]], Momentum[pa, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[kperp1, LorentzIndex[b_]], Momentum[pa, LorentzIndex[b_]], c_] :> 0,
Times[a_, Momentum[kperp2, LorentzIndex[b_]], Momentum[pa, LorentzIndex[b_]], c_] :> 0}]//FullSimplify;


MdownT = Mdownotherspinor/.(SUNTF[List[SUNIndex[\[Alpha]]], SUNFIndex[c], SUNFIndex[a]] 
*SUNTF[List[SUNIndex[\[Gamma]]], SUNFIndex[d], SUNFIndex[b]]-> -SUNTF[List[SUNIndex[\[Gamma]]], SUNFIndex[c], SUNFIndex[a]] 
*SUNTF[List[SUNIndex[\[Alpha]]], SUNFIndex[d], SUNFIndex[b]])//Simplify;

Mupfinal = (Mupotherspinor*Momentum[pa, LorentzIndex[\[Chi]1]]*Momentum[pb, LorentzIndex[\[Chi]1]]*2/s
/.\[Alpha]2 -> -Subscript[t,2]/s /. \[Beta]1 -> Subscript[t,1]/s);
Print["Effective vertex for M_up:", Mupfinal];

Mdownfinal = (MdownT*Momentum[pa, LorentzIndex[\[Chi]1]]*Momentum[pb, LorentzIndex[\[Chi]1]]*2/s
/.\[Alpha]2 -> -Subscript[t,2]/s /. \[Beta]1 -> Subscript[t,1]/s)//Simplify;
Print["Effective vertex for M_down:", Mdownfinal];
Mdownfinal3 = Mdownfinal * SUNTF[List[SUNIndex[\[Alpha]]],SUNFIndex[c],SUNFIndex[a]] /. \[Alpha] -> \[Sigma];
Mdownfinal2 = Mdownfinal3 /. \[Gamma] -> \[Alpha];
Mdownfinal0 = Mdownfinal2 /. \[Sigma] -> \[Gamma];
Mupfinal0 = Mupfinal*SUNTF[List[SUNIndex[\[Alpha]]],SUNFIndex[d],SUNFIndex[b]];

EffectiveVertex = Mdownfinal0 +  Mupfinal0//Simplify


(* ::Section:: *)
(*Check the final results*)


knownResults = {
	-I*\!\(TraditionalForm\`Power[SMP["\<g_s\>"], 3]\)*Pair[LorentzIndex[\[Mu]], LorentzIndex[\[Sigma]]]*((\[Alpha]1 - 2*Subscript[t,1]/(s*\[Beta]2))
	*Momentum[pa,LorentzIndex[\[Tau]]] + (\[Beta]2 - 2*Subscript[t,2]/(s*\[Alpha]1))*Momentum[pb,LorentzIndex[\[Tau]]]
	- Momentum[Plus[kperp1,kperp2],LorentzIndex[\[Tau]]])*4*Momentum[pa,LorentzIndex[\[Mu]]]*Momentum[pb,LorentzIndex[\[Sigma]]]
	*SUNTF[List[SUNIndex[\[Gamma]]],SUNFIndex[c],SUNFIndex[a]]*SUNTF[List[SUNIndex[\[Alpha]]],SUNFIndex[d],SUNFIndex[b]]
	*SUNF[SUNIndex[\[Gamma]],SUNIndex[\[Beta]],SUNIndex[\[Alpha]]]/(Subscript[t,1]* Subscript[t,2])
};
knownResults2 = ReplaceAll[knownResults[[1]]//Contract, {Times[a_, Momentum[pa, LorentzIndex[b_]], 
Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c]}];
EffectiveVertex2 = ReplaceAll[EffectiveVertex, {Times[a_, Momentum[pa, LorentzIndex[b_]], 
Momentum[pb, LorentzIndex[b_]], c_] :> Times[a, s/2, c]}];
Print[knownResults];
FCCompareResults[{EffectiveVertex2},{knownResults2},
Text->{"\tCompare to Agust\[IAcute]n, Sabio, Eduardo Verna, M.A V\[AAcute]zquez, in the paper Graviton Emission in EH gravity, \
Table 7.1:","CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic},Factoring->
Function[x,Simplify[TrickMandelstam[x,{s,t,u,0}]]]]
Print["\tCPU Time used: ", Round[N[TimeUsed[],3],0.001], " s."];



