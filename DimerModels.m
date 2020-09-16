(* ::Package:: *)

BeginPackage[ "DimerModels`"];
Needs["ComputationalGeometry`"];


HalfGraphGenus::usage = "HalfGraphGenus[ graph] returns the genus of the surface in which the graph is canonically embedded.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

TwistHalfGraph::usage = "TwistHalfGraph[ graph] returns the twisted half graph.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

InvoluteHalfGraph::usage = "InvoluteHalfGraph[ graph] returns the half graph with the same underlying graph as the input, but which is embedded in the involuted surface.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

IsomorphicHalfGraphsQ::usage = "IsomorphicHalfGraphsQ[ graph1, graph2] tests if there is an isomorphism between the two half-graphs.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

HalfGraphIsomorphismClasses::usage = "HalfGraphIsomorphismClasses[ list] partitions a list of half-graphs into isomorphism classes.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

ToGraph::usage = "ToGraph[ graph] returns the underlying graph of the half-graph.
N.B., the input should be given in half-graph notation: graph = (\[Sigma], \[Tau]), where \[Sigma] and \[Tau] are permutaions of a set of half-edges."

Dimers::usage = "Dimers[ A] returns the list of all minimally consisten dimer models whose characteristic polygon is the conves hull of the columns of the (integer) matrix A."


Begin["Private`"];


PolygonEdges[A_] := Module[{SplitVector, OrderedBoundaryPoints, BoundaryVectors},
	SplitVector[v_] := Module[{n = GCD @@ v}, ConstantArray[v/n, n]];
	OrderedBoundaryPoints = A[[ ConvexHull[A] ]];
	BoundaryVectors = Append[OrderedBoundaryPoints, First[OrderedBoundaryPoints]] // Differences;
	Flatten[ SplitVector/@(BoundaryVectors), 1] // Return;
];


PolygonGenus[A_] := Module[{OrderedBoundaryPoints, area, edges, boundary},
	(* Determined using Pick's formula. *)
	OrderedBoundaryPoints = A[[ ConvexHull[A] ]];
	area = OrderedBoundaryPoints // Polygon // Area;
	edges = Append[OrderedBoundaryPoints, First[OrderedBoundaryPoints]] // Differences;
	boundary = ( (GCD@@#) &/@ edges ) // Total;
	1 + area  - boundary/2 // Return;
];


MultiSubsets[list_, integer_] := Module[{k, Extensions, CompleteList, multisubsets},

	Extensions[multisubset_, element_] := Module[ {difference},
		difference = integer - Length[multisubset];
		Return[ Join[multisubset, ConstantArray[element, #]]&  /@  Range[0, difference] ];
	];
	
	CompleteList[multisubset_, element_] := Module[ {difference},
		difference = integer - Length[multisubset];
		Return[Join[multisubset, ConstantArray[element, difference]]];
	];
	
	multisubsets = ConstantArray[First[list], #] & /@ Range[0, integer];  
	k = 2;
	While[ k <  Length[list],
		multisubsets = Flatten[Extensions[#, list[[k]]]& /@ multisubsets, 1];
		k = k + 1;
	];
	Return[CompleteList[#, Last[list]] & /@ multisubsets ];
];


PermutationRules[list_] := Thread[list -> #]&  /@  Permutations[list];


RearrangeCycle[cycle_, element_] := Module[{position},
	position = Position[cycle, element] // First // First;
	Join[ Drop[cycle, position],  cycle[[1;;position]] ] // Return;   
];


LexiographicSuccessor[list_, maximums_] := Module[{length, difference, index, rules},

	LexiographicSuccessor::length = "The two lists are not equal in length.";
	LexiographicSuccessor::maxumum = "The list `1` is larger than `2` in at least one component.";
	LexiographicSuccessor::equal = "The list `1` has no successor smaller or equal to `2`.";           

	length = Length[list];
	If[ Length[maximums] != length, Message[LexiographicSuccessor::length]; Return[$Failed];];
	difference = maximums - list;
	If[ Min[difference] < 0, Message[LexiographicSuccessor::maxumum, list, maximums]; Return[$Failed];];
	If[ Max[difference] == 0, Message[LexiographicSuccessor::equal, list, maximums]; Return[$Failed];];
	index = Position[ Sign /@ difference,  1]  // Flatten // Max;
	rules = Append[Thread[Range[index + 1, length] -> 1], index -> list[[index]] + 1];
	ReplacePart[list, rules] // Return;
];


HalfGraphGenus[graph_]:=Module[{halfEdgesSet, rules, faces, genus},
	faces = (PermutationProduct@@(Cycles/@graph)) // First // Length;
	Return[(2-faces-Length[Last[graph]]+Length[First[graph]]) / 2 ];
];


TwistHalfGraph[graph_] := Module[{FlipOneNode},
	FlipOneNode[list_] := If[OddQ[First[list]], Return[Reverse[list]], Return[list]];
	Return[{First[graph], FlipOneNode/@Last[graph]}];
];


InvoluteHalfGraph[graph_] := Module[{k, white, black},
	Return[{First[graph], Reverse /@ Last[graph] }];
];


IsomorphicHalfGraphsQ[graph1_, graph2_] := Module[
	{K, edges, vertices1, vertices2, IsomorphismQ, ConsistentVertexDegreesQ, 
	ConsistentRulesQ, RulesInducedFromVertices, RulesInducedFromEdges, PossibleRules, m},
	
	IsomorphicHalfGraphsQ::input = "Edges of at least one input is not in the expected format: {{1,2},{3,4},...,{2K-1,2K}}.";
	
	(* STEP 1. INITIATION AND TYPE HANDLING *)K = Length[First[graph1]];If[ Length[First[graph1]] != K, Return[False]; ];
	edges = Table[{2k-1, 2k}, {k,1,K}];
	If[First[graph1] != edges || First[graph2] != edges,
		Message[IsomorphicHalfGraphsQ::input]; 
		Return[$Failed];
	];
    vertices1 = Last[graph1];
    vertices2 = Last[graph2];
    If[Sort[Length /@ vertices1] != Sort[Length/@vertices2],  Return[False];];

	(* INTERMEZZO: LOCAL FUNCTIONS *)
	IsomorphismQ[rules_] := Module[{rearrangedvertices1, rearrangedvertices2},
		rearrangedvertices1 = Sort[RearrangeCycle[#, Min[#]] &/@  vertices1,         First[#1] < First[#2] &];
		rearrangedvertices2 = Sort[RearrangeCycle[#, Min[#]] &/@ (vertices2/.rules), First[#1] < First[#2] &];
		Return[rearrangedvertices1 == rearrangedvertices2]
	];
	
    ConsistentVertexDegreesQ[rules_]:= Module[{CheckIndividualRule},
		CheckIndividualRule[rule_] := Module[{degree1, degree2},
			degree1 = Select[vertices1, MemberQ[#, Last[rule] ]& ] // First // Length ;
			degree2 = Select[vertices2, MemberQ[#, First[rule]]& ] // First // Length ;
			Return[degree1 == degree2];
		];
        AllTrue[rules, CheckIndividualRule] // Return;
	];

    ConsistentRulesQ[rules_] := Module[{counts},
		counts = Last /@  Join[  Tally[First /@ rules], Tally[Last /@ rules]  ];
		Return[Max[counts] == 1];
    ];

    RulesInducedFromVertices[rules_]:= Module[{RulesInducedFromOneRule},
		RulesInducedFromOneRule[rule_] := Module[{cycle1, cycle2},
			cycle1 = RearrangeCycle[  Select[vertices1, MemberQ[#, Last[rule] ]& ] // First,  Last[rule] ];
			cycle2 = RearrangeCycle[  Select[vertices2, MemberQ[#, First[rule]]& ] // First,  First[rule]];
			Thread[cycle2 -> cycle1] // Return ;
        ];
        RulesInducedFromOneRule /@ rules  // Flatten // DeleteDuplicates // Return ;
	];

	RulesInducedFromEdges[rules_]:=Module[{Interchange, sourcelabels, targetlabels},
        Interchange[n_] := If[ OddQ[n],  n + 1,  n - 1 ];
        sourcelabels = Interchange /@ (First /@ rules);
        targetlabels = Interchange /@ (Last  /@ rules);
        Join[rules, Thread[sourcelabels -> targetlabels]]  //  DeleteDuplicates  // Return ;
    ];

	(* PART 2: SEARCH FOR AN ISOMORPHISM *)
	(* Testing all possible relabelling unnecessary too expensive; if we guess the new label of one half-edge, 
	   then the labels of all other half-edges are determined by connectedness of the two graphs.  *)
    PossibleRules  = Table[ {1 -> k}, {k, 1, 2K} ];
    PossibleRules  = Select[PossibleRules, ConsistentVertexDegreesQ];    
    m = 0; (* Count the number of iterations for good measure *)
    While[ PossibleRules != {}   &&   m < 4K,
        If[MemberQ[IsomorphismQ /@ PossibleRules, True], Return[True]; ];
        PossibleRules  = RulesInducedFromVertices /@ PossibleRules;
        PossibleRules  = RulesInducedFromEdges    /@ PossibleRules;
        PossibleRules  = Select[PossibleRules, ConsistentRulesQ];
        PossibleRules  = Select[PossibleRules, ConsistentVertexDegreesQ];
        m = m + 1;
    ];
    If[PossibleRules == {}, Return[False], Return[$Failed]];
];


HalfGraphIsomorphismClasses[GraphList_] := Gather[ Range[Length[GraphList]],  IsomorphicHalfGraphsQ[GraphList[[#1]], GraphList[[#2]]]& ];


ToGraph[graph_] := Module[{halfEdgesSet, rules, faces, genus},
	edges = First[graph];
	vertices = Last[graph];
	TranslateOneEdge[edge_] := UndirectedEdge[ Position[vertices, First[edge]] // First // First,  Position[vertices, Last [edge]] // First // First  ];
	Return[TranslateOneEdge /@ edges];
];


EdgeGroupsAndFaceSets[A_] := Module[
	{dualvertices, circumference, pairsofindices, determinants, halfedges,
	SetToCharacteristicList, ConsistentOrientationQ, caracteristiclists,
	PartitionsUpToCoordinate, partitions, k, detsums, halfedgesbygroup, 
	TranslatePartition, SortCycle, SortCycles},
	
	(* STEP 1:  INITIATION  *)
    (* Retrieve the primitive facet vectors of the boundary of the Newton polytope and count them. *) 
    (* Recall that each primitive facet vector corresponds to a vertex of the flipped dimer model; we call them dual vertices. *)
    dualvertices   = PolygonEdges[A];
    circumference  = Length[dualvertices];
    pairsofindices = Subsets[Range[circumference], {2}];
    determinants   = Det[ dualvertices[[#]] ]&  /@  pairsofindices;
    pairsofindices = MapAt[ Reverse,  pairsofindices,   Position[Sign /@ determinants, -1]  ];
    determinants   = Abs /@ determinants;
    halfedges      = Flatten[ (ConstantArray @@\[NonBreakingSpace]#)& /@ Thread[{pairsofindices, determinants}], 1];  
  
  (* STEP 2:  CONSTRUCT A LIST OF ALL CLOSED SUBCYCLES OF WINDING NUMBER ONE OF THE CHARACTERISTIC CYCLE *)
    SetToCharacteristicList[halfedges_] := Module[{dilations},
        dilations = Sort /@ Thread[{halfedges, RotateLeft[halfedges]}];
        Return[ If[ MemberQ[dilations, Sort[#]], 1, 0] & /@ pairsofindices ]    
    ];
  
    ConsistentOrientationQ[characteristiclist_] := Module[{appearingedges},
        appearingedges = pairsofindices[[#]]& /@ Flatten[Position[characteristiclist, 1]];
        Return[ Sort[ First /@ appearingedges ] == Sort[ Last /@ appearingedges ] ];
    ];

    caracteristiclists = SetToCharacteristicList  /@  Subsets[Range[circumference], {3, circumference}];
    caracteristiclists = Select[caracteristiclists, ConsistentOrientationQ];
    
	(* STEP 3:  CONSTRUCT A LIST OF ALL PARTITIONS OF THE CHARACTERISTIC CYCLE INTO CYCLES OF WINDING NUMBER ONE  *)

    PartitionsUpToCoordinate[cycleList_, index_] := Module[{difference, admissible, multisubsets},
		(* Compute the difference of the sum of the cycles and the dets vector at position index.
		   If the numbers agree, then the trivial extension is the only extensions. *)
        difference = (determinants - Total[cycleList])[[index]];
        If[difference == 0, Return[{cycleList}]];
        admissible = Select[ caracteristiclists,   FirstPosition[#, 1] == {index}  & ];
        If[Length[admissible] == 0, Return[{}]];
        multisubsets = MultiSubsets[admissible, difference];
        Join[cycleList, #]& /@ multisubsets  //  Return;
    ];

    partitions = {{}}; 
    k = 1;
    While[k <= Length[determinants],
        partitions = Flatten[  PartitionsUpToCoordinate[#, k]&  /@  partitions,  1];
        partitions = Select[partitions,   Min[determinants - Total[#]] >= 0  &] // DeleteDuplicates;
        k = k + 1;
    ];
     
    partitions = Select[partitions, Total[#] == determinants &]; 

	(* STEP 4:  RELABEL THE RESULT. *)
    detsums = Total[determinants[[1 ;; #]]]& /@ Range[0, Length[determinants]];
    halfedgesbygroup = Table[Range[detsums[[k]] + 1, detsums[[k+1]]], {k, 1, Length[determinants]}];
    
    TranslatePartition[partition_] := Module[{RemainingIndices, HalfEdgeCycles, RemainingParts, positions},
        RemainingParts    = partition;
        RemainingIndices  = halfedgesbygroup;
        HalfEdgeCycles    = {};
        While[Length[RemainingParts] > 0,
            positions = Flatten[ Position[ First[RemainingParts], 1] ];
            HalfEdgeCycles = Append[ HalfEdgeCycles,  First /@ RemainingIndices[[positions]] ];
            RemainingIndices = Delete[RemainingIndices, {#, 1} & /@ positions];
            RemainingParts   = Drop[ RemainingParts, 1]; 
        ];
        Return[HalfEdgeCycles];
   ];
  
   partitions = TranslatePartition /@ partitions;  

  (* STEP 5:  SORT THE PARTITIONS. *)
    SortCycle[cycle_] := Module[{NextIndex, answer},
        NextIndex[index_] := Select[cycle, First[halfedges[[#]]] == Last[halfedges[[index]]] & ]  //  First;
        answer = {First[cycle]};
        While[Length[answer] < Length[cycle],
            answer = Append[answer, NextIndex[Last[answer]]];
        ];
        answer // Return;
    ];

    SortCycles[list_] := SortCycle /@ list;

    (* RETURN *)
    Return[{halfedgesbygroup, SortCycles /@ partitions}]
];


GraphsWithPrescribedGenera[white_, black_, genus_] := Module[{K, edges, graphlist},
    K = white // First // Flatten // Length;
	edges = Table[ {2k - 1, 2k}, {k, 1, K} ];
    graphlist = Flatten[ Table[ {edges, Join[w, b]}, {w, white}, {b, black}], 1];
    graphlist = Select[graphlist, HalfGraphGenus[#] == genus && HalfGraphGenus[TwistHalfGraph[#]] == 1 &];
    Return[ graphlist ];
];


Options[Dimers] = 
	{
	 "Output"         -> False,
	 "FindOne"        -> False,
	 "StartAt"        -> 1,
	 "StopAt"         -> 0
	};
	
Dimers[A_, OptionsPattern[]] := Module[
    {genus, groupededges, vertexsets, adjustedgroupededges, permutations, multiplicities, edges,
    reversedvertexsets, white, black, graphlist, indexvector, rules, currentposition},
    (* Compute the genus of the associated Riemann surface *)
    genus =  PolygonGenus[A];
    (* Retrieve the EdgeGroups and the FaceSets *)
    {groupededges, vertexsets} = EdgeGroupsAndFaceSets[A];  
    If[OptionValue["Output"],  Print["Number of possible vertex sets is ", Length[vertexsets], "."]];
    (* Retrieve the list of permutations of half-edges associated to the same pairs of edges. *)
    permutations   = PermutationRules /@ Select[groupededges, Length[#] > 1 &];
    multiplicities = Length /@ permutations;
	(* Create the list of edges of the dimer model *)
	edges = Table[ {2k - 1, 2k}, {k, 1, Length[Flatten[groupededges]]} ];
    (* Consider two separate cases: whether there are permutations to take into account or not. *)
    If[ Length[multiplicities] == 0, 
        If[ OptionValue["Output"],  Print["Total number of graphs is ", Length[vertexsets]^2, "."];];
        reversedvertexsets = (Reverse /@ # &) /@ vertexsets;
        white = (2# - 1 &  /@ #)&  /@  vertexsets;
        black = (2#     &  /@ #)&  /@  reversedvertexsets;
        graphlist = GraphsWithPrescribedGenera[white, black, genus];
        If[OptionValue["FindOne"], Return[ First[graphlist] ] ];
        graphlist = graphlist[[  First /@ HalfGraphIsomorphismClasses[graphlist] ]];,
  (* ElseIf *)
        If[ OptionValue["Output"], Print["Total number of permutations is ", Times@@multiplicities, "."];];    
        (* Loop through all permutations *)
        indexvector = Append[ConstantArray[1, Length[multiplicities] - 1], 0] ;
        graphlist = {};
        currentposition = 1;
        While[ currentposition < OptionValue["StartAt"],
             indexvector     = LexiographicSuccessor[indexvector, multiplicities];      
             currentposition = currentposition + 1;
        ];    
        While[Total[indexvector] < Total[multiplicities],
            indexvector = LexiographicSuccessor[indexvector, multiplicities];
            rules       = permutations[[ #, indexvector[[#]] ]]&  /@  Range[Length[indexvector]]  // Flatten;
            reversedvertexsets = (Reverse /@ # &) /@ (vertexsets /. rules);
            white = (2# - 1 &  /@ #)&  /@  vertexsets;
            black = (2#     &  /@ #)&  /@  reversedvertexsets;
            graphlist = Join[graphlist, GraphsWithPrescribedGenera[white, black, genus ]];
            graphlist = graphlist[[  First /@ HalfGraphIsomorphismClasses[graphlist] ]];      
            If[ OptionValue["FindOne"] && (Length[graphlist] > 0), Return[ First[graphlist] ] ];
            If[ currentposition == OptionValue["StopAt"], Return[graphlist] ];
            currentposition = currentposition + 1;
        ];
    ];
    Return[graphlist];
];


End[];
EndPackage[];



