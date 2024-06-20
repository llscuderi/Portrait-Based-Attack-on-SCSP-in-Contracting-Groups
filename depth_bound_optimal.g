LoadPackage("automgrp");
filename := "/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/test_depth_bound.g";

# Helper functions

# Find maximum length of elements in the nucleus
NucleusMaxLength := function(G)
        local nucleus, element_lengths, M;
        nucleus:=FindNucleus(G)[1];
	AppendTo(filename, "Size of Nucleus: ", Size(nucleus), "\n");
        element_lengths:=List(nucleus, x -> Length(Word(x)));
        M:=Maximum(element_lengths);

        return M;
end;

# Finds maximum level at which elements of length <= len contract to nucleus
MaxContractingDepth := function(G, len)
        local level, elements, elem_depths;

	AG_UseRewritingSystem(G);
        AG_UpdateRewritingSystem(G, 4);

        elements := ListOfElements(G, len);
        elem_depths := List(elements, x -> AutomPortraitDepth(x));
        level := Maximum(elem_depths);
        return level;
end;

# List of contracting groups

Grigorchuk := AG_Groups.GrigorchukGroup;

Basilica := AG_Groups.Basilica;

Autom748 := AutomatonGroup("a=(a,a)(1,2), b=(c,a), c=(a,a)");

Autom775 := AutomatonGroup("a=(a,a)(1,2), b=(c,b), c=(a,a)");

Autom2277 := AutomatonGroup("a=(c,c)(1,2), b=(a,a)(1,2), c=(b,a)"); 

Autom2287 := AutomatonGroup("a=(a,a)(1,2), b=(c,a)(1,2), c=(b,a)");

Autom2853 := AutomatonGroup("a=(c,c)(1,2), b=(b,a)(1,2), c=(c,c)");

CGroups := [[Grigorchuk, "Grigorchuk"], [Basilica, "Basilica"],
		 [Autom748, "Autom748"], [Autom775, "Autom775"], 
		  [Autom2277, "Autom2277"], [Autom2287, "Autom2287"], 
			[Autom2853, "Autom2853"]];

# 
MinimizeMaxDepth := function(G)
        local k, min, ratio, min_k, M, Nk;
	
        M := NucleusMaxLength(G);
	AppendTo(filename, "Max length of element in nucleus: ", M, "\n");

        # Warning: This takes a long time
        for k in [2..5] do
		Nk := MaxContractingDepth(G, k*M);
                ratio := Float(Nk)/Log2(Float(k));
                AppendTo(filename, "k = ", k, ", Nk = ", Nk, ", ratio = ", ratio, "\n");

		if k = 2 then
			min := ratio;
			min_k := k;
		fi;
 
                if ratio < min then
                        min := ratio;
                        min_k := k;
                fi;
        od;

        return min_k;
end;	

for group in CGroups do
	AppendTo(filename, "Group: ", group[2], "\n");
	min := MinimizeMaxDepth(group[1]);
	AppendTo(filename, "Best k: ", min, "\n");
	AppendTo(filename, "\n");
od;





 
