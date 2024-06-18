#Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");

# ----------------------------------------------------------------------------
# ------ Functions for finding depth needed to recover conjugator ------------
# -----------------------------------------------------------------------------


# Find maximum length of elements in the nucleus
NucleusMaxLength := function(G)
	local nucleus, element_lengths, M; 
	nucleus:=FindNucleus(G)[1];
	element_lengths:=List(nucleus, x -> Length(Word(x)));
	M:=Maximum(element_lengths);

	return M;
end;


# Computes maximum level at which elements of length <= 2M contract to nucleus
# Where M is maximum length of elements in the nucleus 
2MDepth := function(G, M)
	local N, L, L_Depths;
	L := ListOfElements(G, 2*M);
	L_Depths := List(L, x -> AutomPortraitDepth(x));
	N := Maximum(L_Depths);
	return N;
end;

# Computes maximum level at which elements of length <= kM contract to nucleus
# Where M is maximum length of elements in the nucleus 
kMDepth := function(G, M, k)
	local N, L, L_Depths;
	L := ListOfElements(G, k*M);
	L_Depths := List(L, x -> AutomPortraitDepth(x));
	N := Maximum(L_Depths);
	return N;
end;
	
# Computes upper bound for portrait depth for an element in group G of length n
# uses max level at which elements of length <= k*M contract
MaxPortraitDepth := function(G, n, k)
	local M, N, a;

	AG_UseRewritingSystem(G);
	AG_UpdateRewritingSystem(G, 4);

	M := NucleusMaxLength(G);
	N := kMDepth(G, M, k);

	if n <= k*M then
		return N;
	fi;

	a := LogInt(n, k) + 1;
	return N*a + 2MDepth(G, M);
end;

# Returns true if list L contains no repeat elements 
NoRepeats := function(L)
	local i, j, no_repeats;

	no_repeats:= true;
	for i in [1..Size(L)-1] do
		for j in [i+1..Size(L)] do
			if L[i] = L[j] then
				# if 2 elements match, all elements do not differ
				no_repeats := false;
				return no_repeats;
			fi;
		od;
	od;
	return no_repeats;
end;
			

# Finds the level at which all elements of the nucleus differ in permutation
NucleusDistinctLevel := function(G)
	local Nucleus, lev, L, N;

	Nucleus := FindNucleus(G)[1];
	lev := 1;
	while true do
		L := List(Nucleus, x -> PermOnLevel(x, lev));
		if NoRepeats(L) then
			return lev;
		else
			lev := lev + 1;
		fi;
	od;
end;

# For group G and fixed n, returns k between 2 and 4 for which
# MaxPortraitDepth( G, n, k) is minimized 
# Want to minimize N_k/(log_2(k)) (this is for large n)
MinimizeMaxDepth := function(G)
	local k, min, ratio, min_k, M, logn;
		
	M := NucleusMaxLength(G);
	min := Float(kMDepth(G, M, 2)); 
	min_k := 2;
	Print("k = ", min_k, ", ratio = ", min, "\n");
	
	for k in [3..4] do
		ratio := Float(kMDepth(G, M, k))/Log2(Float(k));
		Print("k = ", k, ", ratio = ", ratio, "\n");
		if ratio < min then
			min := ratio;
			min_k := k;
		fi;
	od;
		
	return min_k;
end;
			

# ------------------------------------------------------
# ------- Functions for recovering conjugator ----------
# ------------------------------------------------------

# We precompute this list and pass it along with G to our funtctions
ComputePermGroups:=function(G,l)
	local PermGroups, i;
	PermGroups:=[];

	for i in [1..l] do
		Add(PermGroups, PermGroupOnLevel(G,i));
	od;
	return PermGroups;
end;

AreNotConjugate:=function(PermGroups,a,b)
	local l, Glev;
	for l in [1..Size(PermGroups)] do
		Glev:=PermGroups[l]; 
		if not IsConjugate(Glev, PermOnLevel(a,l), PermOnLevel(b,l)) then
			# Return true if NOT conjugate 
			return true; 
		else
			return false;
		fi;
	od;
end;

# We always pass g that's even on the first level
# Returns true if conjugator is even on the first level, false if odd, fail if fail
ConjugatorEvenFirstLevel:=function(PermGroups,g,h)
	local g0, g1, h0, h1;
	g0 := Section(g,1);
	g1 := Section(g,2);
			
	h0 := Section(h,1);
	h1 := Section(h,2);

	# Case 1: if the following aren't conjugate, r isn't even
	if AreNotConjugate(PermGroups,g0,h0) or AreNotConjugate(PermGroups,g1,h1) then
		return false;

	# Case 2: if the following aren't conjugate, r is even
	elif AreNotConjugate(PermGroups,g0,h1) or AreNotConjugate(PermGroups,g1,h0) then
		return true;
	else
		return fail;
	fi;	
end;

# Returns list of indices of elements having perm (1,2) on 1st level
IdxsOfOdds:=function(g_list)
	local odd_idxs, i;
	odd_idxs:=[];
	for i in [1..Size(g_list)] do	
		if PermOnLevel(g_list[i], 1) = (1,2) then
			Add(odd_idxs, i);
		fi;
	od;
	return odd_idxs;
end;
	
# Appends to g_list and h_list multiples of odd elements of the lists
ExtendLists:=function(g_list, h_list, odd_idxs)
	local i, j;
	for i in [1..Size(odd_idxs)-1] do
		for j in [i+1..Size(odd_idxs)] do
			Add(g_list, g_list[odd_idxs[i]]*g_list[odd_idxs[j]]);
			Add(h_list, h_list[odd_idxs[i]]*h_list[odd_idxs[j]]);
		od;
	od;
	return [g_list, h_list];
end;

ConjugatorPortraitRecursive:=function( g_list, h_list, lev, PermGroups )
	
	local i, ConjEven, g_list_r0, h_list_r0, g_list_r1, h_list_r1, r0, r1,
		odd_g_idxs, gh_extended;
	
	odd_g_idxs := IdxsOfOdds( g_list );
	gh_extended := ExtendLists( g_list, h_list, odd_g_idxs );
	g_list := gh_extended[1];
	h_list := gh_extended[2];
	
	for i in [1..Size(g_list)] do
		# if g_i is even (note that g_list is only extended with even elements)
		if not i in odd_g_idxs then
			ConjEven := ConjugatorEvenFirstLevel( PermGroups, g_list[i], h_list[i] );
			
			if not ConjEven = fail then
				# If r is even 
				if ConjEven then 

					# If we're as deep as we want, return portrait with placeholders 
					if lev = 1 then
						return [(), 1, 1];
					fi;	
					
					# Build new lists to recover r0
					g_list_r0 := [];
					h_list_r0 := [];
					for i in [1..Size(g_list)] do
						# If g_i is even on the first level
						if PermOnLevel( g_list[i], 1 ) = () then
							Add( g_list_r0, Section( g_list[i], 1 ) );
							Add( h_list_r0, Section( h_list[i], 1 ) );

						# If g_i is odd on the first level
						else 
							Add( g_list_r0, Section( g_list[i], 1 )*Section( g_list[i], 2) );
							Add( h_list_r0, Section( h_list[i], 1 )*Section( h_list[i], 2) );
						fi;
					od;
					
					# Recursive step: recover portrait of r0
					r0 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev-1, PermGroups );

					# Should be: if not Size(odd_g_idxs) = 0, use odd_g_idxs[1] for relations
					# else build new lists to recover r1
					# For now, we build new lists for testing 
					
					if false then
						# r1 = g0^-1*r0*h0, but we can't multiply portraits yet
					else 
													
						# Build new lists to recover r1
						g_list_r1 := [];
						h_list_r1 := [];
						for i in [1..Size(g_list)] do
							# If g_i is even on the first level
							if PermOnLevel( g_list[i], 1 ) = () then
								Add( g_list_r1, Section( g_list[i], 2 ) );
								Add( h_list_r1, Section( h_list[i], 2 ) );

							# If g_i is odd on the first level
							else 
								Add( g_list_r1, Section( g_list[i], 2 )*Section( g_list[i], 1) );
								Add( h_list_r1, Section( h_list[i], 2 )*Section( h_list[i], 1) );
							fi;
						od;
						
						# Recursive step: recover portrait of r1
						r1 := ConjugatorPortraitRecursive( g_list_r1, h_list_r1, lev-1, PermGroups );
					fi;
					
					return [ (), r0, r1 ];

				# If r is odd
				else 
					# If we're as deep as we want, return portrait with placeholders 
					if lev = 1 then
						return [(1,2), 1, 1];
					fi;	
					
					# Build new lists to recover r0
 					g_list_r0 := [];
					h_list_r0 := [];
					for i in [1..Size(g_list)] do
						# If g_i is even on the first level
						if PermOnLevel( g_list[i], 1 ) = () then
							Add( g_list_r0, Section( g_list[i], 1 ) );
							Add( h_list_r0, Section( h_list[i], 2 ) );

						# If g_i is odd on the first level
						else 
							Add( g_list_r0, Section( g_list[i], 1 )*Section( g_list[i], 2) );
							Add( h_list_r0, Section( h_list[i], 2 )*Section( h_list[i], 1) );
						fi;
					od;

					# Recursive step: recover portrait of r0
					r0 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev-1, PermGroups );

					# Should be: if not Size(odd_g_idxs) = 0, use odd_g_idxs[1] for relations
					# else build new lists to recover r1
					# For now, we build new lists for testing 

					if false then
						# r1 = g0^-1*r0*h0, but we can't multiply portraits yet
					else 
													
						# Build new lists to recover r1
						g_list_r1 := [];
						h_list_r1 := [];
						for i in [1..Size(g_list)] do
							# If g_i is even on the first level
							if PermOnLevel( g_list[i], 1 ) = () then
								Add( g_list_r1, Section( g_list[i], 2 ) );
								Add( h_list_r1, Section( h_list[i], 1 ) );

							# If g_i is odd on the first level
							else 
								Add( g_list_r1, Section( g_list[i], 2 )*Section( g_list[i], 1) );
								Add( h_list_r1, Section( h_list[i], 1 )*Section( h_list[i], 2) );
							fi;
						od;
						
						# Recursive step: recover portrait of r1
						r1 := ConjugatorPortraitRecursive( g_list_r1, h_list_r1, lev-1, PermGroups );
					fi;
					
					return [ (1,2), r0, r1 ];
				fi;
			else
				Print( i, " Failed\n" );
				if i = Size(g_list) then 
					return ["F1"];
				fi;
			fi;
		else 
			Print(i, " Odd\n");
			if i = Size(g_list) then
				return ["F2"];
			fi;
		fi;
	od;	
					
end;	
												
ConjugatorPortrait:=function( g_list, h_list, key_length )
	local G, PermGroups, portrait, depth;
	G:= GroupOfAutomFamily( FamilyObj( g_list[1] ) );
	PermGroups:= ComputePermGroups( G, 10 );

	depth := MaxPortraitDepth(G, key_length, 2) + NucleusDistinctLevel(G);

	portrait := ConjugatorPortraitRecursive( g_list, h_list, depth, PermGroups );

	return portrait;

end;
