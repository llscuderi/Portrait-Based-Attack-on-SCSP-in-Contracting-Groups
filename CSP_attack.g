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

# Finds maximum level at which elements of length <= len contract to nucleus
MaxContractingDepth := function(G, len)
	local level, elements, elem_depths;
	elements := ListOfElements(G, len);
	elem_depths := List(elements, x -> AutomPortraitDepth(x));
	level := Maximum(elem_depths);
	return level;
end;
	
# Computes upper bound for portrait depth for an element in group G of length n
# uses max level at which elements of length <= k*M contract
PortraitDepthUpperBound := function(G, n, k)
	local M, N, a, len;

	# Question: if we use rewriting system and pass G to another function,
	# Does the rewriting hold? 
	AG_UseRewritingSystem(G);
	AG_UpdateRewritingSystem(G, 4);

	M := NucleusMaxLength(G);
	N := MaxContractingDepth(G, k*M);

	if n <= k*M then
		return N;
	fi;

	a := LogInt(n, k) + 1;
	len := Int(Ceil( Float( (k/k-1)*M ) ));
	return N*a + MaxContractingDepth( G, len );
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
			

# For group G and fixed n, returns k between 2 and 4 for which
# MaxPortraitDepth( G, n, k) is minimized 
# Want to minimize N_k/(log_2(k)) (this is for large n)
MinimizeMaxDepth := function(G)
	local k, min, ratio, min_k, M, logn;
		
	M := NucleusMaxLength(G);
	min := Float(MaxContractingDepth(G, 2*M)); 
	min_k := 2;
	Print("k = ", min_k, ", ratio = ", min, "\n");
	
	# Warning: This takes a long time	
	for k in [3..4] do
		ratio := Float(MaxContractingDepth(G, k*M))/Log2(Float(k));
		Print("k = ", k, ", ratio = ", ratio, "\n");
		if ratio < min then
			min := ratio;
			min_k := k;
		fi;
	od;
		
	return min_k;
end;

# TODO: Some functions that decide what depth we need, possibly by using previous calculations	

# ------------------------------------------------------
# ------- Functions for recovering conjugator ----------
# ------------------------------------------------------


ComputePermGroups:=function(G,l)
	local PermGroups, i;
	PermGroups:=[];

	for i in [1..l] do
		Add(PermGroups, PermGroupOnLevel(G,i));
	od;
	return PermGroups;
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

# ------------------------------------------------------------------------------------
												
ConjugatorPortrait:=function( g_list, h_list, key_length )
	local G, Nucleus, placeholder, portrait, contracting_depth, PermGroups, AreNotConjugate, ConjugatorEvenFirstLevel, 
		NucleusDistinctLevel, nucleus_distinct_level, N_perms, N_masks, NucleusElementByPortrait, MaskToNucleusElement,
			ConjugatorPortraitRecursive, i, odd_g_idxs, gh_extended ;
	
	G:= GroupOfAutomFamily( FamilyObj( g_list[1] ) );
	Nucleus := FindNucleus(G)[1];

	placeholder := g_list[1];

	# We precompute this list because it takes a while 
	PermGroups := ComputePermGroups( G, 10 );
	
	contracting_depth := PortraitDepthUpperBound(G, key_length, 2);

	AreNotConjugate:=function(a,b)
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
	ConjugatorEvenFirstLevel:=function(g,h)
		local g0, g1, h0, h1;
		g0 := Section(g,1);
		g1 := Section(g,2);
				
		h0 := Section(h,1);
		h1 := Section(h,2);

		# Case 1: if the following aren't conjugate, r isn't even
		if AreNotConjugate(g0,h0) or AreNotConjugate(g1,h1) then
			return false;

		# Case 2: if the following aren't conjugate, r is even
		elif AreNotConjugate(g0,h1) or AreNotConjugate(g1,h0) then
			return true;
		else
			return fail;
		fi;	
	end;

	# Finds the level at which all elements of the nucleus differ in permutation
	NucleusDistinctLevel := function(G)
		local lev, L;

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

	nucleus_distinct_level := NucleusDistinctLevel(G);
	N_perms := List(Nucleus, x -> PermOnLevel(x, nucleus_distinct_level));

	Print("N_perms:" , N_perms, "\n");

	N_masks := List(Nucleus, x -> mask_function(x,1)); 

	# If a nested portrait is certainly in the nucleus, identify it by permutation
	NucleusElementByPortrait := function( port )
	
		Print("Portrait passed to NEBP:", port, "\n");
		Print("Permutation:", PermutationOfNestedPortrait(port, nucleus_distinct_level), "\n"); 
	
		for i in [1..Size(Nucleus)] do
			if PermutationOfNestedPortrait(port, nucleus_distinct_level) = N_perms[i] then
				return Nucleus[i];
			fi;
		od;
		
		# This should never happen if we do everything right
		# TODO: it does, in fact, happen
		return fail;
	end;

	# function to take mask of depth 1 ([[word, word], perm]) 
	# and if it is in the nucleus, return element of nucleus
	MaskToNucleusElement := function( mask )
		
		for i in Size(Nucleus) do
			if mask = N_masks[i] then 
				return Nucleus[i];
			fi;
		od;

		return fail;
	end;
	
	# Recursively builds portrait of conjugator from lists of conjugate pairs
	# Returns list [portrait, depth] since we need depth for PortraitToMask
	# TODO (eventually): Refactor for less repeat code 
	ConjugatorPortraitRecursive :=function( g_list, h_list, lev)
	
		local i, ConjEven, g_list_r0, h_list_r0, g_list_r1, h_list_r1, r0, r1,
			r0_portrait, r1_portrait, r0_mask, r1_mask, odd_g, odd_h, r0_TA, r1_TA, 
			g0_TA, g1_TA, h0_TA, portrait_depth, nucleus_element;
		
		for i in [1..Size(g_list)] do
			# if g_i is even (note that g_list is only extended with even elements, so odd_g_idxs need not be updated)
			if not i in odd_g_idxs then
				ConjEven := ConjugatorEvenFirstLevel(g_list[i], h_list[i] );
				
				if not ConjEven = fail then
					# ------------------------------------ If r is even -------------------------------------
					if ConjEven then 
	
						# If we're as deep as we need, return portrait with placeholders
						# Possible source of error - pretty sure that perm we add on contracting_depth
						# counts toward nucleus_distinct_level
						if lev = contracting_depth + nucleus_distinct_level then
							return [[(), [placeholder], [placeholder]], 1];
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
						r0 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev+1);

	
						if not (r0 = fail or Size(odd_g_idxs) = 0) then
							
							# If we can recover r1 from r0 (r1 = g0^-1*r0*h0)
							
							r0_portrait := r0[1];
							portrait_depth := r0[2];
	
							odd_g := g_list[odd_g_idxs[1]];
							odd_h := h_list[odd_g_idxs[1]];

							# If r0_portrait is a nested list (as opposed to one word),
							# make it into a TreeAutomorphism
							if Size(r0_portrait) > 1 then
								r0_mask := PortraitToMask(r0_portrait, portrait_depth );
								r0_TA := TreeAutomorphism(r0_mask[1], r0_mask[2]);

								g0_TA := Decompose(Section(odd_g, 1), portrait_depth );
								h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
								r1_TA := g0_TA^-1 * r0_TA * h0_TA;
								
								r1_mask := mask_function(r1_TA, 1);
								r1_portrait := MaskToPortrait(r1_mask, portrait_depth );
							else 
								r1_portrait := [Section(odd_g,1)^-1 * r0_portrait[1] * Section(odd_h,1)];
							fi;
								
						elif (r0 = fail and not Size(odd_g_idxs) = 0) or (not r0 = fail and Size(odd_g_idxs) = 0) then
		
							# If can't recover r1 from r0, or we need to recover r0 from r1
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
							r1 := ConjugatorPortraitRecursive( g_list_r1, h_list_r1, lev+1);
							
							if r1 = fail then
								return fail;
							elif not r0 = fail then
								r0_portrait := r0[1];
								r1_portrait := r1[1];
								
								portrait_depth := Maximum(r0[2], r1[2]);
							else 
								# the only case left is where we recover r0 from r1 (r0 = g0*r1*h0^-1)
								r1_portrait := r1[1];
								portrait_depth := r1[2];
		
								odd_g := g_list[odd_g_idxs[1]];
								odd_h := h_list[odd_g_idxs[1]];

								# If r1_portrait is a nested list (as opposed to one word),
								# make it into a TreeAutomorphism
								if Size(r1_portrait) > 1 then
									r1_mask := PortraitToMask(r1_portrait, portrait_depth);
									r1_TA := TreeAutomorphism(r1_mask[1], r1_mask[2]);

									g0_TA := Decompose(Section(odd_g, 1), portrait_depth);
									h0_TA := Decompose(Section(odd_h, 1), portrait_depth);	
									r0_TA := g0_TA * r1_TA * h0_TA^-1;
									
									r0_mask := mask_function(r0_TA, 1);
									r0_portrait := MaskToPortrait(r1_mask, portrait_depth);
								else 
									r0_portrait := [Section(odd_g,1) * r1_portrait[1] * Section(odd_h,1)^-1];
								fi;
							fi;
								
						else
							# if we don't have r0 and we don't have relations
							return fail; 
						fi;

						

						if lev = contracting_depth then
							# on this level, portraits with placeholders become members of the nucleus
							# WARNING counting may be wrong here, double check
							return [ [ NucleusElementByPortrait([ (), r0_portrait, r1_portrait ]) ], 0 ];
						fi;
							
	
					
						# If both r0/r1 portraits are in the form [word], 
						# check if the portrait we're about to return is an element of the nucleus
						# (Since we return [[word], 0] iff word is in the nucleus)
						#  If it is, return [[word], 0] (this is the self-pruning part)
						if portrait_depth = 0 then
							nucleus_element := MaskToNucleusElement([r0_portrait[1], r1_portrait[1]], ());
							if not nucleus_element = fail then
								return [[nucleus_element], 0];
							fi;
						fi;					
	
						return [ [ (), r0_portrait, r1_portrait ], portrait_depth + 1 ];
	
					# ------------------------------------ If r is odd ------------------------------------------
					else 
						# If we're as deep as we need, return portrait with placeholders 
						# Possible source of error - pretty sure that perm we add on contracting_depth
						# counts toward nucleus_distinct_level
						if lev = contracting_depth + nucleus_distinct_level then
							return [[(1,2), [placeholder], [placeholder]], 1];
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
						r0 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev+1);

						if not (r0 = fail or Size(odd_g_idxs) = 0) then
							
							# If we can recover r1 from r0 (r1 = g1*r0*h0^-1)
							
							r0_portrait := r0[1];
							portrait_depth := r0[2];
	
							odd_g := g_list[odd_g_idxs[1]];
							odd_h := h_list[odd_g_idxs[1]];

							# If r0_portrait is a nested list (as opposed to one word),
							# make it into a TreeAutomorphism
							if Size(r0_portrait) > 1 then
								r0_mask := PortraitToMask(r0_portrait, portrait_depth );
								r0_TA := TreeAutomorphism(r0_mask[1], r0_mask[2]);

								g1_TA := Decompose(Section(odd_g, 2), portrait_depth );
								h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
								r1_TA := g1_TA * r0_TA * h0_TA^-1;
								
								r1_mask := mask_function(r1_TA, 1);
								r1_portrait := MaskToPortrait(r1_mask, portrait_depth );
							else 
								r1_portrait := [Section(odd_g,2) * r0_portrait[1] * Section(odd_h,1)^-1];
							fi;
								
						elif (r0 = fail and not Size(odd_g_idxs) = 0) or (not r0 = fail and Size(odd_g_idxs) = 0) then
		
							# If can't recover r1 from r0, or we need to recover r0 from r1 
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
							r1 := ConjugatorPortraitRecursive( g_list_r1, h_list_r1, lev+1);

							if r1 = fail then
									return fail;
								elif not r0 = fail then
									r0_portrait := r0[1];
									r1_portrait := r1[1];
									
									portrait_depth := Maximum(r0[2], r1[2]);
								else 
									# the only case left is where we recover r0 from r1 (r0 = g1^-1*r1*h0)
									r1_portrait := r1[1];
									portrait_depth := r1[2];
			
									odd_g := g_list[odd_g_idxs[1]];
									odd_h := h_list[odd_g_idxs[1]];

									# If r0_portrait is a nested list (as opposed to one word),
									# make it into a TreeAutomorphism
									if Size(r1_portrait) > 1 then
										r1_mask := PortraitToMask(r1_portrait, portrait_depth);
										r1_TA := TreeAutomorphism(r1_mask[1], r1_mask[2]);

										g1_TA := Decompose(Section(odd_g, 2), portrait_depth);
										h0_TA := Decompose(Section(odd_h, 1), portrait_depth);	
										r0_TA := g1_TA^-1 * r1_TA * h0_TA;
										
										r0_mask := mask_function(r0_TA, 1);
										r0_portrait := MaskToPortrait(r1_mask, portrait_depth);
									else 
										
										r0_portrait := [Section(odd_g,2)^-1 * r1_portrait[1] * Section(odd_h,1)];
								fi;
							fi;
									
						else
							# if we don't have r0 and we don't have relations
							return fail; 
						fi;

						if lev = contracting_depth then
							# on this level, portraits with placeholders become members of the nucleus
							# WARNING counting may be wrong here, double check
							return [ [ NucleusElementByPortrait([ (1,2), r0_portrait, r1_portrait ]) ], 0 ];
						fi;
							
	
					
						# If both r0/r1 portraits are in the form [word], 
						# check if the portrait we're about to return is an element of the nucleus
						# (Since we return [[word], 0] iff word is in the nucleus)
						#  If it is, return [[word], 0] (this is the self-pruning part)
						if portrait_depth = 0 then
							nucleus_element := MaskToNucleusElement([r0_portrait[1], r1_portrait[1]], (1,2));
							if not nucleus_element = fail then
								return [[nucleus_element], 0];
							fi;
						fi;					
								
						return [ [ (1,2), r0_portrait, r1_portrait ], portrait_depth + 1 ];
					fi;
				else
					# If ConjEven failed 
					if i = Size(g_list) then 
						# If we make it through the whole list (i.e., fail on every g to recover r), return fail
						return fail;
					fi;
				fi;
			else 
				# If g_i is odd
				if i = Size(g_list) then
					# If we make it through the whole list (i.e., fail on every g to recover r), return fail
					return fail;
				fi;
			fi;
		od;	
						
	end;	

	odd_g_idxs := IdxsOfOdds( g_list );
	gh_extended := ExtendLists( g_list, h_list, odd_g_idxs );
	g_list := gh_extended[1];
	h_list := gh_extended[2];

	portrait := ConjugatorPortraitRecursive( g_list, h_list, 1);

	# Returns depth as well for checking accuracy
	return portrait;

end;
