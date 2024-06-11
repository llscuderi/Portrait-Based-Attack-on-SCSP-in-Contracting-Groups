#Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");

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
					if lev = 0 then
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
					if lev = 0 then
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
						
	
# Eventually, third argument is key length
ConjugatorPortrait:=function( g_list, h_list, depth )
	local G, PermGroups, portrait;
	G:= GroupOfAutomFamily( FamilyObj( g_list[1] ) );
	PermGroups:= ComputePermGroups( G, 10 );

	portrait := ConjugatorPortraitRecursive( g_list, h_list, depth, PermGroups );

	return portrait;

end;
