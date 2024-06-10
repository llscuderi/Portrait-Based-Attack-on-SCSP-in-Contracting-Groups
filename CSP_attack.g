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



ConjugatorPortraitRecursive:=function( g_list, h_list, lev, PermGroups )
	
	local i, ConjEven, g_list_r0, h_list_r0, g_list_r1, h_list_r1, r0, r1, idx;
	
	for i in [1..Size(g_list)] do
		if PermOnLevel( g_list[i], 1 ) = () then
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

					# pick an odd element of g_list
					idx := -1;
					#for i in [1..Size(g_list)] do
					#	if PermOnLevel( g_list[i], 1 ) = (1,2) then
					#		idx := i;
					#		break;
					#	fi; od;
					
					if not idx = -1 then
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
						r1 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev-1, PermGroups );
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

					# pick an odd element of g_list
					idx := -1;

					#for i in [1..Size(g_list)] do
					#	if PermOnLevel( g_list[i], 1 ) = (1,2) then
					#		idx := i;
					#		break;
					#	fi; od;

					
					if not idx = -1 then
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
						r1 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev-1, PermGroups );
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
						
	
# Eventually, third element is key length
ConjugatorPortrait:=function( g_list, h_list, depth )
	local G, PermGroups, portrait;
	G:= GroupOfAutomFamily( FamilyObj( g_list[1] ) );
	PermGroups:= ComputePermGroups( G, 10 );

	portrait := ConjugatorPortraitRecursive( g_list, h_list, depth, PermGroups );

	return portrait;

end;
