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

AreNotConjugate:=function(G,PermGroups,a,b,levels)
	local l, Glev;
	for l in [1..levels] do
		Glev:=PermGroups[l]; 
		if not IsConjugate(Glev, PermOnLevel(a,l), PermOnLevel(b,l)) then
			# Return true if NOT conjugate 
			return true; 
		else
			return false;
		fi;
	od;
end;


ConjugatorEvenFirstLevel:=function(G,PermGroups,g,h)
	local g0, g1, h0, h1;
	g0 := Section(g,1);
	g1 := Section(g,2);
			
	h0 := Section(h,1);
	h1 := Section(h,2);

	# Case A: g even
	if PermOnLevel(g,1) = () then
		# Case 1: if the following aren't conjugate, r isn't even
		if AreNotConjugate(G,PermGroups,g0,h0,5) or AreNotConjugate(G,PermGroups,g1,h1,5) then
			return false;
		# Case 2: if the following aren't conjugate, r is even
		elif AreNotConjugate(G,PermGroups,g0,h1,5) or AreNotConjugate(G,PermGroups,g1,h0,5) then
			return true;
		else
			return fail;
		fi;
	
	# Case B: g odd
	else
		Print("g odd");
		return fail;
	fi;
end;

ConjugatorPortraitRecursive:=function(G,PermGroups,g,h,level)
	# Build as much of the portrait of r as we can just by traversing even vertices
	local r_portrait, g0, g1, h0, h1;
	r_portrait:=[];
	
	g0:=Section(g,1);
	g1:=Section(g,2);
	h0:=Section(h,1);
	h1:=Section(h,2);

	ConjugatorEvenFirstLevel := ConjugatorEvenFirstLevel(G,PermGroups,g,h);	

	if level=0 then
		Add(r_portrait, []);
	fi;
	
	if ConjugatorEvenFirstLevel = fail then
		Print("Failed");
		Add(r_portrait, ["x"]);
		Print(r_portrait);

	elif ConjugatorEvenFirstLevel then
		Print("Even");
		Add(r_portrait, ());
		Add(r_portrait, ConjugatorPortraitRecursive(G, PermGroups, g0, h0, level-1));
		Add(r_portrait, ConjugatorPortraitRecursive(G, PermGroups, g1, h1, level-1));
	else 
		Print("Odd");
		Add(r_portrait, (1,2));	
		Add(r_portrait, ConjugatorPortraitRecursive(G, PermGroups, g0, h1, level-1));
		Add(r_portrait, ConjugatorPortraitRecursive(G, PermGroups, g1, h0, level-1));
	fi;

	return r_portrait;				
end;


