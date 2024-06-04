#Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");


AreNotConjugate:=function(G,a,b,levels)
	local l, Glev;
	for l in [1..levels] do
		# this would be better if we precomputed these somewhere
		# but it's fast so we won't worry about it for now
		Glev:= PermGroupOnLevel(G, l);
		if not IsConjugate(Glev, PermOnLevel(a,l), PermOnLevel(b,l)) then
			# Return true if NOT conjugate 
			return true; 
		else
			return false;
		fi;
	od;
end;


ConjugatorEvenFirstLevel:=function(G,g,h)
	local g0, g1, h0, h1;
	g0 := Section(g,1);
	g1 := Section(g,2);
			
	h0 := Section(h,1);
	h1 := Section(h,2);

	# Case A: g even
	if PermOnLevel(g,1) = () then
		# Case 1: if the following aren't conjugate, r isn't even
		if AreNotConjugate(G,g0,h0,5) or AreNotConjugate(G,g1,h1,5) then
			return false;
		# Case 2: if the following aren't conjugate, r is even
		elif AreNotConjugate(G,g0,h1,5) or AreNotConjugate(G,g1,h0,5) then
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

ConjugatorPortraitRecursive:=function(G,g,h,level)
	# Build as much of the portrait of r as we can just by traversing even vertices
	local r_partial_portrait, g0, g1, h0, h1;
	r_partial_portrait:=[];
	
	g0:=Section(g,1);
	g1:=Section(g,2);
	h0:=Section(h,1);
	h1:=Section(h,2);

	ConjugatorEvenFirstLevel := ConjugatorEvenFirstLevel(G,g,h);	

	if level=0 then
		Add(r_partial_portrait, []);
	fi;
	
	if ConjugatorEvenFirstLevel = fail then
		Print("Failed");
		Add(r_partial_portrait, ["x"]);
		Print(r_partial_portrait);

	elif ConjugatorEvenFirstLevel then
		Print("Even");
		Add(r_partial_portrait, ());
		Add(r_partial_portrait, ConjugatorPortraitRecursive(G, g0, h0, level-1));
		Add(r_partial_portrait, ConjugatorPortraitRecursive(G, g1, h1, level-1));
	else 
		Print("Odd");
		Add(r_partial_portrait, (1,2));	
		Add(r_partial_portrait, ConjugatorPortraitRecursive(G, g0, h1, level-1));
		Add(r_partial_portrait, ConjugatorPortraitRecursive(G, g1, h0, level-1));
	fi;

	return r_partial_portrait;				
end;


