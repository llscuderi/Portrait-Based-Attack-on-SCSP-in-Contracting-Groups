#Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
#Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");


# Hardcoding some things for testing 
G:=AG_Groups.GrigorchukGroup;
AssignGeneratorVariables(G);

g:=a*b;

r:=a^2*b*a;
Print(PermOnLevel(r,1));
h:= r^-1*g*r;

ConjugatorEvenFirstLevel:=function(G,g,h, G5)
	local g0, g1, h0, h1;
	g0 := Section(g,1);
	g1 := Section(g,2);
			
	h0 := Section(h,1);
	h1 := Section(h,2);

	# Case A: g even
	if PermOnLevel(g,1) = () then
		# eventually we should make an IsNotConjugate function that
		# tests multiple levels

		# Case 1: tests if r is NOT even
		if not IsConjugate(G5, PermOnLevel(g0,5), PermOnLevel(h0,5)) 
		or not IsConjugate(G5, PermOnLevel(g1,5), PermOnLevel(h1,5)) then
			return false;
		# Case 2: tests if r is even
		elif not IsConjugate(G5, PermOnLevel(g0,5), PermOnLevel(h1,5)) 
		or not IsConjugate(G5, PermOnLevel(g1,5), PermOnLevel(h0,5)) then
			return true;
		else
			return fail;
		fi;
	
	# Case B: g odd
	else
		if not IsConjugate(G5, PermOnLevel(g0*g1,5), PermOnLevel(h0*h1,5))  then
			return false;
		elif not IsConjugate(G5, PermOnLevel(g1,5), PermOnLevel(h0,5))
		or not IsConjugate(G5, PermOnLevel(g0,5), PermOnLevel(h1,5)) then
			return true;
		else
			return fail;
		fi;
	fi;
end;

ConjugatorPortrait:=function(G,g,h)
	#for now this just calls the function we want to test
	local G5;
	G5:=PermGroupOnLevel(G,5);
	Print("\n",ConjugatorEvenFirstLevel(G,g,h,G5));
end;

ConjugatorPortrait(G,g,h);
