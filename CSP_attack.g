
#Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");

#Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");

#Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");




G:=AG_Groups.GrigorchukGroup;
AssignGeneratorVariables(G);
G3:=PermGroupOnLevel(G,3);
G4:=PermGroupOnLevel(G,4);

f:=function(g)
	local i,L;
	L:=[];
	for i in [1..3] do
		Add(L,g^i);
	od;
	return L;
end;