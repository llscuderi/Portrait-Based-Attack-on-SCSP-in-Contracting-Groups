## Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/portrait_to_tree_aut.g");

PortraitToTreeAut := function(portrait)

if Length(portrait) = 1 then 
	return portrait[1];
else 
	return TreeAutomorphism([PortraitToTreeAut(portrait[2]), PortraitToTreeAut(portrait[3])], portrait[1]);
fi;

end;
