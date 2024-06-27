# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/testing.g");

# Read("~/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/testing.g");


# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/testing.g");

# Note: Need to load CSP_attack.g and random_grigorchuk.g first 
# TODO: Find a way to import files automatically if a way exists

# ---- Prelims ----

LoadPackage("automgrp");
G := AG_Groups.GrigorchukGroup;
nucleus := FindNucleus(G)[1];


# ---- Functions for testing ----

# Returns element in the same format as output of ConjugatorPortrait
# This way, we can check if the output is equal to the actual conjugator
AsNestedList := function(r, lev)

   if PermOnLevel(r,1) = () then
    if lev = 1 then
      return [(), 1, 1];
    fi;

    return [(), AsNestedList(Section(r,1), lev-1), AsNestedList(Section(r,2), lev-1)];
  else
    if lev = 1 then
      return [(1,2), 1, 1];
    fi;
    
    return [(1,2), AsNestedList(Section(r,1), lev-1), AsNestedList(Section(r,2), lev-1)];
  fi;
end;

N_masks := List(nucleus, x -> mask_function(x,1));
N_portraits := List(N_masks, x -> MaskToPortrait(x, 1)); 

# function to take portrait of depth 1 ([perm, [word], [word]]) 
# and if it is in the nucleus, return element of nucleus
NucleusElementByPortrait := function( port )
	local i;
	
	for i in [1..Size(nucleus)] do
		if port = N_portraits[i] then 
			return nucleus[i];
		fi;
	od;

	return fail;
end;

ExtendPortrait := function(port)
	local depth, extended_portrait1, extended_portrait2;

	if Size(port) = 1 then 
		return [AutomPortrait(port[1]), AutomPortraitDepth(port[1])];              
	else 
		extended_portrait1 := ExtendPortrait(port[2]);
		extended_portrait2 := ExtendPortrait(port[3]); 

		depth := Maximum(extended_portrait1[2], extended_portrait2[2]) + 1;
		
		return [ [port[1], extended_portrait1[1], extended_portrait2[1]], depth ]; 
	fi; 
end;	

PrunePortrait := function (port) 
	local pruned_portrait, depth, pruned_1, pruned_2;                                

	if Size(port) = 1 then 
		return [port, 0]; 
	fi;  

	pruned_portrait := port;

	if Size(port[2]) > 1 or Size(port[3]) > 1 then
		pruned_1 := PrunePortrait(port[2]);
		pruned_2 := PrunePortrait(port[3]);

		depth := Maximum(pruned_1[2], pruned_2[2]) + 1;

		pruned_portrait := [port[1], pruned_1[1], pruned_2[1]];
	else
		depth := 1; 
	fi;      

	if pruned_portrait in N_portraits then 
		return [ [NucleusElementByPortrait(pruned_portrait)], 0 ]; 
	fi;

	return [pruned_portrait, depth]; 
end;

ContractingPortrait := function(port) 
	local cportrait;
	cportrait := ExtendPortrait(port);
	cportrait := PrunePortrait(cportrait[1]);
	return cportrait;
end;


# Tests the ConjugatorPortrait function in specified group G
TestConjugatorPortrait := function(G, list_size, g_length, conj_length, attempts)
  local successes, i, g_list, r, h_list, result, r_portrait, depth;
  successes := 0;

  for i in [1..attempts] do

    g_list := List([1..list_size], x -> Random_Element(g_length, G));
    r := Random_Element(conj_length, G);
    h_list := List(g_list, x -> r^-1*x*r);
	
    Print("g_list: ", g_list, "\n");
    Print("h_list: ", h_list, "\n");
    Print("r: ", r, "\n");
  
    # ConjugatorPortrait returns list [portrait, depth]
    result := ConjugatorPortrait(g_list, h_list, conj_length);
    
    if not result = fail then
	    r_portrait := result[1];

	    if r_portrait = AutomPortrait(r) then
		successes := successes + 1;
	    else
		# If a list is returned but it isn't the right portrait, something is wrong
		Error("output is not AutomPortrait");
	    fi;
    fi;

    od;

  return Float(successes/attempts);

end;



      
