# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/testing.g");

# Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/testing.g");


# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/testing.g");

# Note: Need to load CSP_attack.g and random_grigorchuk.g first 
# TODO: Find a way to import files automatically if a way exists

# ---- Prelims ----

LoadPackage("automgrp");
G := AG_Groups.GrigorchukGroup;


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

# Tests the ConjugatorPortrait function in specified group G
TestConjugatorPortrait := function(G, list_size, conj_length, attempts)
  local successes, i, g_list, r, h_list, result, r_portrait, depth;
  successes := 0;

  for i in [1..attempts] do

    # TODO: Do we want g's of specified length? 
    g_list := List([1..list_size], x -> Random(G));
    r := Random_Element(conj_length, G);
    h_list := List(g_list, x -> r^-1*x*r);
  
    # ConjugatorPortrait returns list [portrait, depth]
    result := ConjugatorPortrait(g_list, h_list, conj_length);
    r_portrait := result[1];
    depth := result[2];

    if r_portrait = AsNestedList(r, depth) then
        successes := successes + 1;
    fi;
  od;

  return Float(successes/attempts);

end;



      
