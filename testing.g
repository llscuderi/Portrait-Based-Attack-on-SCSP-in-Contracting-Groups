# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/random_grigorchuk.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/testing.g");

# Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/random_grigorchuk.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/testing.g");


# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/random_grigorchuk.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/testing.g");

# Note: Need to load CSP_attack.g and random_grigorchuk.g first 

# ---- Prelims ----

LoadPackage("automgrp");
G := AG_Groups.GrigorchukGroup;

# ---- Functions useful for testing ----


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


TestConjugatorPortraitGrigorchuk := function(list_size, level, conj_length, attempts)
  local successes, i, r_portrait;
  successes := 0;

  for i in [1..attempts] do

    g_list := List([1..list_size], x -> Random(G));
    r := RandomElementGrigorchuk(conj_length);
    h_list := List(g_list, x -> r^-1*x*r);
  
    r_portrait := ConjugatorPortrait(g_list, h_list, level);
    if r_portrait = AsNestedList(r, level) then
        successes := successes + 1;
    fi;
  od;

  return Float(successes/attempts);

end;



      
