Random_Element := function(len , group)
 
    local i , rule, rules, rules_product, rules_equivalence, generators, family, generators, randomelt, FindSuccessors ;
    
    # TODO: have this function generate a list of random elements (so we don't do the overhead every time)
    rws        := AG_RewritingSystem(group);
    generators := GeneratorsOfMonoid(Image(rws!.mhom)) ;
 
    rules      := AG_RewritingSystemRules(group);
    rules_product := [];
    rules_equivalence := [];
    family     := FamilyObj(rules[1][1]);

    for rule in rules do
	letter_rep := LetterRepAssocWord(rule[1]);
	if Size(letter_rep) = 2 then
		Add(rules_product, letter_rep);
        elif Size(letter_rep) = 1 then
		Add(rules_equivalence, [letter_rep[1], LetterRepAssocWord(rule[2])];
	fi;
    od;

    starters   := Set([1..Size(generators)]);
    successors := List([1..Size(generators)], x -> Set([1..Size(generators)]) );
   
    # No generator can be followed by an element that will simplify the product 
    for rule in rules_product do
	RemoveSet(successors[rule[1]], rule[2]);
    od;

    # If two generators are equivalent, ignore one
    for rule in rules_equivalence do
	for i in [1..Size(successors)] do	
		RemoveSet(successors[i], rule[1]);
	od;
	successors[rule[1]] := [];
	RemoveSet(starters, rule[1]);
    od;

    gen :=  Random(starters);
    randomelt := [gen];
 
    for i in [2..len] do 
        do 
	    gen := Random(successors[gen]);
	    Add( randomelt, gen );
        od;

    # Changes from denoting generators/inverses as 1, 2, 3.. to 1, -1, 2, -2..
    randomelt := List( randomelt, x -> (-1)^(x + 1)*Ceil(Float(x/2)) );
    randomelt := List( randomelt, x -> Int(x) );

    randomelt := AssocWordByLetterRep(family, randomelt);
    # TODO: Representative doesn't work
    randomelt := Representative(randomelt);

    return randomelt ;
 
end;
