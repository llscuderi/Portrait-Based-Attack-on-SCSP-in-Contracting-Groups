Random_Element := function(len , group)
 
    local i , j , generators , gen_inv , randomelt ;
 
    generators := GeneratorsOfGroup(group) ;
    gen_inv    := [] ;
 
    for i in [1..Length(generators)]
        do 
            Append(gen_inv , [(generators[i])^(-1)]);
        od;
    Append(gen_inv , generators);
    #Print(gen_inv , "\n") ;

 
    randomelt := One(group) ;
    j         := 0 ;
 
    while j < len 
        do 
            randomelt := randomelt * Random(gen_inv) ;
            j := Length(Word(randomelt)) ;
        od;
    return randomelt ;
 
end;
