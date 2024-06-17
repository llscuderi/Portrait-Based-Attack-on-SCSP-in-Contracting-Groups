##  Read("C:/Users/Arsalan Malik/Desktop/Gap-files/mask_to_portrait_final.g");
##  Read("/Users/Arsalan/Documents/gap-4.12.1/Gap codes/mask_to_portrait_final.g");


mask_function := function(group_element , fixed_depth) 

    local decomposition ;

    decomposition := [] ;

    if fixed_depth = 0 then

        decomposition[1] := Sections(group_element, 1) ;
        decomposition[2] := PermOnLevel(group_element, 1) ;
 
    else 

        decomposition[1] := Sections(group_element, fixed_depth) ;
        decomposition[2] := PermOnLevel(group_element, fixed_depth) ;
    fi;

    return decomposition;
end;


PermOfSection := function (p,lev,v)
    if 1^p<=2^(lev-1) then
        if v=1 then
            return PermList(ListPerm(p,2^(lev-1)));
        else
            return PermList(List(ListPerm(p,2^(lev)){[2^(lev-1)+1..2^lev]},x->x-2^(lev-1)));
        fi;
    else
        if v=2 then
            return PermList(ListPerm(p,2^(lev)){[2^(lev-1)+1..2^lev]});
        else
            return PermList(List(ListPerm(p,2^(lev-1)),x->x-2^(lev-1)));
        fi;
    fi;
end;


MaskToPortrait := function(mask_element, lev)

    local p, s  ;

    p     := mask_element[2] ;
    
    if 
        lev = 0 then return mask_element[1][1];
    fi;
    
    if
        1^p<=2^(lev-1) then s:=();
    else 
        s:=(1,2); 
    fi;
    
    return [s,MaskToPortrait([mask_element[1]{[1..2^(lev-1)]},PermOfSection(p,lev,1)],lev-1),MaskToPortrait([mask_element[1]{[2^(lev-1)+1..2^lev]},PermOfSection(p,lev,2)],lev-1)];
end;

