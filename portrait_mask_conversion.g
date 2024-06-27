##  Read("C:/Users/Arsalan Malik/Desktop/Gap-files/portrait_mask_conversion.g");
##  Read("/Users/Arsalan/Documents/gap-4.12.1/Gap codes/portrait_mask_conversion.g");
##  Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");



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

############# MASK ELEMENT TO PORTRAIT ##############


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

#This function takes a group element in mask format <mask_element> and level <lev> for the required portrait.
#It returns the element as portrait developed up till the level <lev>.
MaskToPortrait := function(mask_element, lev)

    local p, s  ;

    p     := mask_element[2] ;
    
    if 
        lev = 0 then return [mask_element[1][1]];
    fi;
    
    if
        1^p<=2^(lev-1) then s:=();
    else 
        s:=(1,2); 
    fi;
    
    return [ s, MaskToPortrait([mask_element[1]{[1..2^(lev-1)]}, PermOfSection(p,lev,1)],lev-1), MaskToPortrait([mask_element[1]{[2^(lev-1)+1..2^lev]}, PermOfSection(p,lev,2)],lev-1) ];
end;

############# PORTRAIT TO MASK ELEMENT ##############

mask_one_ext_boundary := function(mask_element) 

    local i, new_boundary ;

    new_boundary := [] ;

    for i in mask_element[1]

        do 
            Append (new_boundary , Sections(i)) ; 
        od;

    return new_boundary ;
end;


PortraitToMaskBoundary := function(portrait , lev)

    local i , j , k , boundary_list , flat_list , initial_level , ext_iter ;

    flat_list     := Flat(portrait) ;
    boundary_list := [] ;

    for i in [1..Length(flat_list)]
        do 
            if IsPerm(flat_list[i]) = false then 
            Append(boundary_list,[flat_list[i]]) ;
            fi;
        od;

    initial_level := Log(Length(boundary_list),2) ;
    
    ext_iter := lev - initial_level ; 
    #Print(ext_iter,"\n");

    if ext_iter > 0 then
        for j in [1..ext_iter]
            do 
                boundary_list := mask_one_ext_boundary([boundary_list]);
            od;
            
        elif    
            ext_iter < 0 then Error("PortraitToMaskBoundary: <lev> cannot be smaller than the depth of the portrait");
    fi;

    return boundary_list ;
end;


PortraitToMaskBoundaryNonuniform := function(portrait , lev)
    local i , sections, d;
    
	if lev=0 then
        if Length(portrait)=1 then
            return portrait;
        else
            Error("PortraitToMaskBoundaryNonuniform: <lev> cannot be smaller than the depth of the portrait");
        fi;
    fi;

    if Length(portrait)=1 then 
        return Sections(portrait[1], lev); 
    fi;

    d := Length(portrait) - 1;

    sections:=[];

    for i in [1..d] do
		Append(sections, PortraitToMaskBoundaryNonuniform(portrait[i+1],lev-1));
	od;

    return sections;
end;


PermutationOfNestedPortrait := function(portrait, lev)

    local i, d, perms, l;

    if lev=1 then
        if Length(portrait)=1 then
            return PermOnLevel(portrait[1], lev);
        else
            return portrait[1];
        fi;
    fi;

    if Length(portrait)=1 then 
        return PermOnLevel(portrait[1], lev); 
    fi;

    d := Length(portrait) - 1;

    perms:=List([1..d],x->PermutationOfNestedPortrait (portrait[x+1], lev-1));

    l := [];

    for i in [1..d] 
        do
            Append(l, List(ListPerm(perms[i],d^(lev-1)),x->x+d^(lev-1)*(i^portrait[1]-1)));
        od;

    return PermList(l);
end;

#This function takes portrait <portrait> and its level <lev> as input.
#It returns the element in mask format developed at the level <lev>.

PortraitToMask := function(portrait , lev)

    local mask_element ;

    mask_element := [] ;

    mask_element[1] := PortraitToMaskBoundaryNonuniform(portrait,lev);
    mask_element[2] := PermutationOfNestedPortrait(portrait,lev);

    return mask_element;
end;

############# END ##############
