RandomElementGrigorchuk := function(len)
	local i , randomelt;

	randomelt := Random([One(G), a]);

	if len mod 2 = 0 then

        if Length(Word(randomelt)) = 0 then    
		    for i in [1 .. len/2] do 
		    randomelt := randomelt *Random ([b, c, d]) * a;
		    od;
            return randomelt;

        else
            for i in [1 .. (len/2)-1] do 
		    randomelt := randomelt *Random ([b, c, d]) * a;
            od;
            return randomelt* Random([b,c,d]) ;
        fi;

	else 

        if Length(Word(randomelt)) = 0 then
            for i in [1.. (len-1)/2 ] do
            randomelt := randomelt* Random ([b,c,d]) * a;
            od;
            return randomelt * Random([b,c,d]);

        else
		    for i in [1 .. (len-1)/2] do 
		    randomelt := randomelt *Random ([b, c, d]) * a;
		    od;
		    return randomelt ;
        fi;
	fi;
end;