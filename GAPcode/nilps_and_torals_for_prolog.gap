# For any set of adjoint matrices or Lie algebra, generate a string containing
# the constraints needed for Sicstus Prolog to use CLPFD. Output it to a
# Prolog file, where the Prolog file writes to its own file.

AdjMatsTo2NilpConst := function (Admats)
	local IntAdmats,mat,row,ent,R,n,x,genelt,i,cons,sqr,sqrAsTimes,withpreamble;
	n:=Length(Admats);
	IntAdmats := List(Admats,mat->List(mat,row->List(row,ent->Int(ent))));
	R:=PolynomialRing(Rationals,n);
	x:=IndeterminatesOfPolynomialRing(R);
	genelt:=Sum(List([1..n],i->IntAdmats[i]*x[i]));
	cons := String(AsSet(Flat(genelt^2) mod 2));
	cons := ReplacedString(cons," 0,","");
	cons := ReplacedString(cons,",",") mod 2 #=0,\n (");
	cons := ReplacedString(cons,"[","(");
	cons := ReplacedString(cons," ]",") mod 2 #=0.");
	for i in [1..n] do
		sqr := String(x[i]^2);
		sqrAsTimes := Concatenation(String(x[i]),"*",String(x[i]));
		cons := ReplacedString(cons,sqr,sqrAsTimes);
	od;
	withpreamble := Concatenation(
		":-use_module(library(clpfd)).\n\n:-use_module(library(lists)).\n\ncons(xs) :- xs = ",
		String(x),
		", domain(xs,0,1),",
		cons,"\n",
		"find_to_file(Xs) :-\n",
        	" open_null_stream(StrBin),\n",
	        " set_output(StrBin),\n",
		" cons(Xs),findall(Xs,labeling([],Xs),Vecs),\n",
		" %open($FILE,write,$STREAM),\n",
		" write($STREAM,'['),\n",
	        " maplist(writeout($STREAM),Vecs),\n",
		" write($STREAM,']'),\n",
		" %close($STREAM),\n",
	        " close(StrBin),\n",
		" length(Vecs,Len),\n",
		" write(Len).\n",
		"writeout(Str,Vec) :- write(Str,Vec),write(Str,','),nl(Str).");
	withpreamble := ReplacedString(withpreamble,"x","X");
	return StripLineBreakCharacters(withpreamble);
	end;;



AdjMatsToToral := function (Admats)
	local IntAdmats,mat,row,ent,R,n,x,genelt,i,cons,eqns,sqr,sqrAsTimes,withpreamble,flatsqr,flatgen;
	n:=Length(Admats);
	IntAdmats := List(Admats,mat->List(mat,row->List(row,ent->Int(ent))));
	R:=PolynomialRing(Rationals,n);
	x:=IndeterminatesOfPolynomialRing(R);
	genelt:=Sum(List([1..n],i->IntAdmats[i]*x[i]));
	flatsqr:=Flat(genelt^2+genelt) mod 2;
	eqns:=AsSet(flatsqr);
	cons := Concatenation(
		":-use_module(library(clpfd)).\n\n:-use_module(library(lists)).\ncons(xs) :- xs = ",
		String(x),
		", domain(xs,0,1),\n");
	for i in eqns do
		Append(cons,Concatenation(" (",String(i),") mod 2 #=0",",\n"));
	od;
	Remove(cons);
	Remove(cons);
	Append(cons,".\n");
	
	for i in [1..n] do
		sqr := String(x[i]^2);
		sqrAsTimes := Concatenation(String(x[i]),"*",String(x[i]));
		cons := ReplacedString(cons,sqr,sqrAsTimes);
	od;
	withpreamble := Concatenation(cons,
		"find_to_file(Xs) :-\n",
        	" open_null_stream(StrBin),\n",
	        " set_output(StrBin),\n",
		" cons(Xs),findall(Xs,labeling([],Xs),Vecs),\n",
		" %open($FILE,write,$STREAM),\n",
		" write($STREAM,'['),\n",
	        " maplist(writeout($STREAM),Vecs),\n",
		" write($STREAM,']'),\n",
		" %close($STREAM),\n",
	        " close(StrBin),\n",
		" length(Vecs,Len),\n",
		" write(Len).\n",
		"writeout(Str,Vec) :- write(Str,Vec),write(Str,','),nl(Str).");
	withpreamble := ReplacedString(withpreamble,"x","X");
	return StripLineBreakCharacters(withpreamble);
	end;;



LieAlgTo2NilpConst := function (L)
	local B,Admats,i;
	B:=Basis(L);
	Admats:=List(B,i->AdjointMatrix(B,i));
	return AdjMatsTo2NilpConst(Admats);
	end;;


LieAlgToToral := function (L)
	local B,Admats,i;
	B:=Basis(L);
	Admats:=List(B,i->AdjointMatrix(B,i));
	return AdjMatsToToral(Admats);
	end;;


SaveToPrologFile := function (prologfile,string,outputfile) # outputfile can be "user" to print to screen
	local stream,newstring,quot;
	if outputfile = "user" then
		newstring := ReplacedString(string,"$STREAM","user");
	else
		quot:="\'";
		newstring := ReplacedString(string,"$FILE",Concatenation(quot,outputfile,quot));
		newstring := ReplacedString(newstring,"%","");
		newstring := ReplacedString(newstring,"$STREAM","StrOut");
	fi;
	stream := OutputTextFile(prologfile,false);
	SetPrintFormattingStatus(stream,false);
	PrintTo(stream, newstring);
	CloseStream(stream);
	return true;
	end;;
