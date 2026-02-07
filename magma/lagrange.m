freeze;

// matrix-valued dirichlet map
function dirichlet_map(X, S, precision)
  return Matrix([m(x, S) : x in X]) where m is AdeleRing(GlobalField(S[1]) : Precision := precision)`DirichletMap;
end function;

// mulitplicative independence test
function are_independent_s_units(U, S, prec)
  
// one-element sets (number fields)
  if #U eq 1 then
    return not IsTorsionUnit(U[1]), _;
  end if;

  Sseq := SetToSequence(S);

  F := Parent(U[1]);

  // function fields
  if Characteristic(F) gt 0 then
    return Dimension(Nullspace(Submatrix(dirichlet_map(U, Sseq, prec), 1, 1, #U, #S-1))) eq 0;
  end if;

  d := RationalDegree(F);

  // trivial extensions (number fields)
  if d eq 1 then
    // take the unique infinite place to be the one not considered for independence
    M := Matrix([[Valuation(Idele(u), p) : p in [p : p in S | IsFinitePlace(p)]] : u in U]);
    if Rank(M) eq #U then
      return true, _;
    else
      return false, 10;
    end if;
  end if;

  // number fields, Fieker-Pohst, 2006: for S == InfinitePlaces(F) !
  // someone's gonna prove generality?
  function qs(M)
    m := Ncols(M);
    Q := ChangeRing(M, FieldOfFractions(BaseRing(M)));
    for i := 1 to m do
      _, p := Maximum([Q[j][j] : j in [i..m]]);
      p := p+i-1;
      if p ne i then
        for j := i to m do
          a := Q[j][i];
          Q[j][i] := Q[j][p];
          Q[j][p] := a;
        end for;
        for j := i to m do
          a := Q[i][j];
          Q[i][j] := Q[p][j];
          Q[p][j] := a;
        end for;
      end if;
      if IsZero(Q[i,i]) then
        return 0;
      end if;
      for j := i+1 to m do
        Q[j,i] := Q[i,j];
        Q[i,j] /:= Q[i,i];
      end for;
      for k := i+1 to m do
        for l := k to m do
          Q[k,l] -:= Q[k,i]*Q[i,l];
          Q[l,k] := Q[k, l];
        end for;
      end for;
    end for;
    return &*[Q[i][i] : i in [1..m]];
  end function;

  l := #U;
  s := Ceiling(MaximumNorm(dirichlet_map(U, Sseq, 10)));
  delta := (21/128*Log(d)/d^2)^l/HermiteConstant(l);
  n := #Sseq;
  epsilon := delta/(3*n*s*l*(1+s)^(l-1)*2^(2*l-1));
  precision := 2*Ceiling(-Log(10, epsilon));
  A := dirichlet_map(U, Sseq, precision);
  x := qs(A*Transpose(A));
  if x ge delta/2 then
    return true, _;
  else
    return false, precision; // the precision used to detect dependency
  end if;
  
end function;

// copy construction and normalization,
// not to be confused with reduction!
function s_normalize(i, S)
  result := Parent(i)!1;
  for p in Support(i) diff S do
    SetComponent(~result, p, GetComponent(i, p : ForceEmbedding := false));
  end for;
  return result;
end function;

// returns a set of neighbours of an S-minimum
function neighbours(F, S, i)
  result := [];
  for p in S do
    T := S diff {p};
    lower_bound := Adele(F!0);
    SetComponent(~lower_bound, p, F!1);
    upper_bound := s_normalize(i, S);
    increment := SetComponent(Idele(F!1), p, 1/(IsArchimedeanPlace(p) select LocalParameter(Parent(i), p) else GlobalParameter(p)));
    //increment := SetComponent(Idele(F!1), p, 1/(IsArchimedeanPlace(p) select F!1/3 else GlobalParameter(p)));
    repeat
      upper_bound *:= increment;
      box := Enumerate(lower_bound, upper_bound : 
	OnlyNonZeroElements := true,
	StopCardinality := 1,
	StrictLowerBoundPlaces := {p},
	StrictUpperBoundPlaces := T);
    until not IsEmpty(box);
    repeat
      x := box[1];
      SetComponent(~upper_bound, p, x);
      box := Enumerate(upper_bound : 
        OnlyNonZeroElements := true,
	StopCardinality := 1,
	StrictBoundPlaces := S);
    until IsEmpty(box);
    Append(~result, i/x);
  end for;
  return result;
end function;

// generalized Lagrange algorithm fpr global fields
// in chi(F) = 0, the independence test is only proven for S == InfinitePlaces(F), the use-case
function independent_s_units_lagrange(F, S, precision)
  V := [Idele(F!1 : Precision := precision)];
  n := 1;
  units := [];
  while n le #V do
    v := V[n];
    for w in neighbours(F, S, v) do
      has_associate := false;
      for u in V do
        x := u/w;
        if Support(x) subset S then
          has_associate := true;
          cand := PrincipalComponent(x);
	  U := units cat [cand];
	  units_are_independent := are_independent_s_units(U, S, precision);
	  if units_are_independent then
	    units := U;
	    if #units eq (#S-1) then
	      return units;
	    end if;
          end if;
          break;
        end if;
      end for;
      if not has_associate then
        Append(~V, w);
      end if;
    end for;
    n +:= 1;
  end while;
end function;

intrinsic GlobalFieldIndependentUnits(S::SeqEnum : Precision := 20) -> SeqEnum
{Returns a maximal set of independent S-units of the global field F.}
  test, F := IsSequenceOfPlaces(S);
  require test : "Argument 1 is not a set of places!"; //cor
  if #S le 1 then
    return [];
  end if;
  return independent_s_units_lagrange(F, SequenceToSet(S), Precision);
end intrinsic;

intrinsic GlobalFieldIndependentUnits(F::Fld : Precision := 20) -> SeqEnum
{Returns a maximal set of independent units of the global field F.}
  return GlobalFieldIndependentUnits(InfinitePlaces(F) : Precision := Precision);
end intrinsic;
