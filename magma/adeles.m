//kate: syntax: MAGMA;

freeze;

/* ------------------------------------------------------------------------ */

intrinsic IsGlobalField(F::Fld) -> BoolElt
{Returns true if and only if F is a global field.}
  case Category(F) :
    when FldRat, FldNum :
      return true;
    when FldFunRat, FldFun :
      // BUG: Magma built-in IsGlobal() still crashes sometimes!
      // especially when called as IsGlobal(Parent(x)) ...
      // strange enough, all workarounds seem to suffer the same problem
      // return IsGlobal(F);
      return true;
    else
      return false;
  end case;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsRationalField(F::FldRat) -> BoolElt
{Returns true iff F is a rational field.}
  return true;
end intrinsic;

intrinsic IsRationalField(F::FldFunRat) -> BoolElt
{Returns true iff F is a rational field.}
  return true;
end intrinsic;

intrinsic IsRationalField(F::FldNum) -> BoolElt
{Returns true iff F is a rational field.}
  return false;
end intrinsic;

intrinsic IsRationalField(F::FldFun) -> BoolElt
{Returns true iff F is a rational field.}
  return false;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic RationalSubfield(F::FldRat) -> FldRat
{Returns a rational subfield of F.}
  return F;
end intrinsic;

intrinsic RationalSubfield(F::FldFunRat) -> FldFunRat
{Returns a rational subfield of F.}
  return F;
end intrinsic;

intrinsic RationalSubfield(F::FldNum) -> FldRat
{Returns a rational subfield of F.}
  return Rationals();
end intrinsic;

intrinsic RationalSubfield(F::FldFun) -> FldFunRat
{Returns a rational subfield of F.}
  return BaseField(RationalExtensionRepresentation(F));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic RationalDegree(F::FldRat) -> RngIntElt
{Returns the degree of F over a rational subfield.}
  return 1;
end intrinsic;

intrinsic RationalDegree(F::FldFunRat) -> RngIntElt
{Returns the degree of F over a rational subfield.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  return 1;
end intrinsic;

intrinsic RationalDegree(F::FldNum) -> RngIntElt
{Returns the degree of F over a rational subfield.}
  return AbsoluteDegree(F);
end intrinsic;

intrinsic RationalDegree(F::FldFun) -> RngIntElt
{Returns the degree of F over a rational subfield.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  return AbsoluteDegree(RationalExtensionRepresentation(F));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsAbsoluteGlobalField(F::FldRat) -> BoolElt
{Returns true iff F is an absolute extension field.}
  return true;
end intrinsic;

intrinsic IsAbsoluteGlobalField(F::FldFunRat) -> BoolElt
{Returns true iff F is an absolute extension field.}
  return true;
end intrinsic;

intrinsic IsAbsoluteGlobalField(F::FldNum) -> BoolElt
{Returns true iff F is an absolute extension field.}
  return BaseField(F) eq RationalSubfield(F);
end intrinsic;

intrinsic IsAbsoluteGlobalField(F::FldFun) -> BoolElt
{Returns true iff F is an absolute extension field.}
  return BaseField(F) eq RationalSubfield(F);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsRelativeGlobalField(F::FldRat) -> BoolElt
{Returns true iff F is a relative extension field.}
  return false;
end intrinsic;

intrinsic IsRelativeGlobalField(F::FldFunRat) -> BoolElt
{Returns true iff F is a relative extension field.}
  return false;
end intrinsic;

intrinsic IsRelativeGlobalField(F::FldNum) -> BoolElt
{Returns true iff F is a relative extension field.}
  return not IsAbsoluteGlobalField(F);
end intrinsic;

intrinsic IsRelativeGlobalField(F::FldFun) -> BoolElt
{Returns true iff F is a relative extension field.}
  return not IsAbsoluteGlobalField(F);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IntegralBasis(F::FldFunRat) -> SeqEnum
{Returns an integral basis for the finite maximal order of F as a sequence of elements of F.}
  return [MaximalOrder(F)!1];
end intrinsic;

intrinsic IntegralBasis(F::FldFun) -> SeqEnum
{Returns an integral basis for the finite maximal order of F as a sequence of elements of F.}
  return Basis(MaximalOrder(F));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic MaximalOrder(F::FldFunRat) -> RngUPol
{Returns the maximal order of F.}
  return RingOfIntegers(F);
end intrinsic;

intrinsic MaximalOrder(F::FldFun) -> RngFunOrd
{Returns the maximal order of F.}
  return MaximalOrderFinite(F);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic MaximalOrderInfinite(F::FldFunRat) -> RngUPol
{Returns the infinite maximal order of F.}
  return ValuationRing(F);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic GlobalFieldSignature(S::SeqEnum) -> SeqEnum
{The signature for the given places S.}
  test, F := IsSequenceOfPlaces(S);
  require test : "Argument 1 is not a sequence of places!"; //cor
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  // we may consider this field as a trivial extension of itself
  if IsRationalField(F) then
    return [<p, 1, 1> : p in S];
  end if;
  return [<p, RamificationIndex(p), InertiaDegree(p)> : p in S];
end intrinsic;

intrinsic GlobalFieldSignature(F::Fld) -> SeqEnum
{The signature of the global field F.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  return GlobalFieldSignature(InfinitePlaces(F));
end intrinsic

/* ------------------------------------------------------------------------ */

intrinsic IsTorsionUnit(x::FldRatElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return x in {1,-1};
end intrinsic;

intrinsic IsTorsionUnit(x::RngIntElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return x in {1,-1};
end intrinsic;

intrinsic IsTorsionUnit(x::FldNumElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  test, y := IsCoercible(MaximalOrder(Parent(x)), x);
  return test and IsTorsionUnit(y);
end intrinsic;

intrinsic IsTorsionUnit(x::FldFunRatElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return IsConstant(x);
end intrinsic;

intrinsic IsTorsionUnit(x::RngUPolElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return IsConstant(FieldOfFractions(Parent(x))!x);
end intrinsic;

intrinsic IsTorsionUnit(x::FldFunElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return IsConstant(x);
end intrinsic;

intrinsic IsTorsionUnit(x::RngFunOrdElt) -> BoolElt
{Returns true if and only if x is a torsion unit.}
  return IsConstant(x);
end intrinsic;

/* ------------------------------------------------------------------------ */

// places:
//  rational fields do not come with a places structure...
//  Q: rational primes p and Infinity() -> universe ExtRe
//  F_q(X): rational prime polynomials p and 1/X -> universe FldFunRat
//  places of non-rational fields exist in Magma

intrinsic IsPlace(p::Any) -> BoolElt, .
{Returns true if and only if p is a place. In this case, the associated global field is returned too.}
  case Category(p) :
    when ExtReElt :
      if IsCoercible(Integers(), p) then
        return IsPlace(Integers()!p);
      elif p eq Infinity() then
        return true, Rationals();
      end if;
    when RngIntElt :
      if p gt 0 and IsPrime(p) then
        return true, Rationals();
      end if;
    when FldRatElt :
      if IsCoercible(Integers(), p) then
        return IsPlace(Integers()!p);
      end if;
    when Infty :
      if p gt 0 then
        return true, Rationals();
      end if;
    when RngUPolElt :
      F := FieldOfFractions(Parent(p));
      require IsGlobalField(FieldOfFractions(Parent(p))) : "Argument 1 is not contained in a global field!";
      if IsMonic(p) and IsPrime(p) then
        return true, FieldOfFractions(Parent(p));
      end if;
    when FldFunRatUElt :
      require IsGlobalField(Parent(p)) : "Argument 1 is not contained in a global field!";
      if IsCoercible(MaximalOrder(Parent(p)), p) then
        return IsPlace(MaximalOrder(Parent(p))!p);
      elif p eq 1/Parent(p).1 then
        return true, Parent(p);
      end if;
    when PlcNumElt :
      return true, NumberField(p);
    when PlcFunElt :
      require IsGlobalField(FunctionField(p)) : "Argument 1 is not contained in a global field!";
      return true, FunctionField(p);
  end case;
  return false, _;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsPlaceForField(p::Any, F::Fld) -> BoolElt
{Returns true iff p is a valid place for F.}
  require IsGlobalField(F) : "Argument 2 is not a global field!"; //cor
  test, field := IsPlace(p);
  return test and field cmpeq F;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsSetOfPlaces(S::SetEnum) -> BoolElt, .
{Returns true if and only if S is a set of places (representatives).
In this case, the correspondig global field is returned too.}
  if IsEmpty(S) then
    return false, _;
  end if;
  for p in S do
    test, field := IsPlace(p);
    if test then
      if not assigned F then
        F := field;
      else
        if field cmpne F then
          return false, _;
        end if;
      end if;
    else
      return false, _;
    end if;
  end for;
  return true, F;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsSequenceOfPlaces(S::SeqEnum) -> BoolElt, .
{Returns true if and only if S is a sequence of places (representatives).
In this case, the correspondig global field is returned too.}
  return IsSetOfPlaces(SequenceToSet(S));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic Places(F::FldRat) -> Str
{Returns the universe of places of F.}
  return ExtendedReals();
end intrinsic;

intrinsic Places(F::FldFunRat) -> Str
{Returns the universe of places of F.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  return F;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsArchimedeanPlace(p::RngIntElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsArchimedeanPlace(p::FldRatElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsArchimedeanPlace(p::Infty) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsArchimedeanPlace(p::ExtReElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p eq Infinity();
end intrinsic;

intrinsic IsArchimedeanPlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsArchimedeanPlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsArchimedeanPlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  return IsInfinite(p) select true else false;
end intrinsic;

intrinsic IsArchimedeanPlace(p::PlcFunElt) -> BoolElt
{Returns true iff p is an archimedean place.}
  return false;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic ArchimedeanPlaces(F::FldRat) -> SeqEnum
{Returns the sequence of archimedean places of F.}
  return InfinitePlaces(F);
end intrinsic;

intrinsic ArchimedeanPlaces(F::FldFunRat) -> SeqEnum
{Returns the sequence of archimedean places of F.}
  return [];
end intrinsic;

intrinsic ArchimedeanPlaces(F::FldNum) -> SeqEnum
{Returns the sequence of archimedean places of F.}
  return InfinitePlaces(F);
end intrinsic;

intrinsic ArchimedeanPlaces(F::FldFun) -> SeqEnum
{Returns the sequence of archimedean places of F.}
  return [];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsRealPlace(p::RngIntElt) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsRealPlace(p::FldRatElt) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsRealPlace(p::Infty) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsRealPlace(p::ExtReElt) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p eq Infinity();
end intrinsic;

intrinsic IsRealPlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsRealPlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is a real place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsRealPlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is a real place.}
  return IsReal(p);
end intrinsic;

intrinsic IsRealPlace(p::PlcFunElt) ->  BoolElt
{Returns true iff p is a real place.}
  return false;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic RealPlaces(F::FldFunRat) -> SeqEnum
{Returns the sequence of real places of F.}
  return [];
end intrinsic;

intrinsic RealPlaces(F::FldFun) -> SeqEnum
{Returns the sequence of real places of F.}
  return [];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsComplexPlace(p::RngIntElt) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::FldRatElt) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::Infty) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::ExtReElt) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is a complex place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor 
  return false;
end intrinsic;

intrinsic IsComplexPlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is a complex place.}
  return IsComplex(p);
end intrinsic;

intrinsic IsComplexPlace(p::PlcFunElt) ->  BoolElt
{Returns true iff p is a complex place.}
  return false;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic ComplexPlaces(F::FldRat) -> SeqEnum
{Returns the sequence of complex places of F.}
  return [];
end intrinsic;

intrinsic ComplexPlaces(F::FldFunRat) -> SeqEnum
{Returns the sequence of complex places of F.}
  return [];
end intrinsic;

intrinsic ComplexPlaces(F::FldNum) -> SeqEnum
{Returns the sequence of complex places of F.}
  return [p : p in InfinitePlaces(F) | IsComplex(p)];
end intrinsic;

intrinsic ComplexPlaces(F::FldFun) -> SeqEnum
{Returns the sequence of complex places of F.}
  return [];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsNonarchimedeanPlace(p::RngIntElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::FldRatElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::Infty) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::ExtReElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p ne Infinity();
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  return IsFinite(p);
end intrinsic;

intrinsic IsNonarchimedeanPlace(p::PlcFunElt) -> BoolElt
{Returns true iff p is a nonarchimedean place.}
  return true;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsInfinitePlace(p::RngIntElt) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsInfinitePlace(p::FldRatElt) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsInfinitePlace(p::Infty) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsInfinitePlace(p::ExtReElt) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p eq Infinity();
end intrinsic;

intrinsic IsInfinitePlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsInfinitePlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is an infinite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p cmpeq 1/Parent(p).1;
end intrinsic;

intrinsic IsInfinitePlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is an infinite place.}
  return IsInfinite(p) select true else false;
end intrinsic;

intrinsic IsInfinitePlace(p::PlcFunElt) -> BoolElt
{Returns true iff p is an infinite place.}
  return not IsFinite(p);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic InfinitePlaces(F::FldFunRat) -> SeqEnum
{Returns the sequence of infinite places of F.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  return [1/F.1];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic IsFinitePlace(p::RngIntElt) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsFinitePlace(p::FldRatElt) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsFinitePlace(p::Infty) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return false;
end intrinsic;

intrinsic IsFinitePlace(p::ExtReElt) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p ne Infinity();
end intrinsic;

intrinsic IsFinitePlace(p::RngUPolElt) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return true;
end intrinsic;

intrinsic IsFinitePlace(p::FldFunRatUElt) -> BoolElt
{Returns true iff p is a finite place.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p cmpne 1/Parent(p).1;
end intrinsic;

intrinsic IsFinitePlace(p::PlcNumElt) -> BoolElt
{Returns true iff p is a finite place.}
  return IsFinite(p) select true else false;
end intrinsic;

intrinsic IsFinitePlace(p::PlcFunElt) -> BoolElt
{Returns true iff p is a finite place.}
  return IsFinite(p);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic GlobalFieldResidueClassField(p::RngIntElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  return ResidueClassField(p);
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::FldRatElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require IsNonarchimedeanPlace(p) : "Argument 1 is archimedian!"; //cor
  return ResidueClassField(Integers()!p);
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::ExtReElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require IsNonarchimedeanPlace(p) : "Argument 1 is archimedian!"; //cor
  return ResidueClassField(Integers()!p);
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::RngUPolElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require IsNonarchimedeanPlace(p) : "Argument 1 is archimedian!"; //cor
  // let's use the arithmetic of the kernel
  // plus: the following doesn't depend on rationality
  dummy_F := FunctionField(Polynomial([-F.1,1]));
  dummy_p := Place(Factorization(p*MaximalOrder(dummy_F))[1][1]);
  OF := MaximalOrder(F);
  Rp, dummy := GlobalFieldResidueClassField(dummy_p);
  return Rp, map<OF -> Rp | f :-> dummy(f), g :-> OF!(g@@dummy)>;
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::FldFunRatUElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require IsNonarchimedeanPlace(p) : "Argument 1 is archimedian!"; //cor
  if IsInfinitePlace(p) then
    // again: we can only benfit from kernel arithmetics
    dummy_F := FunctionField(Polynomial([-F.1,1]));
    dummy_p := InfinitePlaces(dummy_F)[1];
    OF := ValuationRing(F);
    Rp, dummy := GlobalFieldResidueClassField(dummy_p);
    return Rp, map<OF -> Rp | f :-> dummy(f), g :-> OF!(g@@dummy)>;
  else
    return GlobalFieldResidueClassField(MaximalOrder(GlobalField(p))!p);
  end if;
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::PlcNumElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  require IsNonarchimedeanPlace(p) : "Argument 1 is archimedian!"; //cor
  return ResidueClassField(Ideal(p));
end intrinsic;

intrinsic GlobalFieldResidueClassField(p::PlcFunElt) -> Fld, Map
{Returns the residue class field for the given non-archimedean place.}
  return ResidueClassField(Ideal(p));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlaceNorm(p::Any) -> RngIntElt
{Returns the norm of the place p.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  if IsArchimedeanPlace(p) then
    return 1;
  end if;
  return #GlobalFieldResidueClassField(p);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic GlobalField(p::Any) -> Fld
{Returns the global field the place p belongs to.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  return F;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlacesOver(p::RngIntElt, E::FldNum) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return [Place(f[1]) : f in Factorization(p*MaximalOrder(E))];
end intrinsic;

intrinsic PlacesOver(p::FldRatElt, E::FldNum) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return [Place(f[1]) : f in Factorization(p*MaximalOrder(E))];
end intrinsic;

intrinsic PlacesOver(p::ExtReElt, E::FldNum) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  if p eq Infinity() then
    return PlacesOver(Infinity(), E);
  else
    return PlacesOver(Integers()!p, E);
  end if;
end intrinsic;

intrinsic PlacesOver(p::Infty, E::FldNum) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return InfinitePlaces(E);
end intrinsic;

intrinsic PlacesOver(p::PlcNumElt, E::FldNum) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  require BaseField(E) eq NumberField(p) : "Incompatible arguments!"; //cor
  if IsFinitePlace(p) then
    return [Place(r[1]) : r in Factorization(MaximalOrder(E)!!Ideal(p))];
  else
    return [r[1] : r in Decomposition(E, p)];
  end if;
end intrinsic;

intrinsic PlacesOver(p::RngUPolElt, E::FldFun) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return Decomposition(E, Zeroes(BaseField(E)!p)[1]);
end intrinsic;

intrinsic PlacesOver(p::FldFunRatUElt, E::FldFun) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  test, F := IsPlace(p);
  require test : "Argument 1 is not a place!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return Decomposition(E, Zeroes(BaseField(E)!p)[1]);
end intrinsic;

intrinsic PlacesOver(p::PlcFunElt, E::FldFun) -> SeqEnum
{Returns the set of places of E/F lying over the place p of F.}
  require BaseField(E) eq FunctionField(p) : "Incompatible arguments!"; //cor
  return Decomposition(E, p);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlacesOver(P::SetEnum, E::Fld) -> SeqEnum
{Returns the set of places of E/F lying over the places of F in P.}
  test, F := IsSetOfPlaces(P);
  require test : "Argument 1 is not a set of places!"; //cor
  require BaseField(E) eq F : "Incompatible arguments!"; //cor
  return &cat[PlacesOver(p, E) : p in P];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlacesOver(P::SeqEnum, E::Fld) -> SeqEnum
{Returns the set of places of E/F lying over the places of F in P.}
  test, F := IsSequenceOfPlaces(P);
  require test : "Argument 1 is not a sequence of places!"; //cor
  return PlacesOver(SequenceToSet(P), E);
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlaceUnder(p::PlcNumElt) -> Any
{Returns the place of the base field lying under p.}
  E := NumberField(p);
  F := BaseField(E);
  if IsInfinitePlace(p) then
    for q in InfinitePlaces(F) do
      if p in PlacesOver(q, E) then
        return q;
      end if;
    end for;
  end if;
  q := Ideal(p) meet MaximalOrder(F);
  if IsRationalField(F) then
    return Generator(q);
  else
    return Place(q);
  end if;
end intrinsic;

intrinsic PlaceUnder(p::PlcFunElt) -> Any
{Returns the place of the base field lying under p.}
  E := FunctionField(p);
  F := BaseField(E);
  if IsInfinitePlace(p) then
    for q in InfinitePlaces(F) do
      if p in PlacesOver(q, E) then
        return q;
      end if;
    end for;
  end if;
  q := Ideal(p) meet MaximalOrder(F);
  if IsRationalField(F) then
    // this is a workaround
    return MaximalOrder(F)!Evaluate(Polynomial(Eltseq(q.1)), F.1);
    // the following seems to blow up sometimes just like IsGlobal()
    // return Generator(q);
  else
    return Place(q);
  end if;
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlacesUnder(P::SetEnum) -> SeqEnum
{Returns the set of places of E/F lying under the places of E in P.}
  test, _ := IsSetOfPlaces(P);
  require test : "Argument 1 is not a place set of places!"; //cor
  return [PlaceUnder(p) : p in P];
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic PlacesUnder(P::SeqEnum) -> SeqEnum
{Returns the set of places of E/F lying under the places of E in P.}
  test, _ := IsSequenceOfPlaces(P);
  require test : "Argument 1 is not a place sequence of places!"; //cor
  return PlacesUnder(SequenceToSet(P));
end intrinsic;

/* ------------------------------------------------------------------------ */

intrinsic GlobalParameter(p::RngIntElt) -> FldRatElt
{Returns a uniformizing parameter at p.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return Rationals()!p;
end intrinsic;

intrinsic GlobalParameter(p::FldRatElt) -> FldRatElt
{Returns a uniformizing parameter at p.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p;
end intrinsic;

intrinsic GlobalParameter(p::ExtReElt) -> FldElt
{Returns a uniformizing parameter at p.}
  require IsFinitePlace(p) : "Argument 1 is not a finite place!"; //cor
  return p;
end intrinsic;

intrinsic GlobalParameter(p::RngUPolElt) -> FldFunRatUElt
{Returns a uniformizing parameter at p.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return FieldOfFractions(Parent(p))!p;
end intrinsic;

intrinsic GlobalParameter(p::FldFunRatUElt) -> FldFunRatUElt
{Returns a uniformizing parameter at p.}
  require IsPlace(p) : "Argument 1 is not a place!"; //cor
  return p;
end intrinsic;

intrinsic GlobalParameter(p::PlcNumElt) -> FldElt
{Returns a uniformizing parameter at p.}
  return UniformizingElement(p);
end intrinsic;

intrinsic GlobalParameter(p::PlcFunElt) -> FldFunElt
{Returns a uniformizing parameter at p.}
  return UniformizingElement(p);
end intrinsic;

/* ------------------------------------------------------------------------ */

declare attributes FldRat :
  AdeleRings;

declare attributes FldFunRat :
  AdeleRings;

declare attributes FldNum :
  AdeleRings;

declare attributes FldFun :
  AdeleRings;

intrinsic AdeleRings(F::Fld) -> Assoc
{Returns an associative array of adele rings by precision for the global field F.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  if not assigned F`AdeleRings then
    F`AdeleRings := AssociativeArray(Integers());
  end if;
  return F`AdeleRings;
end intrinsic;

__default_precision := 20;

declare attributes RngAdel :
  Field,
  IdeleGroup,
  CompleteFields,
  Precision,
  DirichletMap,
  Logarithm;

declare attributes RngAdelElt :
  Parent,
  PrincipalComponent,
  NonPrincipalComponents;

declare attributes GrpIdel :
  AdeleRing;

declare attributes GrpIdelElt :
  Parent,
  PrincipalComponent,
  NonPrincipalComponents;

intrinsic AdeleRing(F::Fld : Precision := __default_precision) -> RngAdel
{Returns the adele ring for the given global field and precision.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  require Category(Precision) eq RngIntElt and Precision gt 0 : "Precision parameter invalid!"; //cor
  if not IsDefined(AdeleRings(F), Precision) then
    A := HackobjCreateRaw(RngAdel);
    A`Field := F;
    A`IdeleGroup := HackobjCreateRaw(GrpIdel);
    A`IdeleGroup`AdeleRing := A;
    A`CompleteFields := AssociativeArray(Places(F));
    A`Precision := Precision;
    F`AdeleRings[Precision] := A;
    if Characteristic(F) eq 0 then
      A`DirichletMap := func< x, S | [Log(NormalizedValuation(a, p)) : p in S] where a is A!x >;
      A`Logarithm := func< x | Log(x) >;
    else
      A`DirichletMap := func< x, S | [-Valuation(a, p) : p in S] where a is A!x >;
      A`Logarithm := func< x | Log(#ExactConstantField(F), x) >;
    end if;
  end if;
  return F`AdeleRings[Precision];
end intrinsic;

intrinsic 'eq'(A::RngAdel, B::RngAdel) -> BoolElt
{Returns true iff A equals B, i.e. if GlobalField(A) eq Field(B) and Precision(A) eq Precision(B).}
  return A`Field cmpeq B`Field and A`Precision eq B`Precision;
end intrinsic;

intrinsic 'ne'(A::RngAdel, B::RngAdel) -> BoolElt
{Returns true iff A does not equal B, i.e. if GlobalField(A) ne Field(B) or Precision(A) ne Precision(B).}
  return A`Field cmpne B`Field or A`Precision ne B`Precision;
end intrinsic;

intrinsic HackobjCoerceRngAdel(A::RngAdel, x::Any) -> BoolElt, .
{Tries to coerce x into A.}
  is_coercible, y := IsCoercible(A`Field, x);
  if is_coercible then
    return true, Adele(y : Precision := A`Precision);
  end if;
  case Category(x) :
    when RngAdelElt :
      if x`Parent eq A then
        return true, Adele(x);
      end if;
      if not x`Parent`Field eq BaseField(A`Field) then
        return false;
      end if;
      embedding := Coercion(x`Parent`Field, A`Field);
      pc := embedding(x`PrincipalComponent);
      npc := AssociativeArray(Places(A`Field));
      for p in Keys(x`NonPrincipalComponents) do
        for q in PlacesOver(p, A`Field) do
          c := GetComponent(x, p : ForceEmbedding := false);
          if FieldOfFractions(Parent(c)) cmpeq x`Parent`Field then
            npc[q] := (A`Field)!c;
          else
            _, _, embed := CompleteField(A, q);
            npc[q] := embed(x`NonPrincipalComponents[p]);
          end if;
        end for;
      end for;
      return true, Adele(pc, npc : Precision := A`Precision);
    when GrpIdelElt :
      return HackobjCoerceRngAdel(A, Adele(x));
  end case;
  return false;
end intrinsic;

intrinsic HackobjInRngAdel(x::Any, A::RngAdel) -> BoolElt
{Returns true if and only if x is coercible into A.}
  return IsCoercible(A, x);
end intrinsic;

intrinsic HackobjHashRngAdel(A::RngAdel) -> RngIntElt
{Returns a hash value for A.}
  return Hash(A`Field) + Hash(A`Precision);
end intrinsic;

intrinsic HackobjPrintRngAdel(A::RngAdel, level::MonStgElt)
{Prints information about the adele ring A at the specified level.}
  case level :
    when "Minimal" : print "Adele Ring";
    when "Maximal" :
      printf "Adele Ring of precision %o over %o\n", A`Precision, A`Field;
      if not IsEmpty(Keys(A`CompleteFields)) then
        print "constructed complete fields:";
        for p in Keys(A`CompleteFields) do
          print "----- local field -----";
          print "the place";
          printf "%o\n", p;
          print "is associated with";
          printf "%o\n", A`CompleteFields[p];
          print "----- ----- ----- -----";
        end for;
      end if;
    else
      printf "Adele Ring of precision %o over %o\n", A`Precision, A`Field;
  end case;
end intrinsic;

intrinsic GlobalField(A::RngAdel) -> Fld
{Returns the field associated with this adele ring.}
  return A`Field;
end intrinsic;

intrinsic IdeleGroup(A::RngAdel) -> GrpIdel
{Returns the idele group associated with this adele ring.}
  return A`IdeleGroup;
end intrinsic;

intrinsic CompleteFields(A::RngAdel) -> Assoc
{Returns the associative array of local fields by place.}
  return A`CompleteFields;
end intrinsic;

intrinsic Precision(A::RngAdel) -> RngIntElt
{Returns the precision of the given adele ring.}
  return A`Precision;
end intrinsic;

intrinsic IdeleGroup(F::Fld : Precision := __default_precision) -> GrpIdel
{Returns the idele group for the given global field and precision.}
  require IsGlobalField(F) : "Argument 1 is not a global field!"; //cor
  require Category(Precision) eq RngIntElt and Precision gt 0 : "Precision parameter invalid!"; //cor
  if not IsDefined(AdeleRings(F), Precision) then
    A := HackobjCreateRaw(RngAdel);
    A`Field := F;
    A`IdeleGroup := HackobjCreateRaw(GrpIdel);
    A`IdeleGroup`AdeleRing := A;
    A`CompleteFields := AssociativeArray(Places(F));
    A`Precision := Precision;
    F`AdeleRings[Precision] := A;
    if Characteristic(F) eq 0 then
      A`DirichletMap := func< x, S | [Log(NormalizedValuation(a, p)) : p in S] where a is A!x >;
      A`Logarithm := func< x | Log(x) >;
    else
      A`DirichletMap := func< x, S | [-Valuation(a, p) : p in S] where a is A!x >;
      A`Logarithm := func< x | Log(#ConstantField(F), x) >;
    end if;
  end if;
  return F`AdeleRings[Precision]`IdeleGroup;
end intrinsic;

intrinsic 'eq'(I::GrpIdel, J::GrpIdel) -> BoolElt
{Returns true iff I equals J.}
  return I`AdeleRing eq J`AdeleRing;
end intrinsic;

intrinsic 'ne'(I::GrpIdel, J::GrpIdel) -> BoolElt
{Returns true iff I does not equal J.}
  return I`AdeleRing ne J`AdeleRing;
end intrinsic;

intrinsic HackobjCoerceGrpIdel(I::GrpIdel, x::Any) -> BoolElt, .
{Internal.}
  A := I`AdeleRing;
  is_coercible, y := IsCoercible(A`Field, x);
  if is_coercible then
    return true, Idele(y : Precision := A`Precision);
  end if;
  case Category(x) :
    when GrpIdelElt :
      if x`Parent eq I then
        return true, Idele(x);
      end if;
      if not x`Parent`Field eq BaseField(A`Field) then
        return false;
      end if;
      embedding := Coercion(x`Parent`Field, A`Field);
      pc := embedding(x`PrincipalComponent);
      npc := AssociativeArray(Places(A`Field));
      for p in Keys(x`NonPrincipalComponents) do
        for q in PlacesOver(p, A`Field) do
          c := GetComponent(x, p : ForceEmbedding := false);
          if FieldOfFractions(Parent(c)) cmpeq x`Parent`Field then
            npc[q] := (A`Field)!c;
          else
            _, _, embed := CompleteField(A, q);
            npc[q] := embed(x`NonPrincipalComponents[p]);
          end if;
        end for;
      end for;
      return true, Idele(pc, npc : Precision := A`Precision);
    when RngAdelElt :
      return HackobjCoerceGrpIdel(I, Idele(x));
    else
      return false;
  end case;
end intrinsic;

intrinsic HackobjInGrpIdel(x::Any, I::GrpIdel) -> BoolElt
{Internal.}
  return IsCoercible(I, x);
end intrinsic;

intrinsic HackobjHashGrpIdel(I::GrpIdel) -> RngIntElt
{Internal.}
  A := I`AdeleRing;
  return Hash(A`Field) + Hash(A`Precision) + 1;
end intrinsic;

intrinsic HackobjPrintGrpIdel(I::GrpIdel, level::MonStgElt)
{Internal.}
  A := I`AdeleRing;
  case level :
    when "Minimal" : print "Idele Group";
    when "Maximal" :
      if not IsEmpty(Keys(A`CompleteFields)) then
        print "known local fields:";
        for p in Keys(A`CompleteFields) do
          print "----- local field -----";
          print "the place";
          printf "%o\n", p;
          print "is associated with";
          printf "%o\n", A`CompleteFields[p];
          print "----- ----- ----- -----";
        end for;
      end if;
    else printf "Idele Group of precision %o over %o\n", A`Precision, A`Field ;
  end case;
end intrinsic;

intrinsic AdeleRing(I::GrpIdel) -> RngAdel
{Returns the adele ring associated with this idele group.}
  return I`AdeleRing;
end intrinsic;

intrinsic GlobalField(I::GrpIdel) -> Fld
{Returns the field associated with this idele group.}
  return I`AdeleRing`Field;
end intrinsic;

intrinsic CompleteFields(I::GrpIdel) -> Assoc
{Returns the associative array of local fields by place.}
  return I`AdeleRing`CompleteFields;
end intrinsic;

intrinsic Precision(I::GrpIdel) -> RngIntElt
{Returns the precision of the given idele group.}
  return I`AdeleRing`Precision;
end intrinsic;

// explicit copy constructor, otherwise adeles would share their non-principal components
// after an assignment
intrinsic Copy(A::Assoc) -> Assoc
{Returns a copy of A.}
  B := AssociativeArray(Universe(A));
  for key in Keys(A) do
    B[key] := A[key];
  end for;
  return B;
end intrinsic;

intrinsic Adele(pc::RngElt : Precision := __default_precision) -> RngAdelElt
{Returns the adele of given precision and principal component.}
  F := FieldOfFractions(Parent(pc));
  require IsGlobalField(F) : "Argument 1 is not an element of a global field!"; //cor
  a := HackobjCreateRaw(RngAdelElt);
  a`Parent := AdeleRing(F : Precision := Precision);
  a`PrincipalComponent := F!pc;
  a`NonPrincipalComponents := AssociativeArray(Places(F));
  return a;
end intrinsic;

intrinsic Adele(pc::RngElt, npc::Assoc : Precision := __default_precision) -> RngAdelElt
{Returns the adele of given precision and components.}
  F := FieldOfFractions(Parent(pc));
//   require IsGlobalField(F) : "Argument 1 is not contained in a global field!";
  a := Adele(pc : Precision := Precision);
  for p in Keys(npc) do
    SetComponent(~a, p, npc[p]);
  end for;
  return a;
end intrinsic;

intrinsic Adele(pc::RngElt, npc::List : Precision := __default_precision) -> RngAdelElt
{Returns the adele of given precision and components.}
  F := FieldOfFractions(Parent(pc));
  require IsGlobalField(F) : "Argument 1 is not contained in a global field!"; //cor
  a := Adele(pc : Precision := Precision);
  for c in npc do
    SetComponent(~a, c[1], c[2]);
  end for;
  return a;
end intrinsic;

intrinsic Adele(a::RngAdelElt) -> RngAdelElt
{Returns a copy of the given adele.}
  b := HackobjCreateRaw(RngAdelElt);
  b`Parent := a`Parent;
  b`PrincipalComponent := a`PrincipalComponent;
  b`NonPrincipalComponents := Copy(a`NonPrincipalComponents);
  return b;
end intrinsic;

intrinsic Adele(i::GrpIdelElt) -> RngAdelElt
{Returns a copy of the given idele as an adele.}
  b := HackobjCreateRaw(RngAdelElt);
  b`Parent := i`Parent`AdeleRing;
  b`PrincipalComponent := i`PrincipalComponent;
  b`NonPrincipalComponents := Copy(i`NonPrincipalComponents);
  return b;
end intrinsic;

intrinsic HackobjPrintRngAdelElt(a::RngAdelElt, level::MonStgElt)
{Internal.}
  A := a`Parent;
  printf "Adele of precision %o of %o\n", Precision(A), GlobalField(A);
  printf "+" cat "-"^78 cat "\n";
  printf "principal component: %o\n", PrincipalComponent(a);
  printf "+" cat "-"^78 cat "\n";
  for p in NonPrincipalPlaces(a) do
    component := GetComponent(a, p : ForceEmbedding := false);
    embedded := not IsExact(a, p);
    printf "non-principal %o component for place %o: %o\n", embedded select "embedded" else "non-embedded", p, component;
    printf "+" cat "-"^78 cat "\n";
  end for;
end intrinsic;

intrinsic HackobjParentRngAdelElt(a::RngAdelElt) -> RngAdel
{Internal.}
  return a`Parent;
end intrinsic;

intrinsic PrincipalComponent(a::RngAdelElt) -> FldElt
{Retuns the principal component of the given adele.}
  return a`PrincipalComponent;
end intrinsic;

intrinsic NonPrincipalComponents(a::RngAdelElt) -> Assoc
{Retuns the associative array of nonprincipal components of the given adele.}
  return Copy(a`NonPrincipalComponents);
end intrinsic;

intrinsic NonPrincipalPlaces(a::RngAdelElt) -> SetEnum
{Retuns the set of nonprincipal places of the given adele.}
  return Keys(a`NonPrincipalComponents);
end intrinsic;

intrinsic GlobalField(a::RngAdelElt) -> FldRat
{Returns the field associated with this adele.}
  return a`Parent`Field;
end intrinsic;

intrinsic Precision(a::RngAdelElt) -> RngIntElt
{Returns the precision of the given adele.}
  return a`Parent`Precision;
end intrinsic;

intrinsic Idele(pc::RngElt : Precision := __default_precision) -> GrpIdelElt
{Returns the idele of given precision and principal component.}
  F := FieldOfFractions(Parent(pc));
  require IsGlobalField(F) : "Argument 1 is not contained in a global field!"; //cor
  require not IsZero(F!pc) : "Argument 1 is not non-zero!"; //cor
  a := HackobjCreateRaw(GrpIdelElt);
  a`Parent := IdeleGroup(F : Precision := Precision);
  a`PrincipalComponent := F!pc;
  a`NonPrincipalComponents := AssociativeArray(Places(F));
  return a;
end intrinsic;

intrinsic Idele(pc::RngElt, npc::Assoc : Precision := __default_precision) -> GrpIdelElt
{Returns the idele of given precision and components.}
  F := FieldOfFractions(Parent(pc));
  require IsGlobalField(F) : "Argument 1 is not contained in a global field!"; //cor
  require not IsZero(F!pc) : "Argument 1 is not non-zero!"; //cor
  i := Idele(pc : Precision := Precision);
  for p in Keys(npc) do
    SetComponent(~i, p, npc[p]);
  end for;
  return i;
end intrinsic;

intrinsic Idele(pc::RngElt, npc::List : Precision := __default_precision) -> GrpIdelElt
{Returns the idele of given precision and components.}
  F := FieldOfFractions(Parent(pc));
  require IsGlobalField(F) : "Argument 1 is not contained in a global field!"; //cor
  require not IsZero(F!pc) : "Argument 1 is not non-zero!"; //cor
  i := Idele(pc : Precision := Precision);
  for c in npc do
    SetComponent(~i, c[1], c[2]);
  end for;
  return i;
end intrinsic;

intrinsic Idele(i::GrpIdelElt) -> GrpIdelElt
{Returns a copy of the given idele.}
  j := HackobjCreateRaw(GrpIdelElt);
  j`Parent := i`Parent;
  j`PrincipalComponent := i`PrincipalComponent;
  j`NonPrincipalComponents := Copy(i`NonPrincipalComponents);
  return j;
end intrinsic;

intrinsic Idele(i::RngAdelElt) -> GrpIdelElt
{Returns a copy of the given adele as an idele.}
  require not IsZero(i`PrincipalComponent) : "Principal component is zero!"; //cor
  require &and[not IsZero(i`NonPrincipalComponents[p]) : p in Keys(i`NonPrincipalComponents)] : "A nonprincipal component is zero!"; //cor
  j := HackobjCreateRaw(GrpIdelElt);
  j`Parent := i`Parent`IdeleGroup;
  j`PrincipalComponent := i`PrincipalComponent;
  j`NonPrincipalComponents := Copy(i`NonPrincipalComponents);
  return j;
end intrinsic;

intrinsic HackobjPrintGrpIdelElt(i::GrpIdelElt, level::MonStgElt)
{Internal.}
  A := AdeleRing(i`Parent);
  printf "Idele of precision %o of %o\n", Precision(A), GlobalField(A);
  printf "+" cat "-"^78 cat "\n";
  printf "principal component: %o\n", PrincipalComponent(i);
  printf "+" cat "-"^78 cat "\n";
  for p in NonPrincipalPlaces(i) do
    component := GetComponent(i, p : ForceEmbedding := false);
    embedded := not IsExact(i, p);
    printf "non-principal %o component for place %o: %o\n", embedded select "embedded" else "non-embedded", p, component;
    printf "+" cat "-"^78 cat "\n";
  end for;
end intrinsic;

intrinsic HackobjParentGrpIdelElt(i::GrpIdelElt) -> RngAdel
{Internal.}
  return i`Parent;
end intrinsic;

intrinsic PrincipalComponent(i::GrpIdelElt) -> FldElt
{Retuns the principal component of the given idele.}
  return i`PrincipalComponent;
end intrinsic;

intrinsic NonPrincipalComponents(i::GrpIdelElt) -> Assoc
{Retuns the associative array of nonprincipal components of the given idele.}
  return Copy(i`NonPrincipalComponents);
end intrinsic;

intrinsic NonPrincipalPlaces(i::GrpIdelElt) -> SetEnum
{Retuns the set of nonprincipal places of the given adele.}
  return Keys(i`NonPrincipalComponents);
end intrinsic;

intrinsic AdeleRing(i::GrpIdelElt) -> RngAdel
{Returns the adele ring this idele is contained in.}
  return i`Parent`AdeleRing;
end intrinsic;

intrinsic GlobalField(i::GrpIdelElt) -> FldRat
{Returns the field associated with this idele.}
  return i`Parent`AdeleRing`Field;
end intrinsic;

intrinsic Precision(i::GrpIdelElt) -> RngIntElt
{Returns the precision of the given idele.}
  return i`Parent`AdeleRing`Precision;
end intrinsic;

intrinsic CompleteField(A::RngAdel, p::Any) -> Fld, Map, .
{Returns the complete field of A at p, an embedding of the global field into this local field and,
 if the global field is not rational, an embedding of the underlying rational completion into this completion.}

  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(A) cmpeq F : "Incompatible arguments!"; //cor
  require IsAbsoluteGlobalField(F) : "This is not an absolute extension!"; //cor

  if not IsDefined(A`CompleteFields, p) then
    if IsRationalField(F) then
      // rational fields
      if IsZero(Characteristic(F)) then
        if IsFinitePlace(p) then
	  completion, embedding := Completion(F, p);
          AssertAttribute(completion, "DefaultPrecision", Precision(A));
	else
          completion := RealField(Precision(A));
          embedding := Coercion(F, completion);
        end if;
      else
        if IsFinitePlace(p) then
          completion, embedding := Completion(F, p);
        else
          dummy_F := FunctionField(Polynomial([-F.1,1]));
          completion, dummy := Completion(dummy_F, Poles(dummy_F.1)[1]);
          embedding := map<F -> completion | f :-> dummy(dummy_F!f), g :-> F!(g@@dummy) >;
        end if;
        AssertAttribute(completion, "DefaultPrecision", Precision(A));
      end if;
      A`CompleteFields[p] := <completion, embedding>;
    else
      // non-rational fields
      if IsNonarchimedeanPlace(p) then
	completion, embedding := Completion(F, p);
        AssertAttribute(completion, "DefaultPrecision", RamificationIndex(p)*Precision(A));
        base_completion, base_embedding := CompleteField(AdeleRing(RationalSubfield(F) : Precision := Precision(A)), PlaceUnder(p));
	if IsZero(Characteristic(F)) then
	  // these are regular extnsions, no fancy stuff hidden
	  local_embedding := Coercion(base_completion, completion);
	else
	  // mere coercion won't work, since these are FORMAL laurent series rings in a prime
	  // luckily, PlaceUnder(p) is the prime element(!) corresponding to X in base_completion, and PlaceUnder(p) is in F
	  // it is merely a matter of series expansion, or here, substitution
	  pi := embedding(PlaceUnder(p));  // is X in base_completion
	  local_embedding := map<base_completion -> completion | f :-> &+[c[k]*pi^(b+k-1) : k in [1..#c]] where c,b is Eltseq(f)>;
	end if;
      else
        if IsRealPlace(p) then
          completion := RealField(Precision(A));
        else
          completion := ComplexField(Precision(A));
        end if;
        _, i := IsInfinite(p);
        embedding := map<F -> completion | x :->completion!Conjugate(x, i : Precision := Precision(A)) >;
        local_embedding := Coercion(CompleteField(AdeleRing(RationalSubfield(F) : Precision := Precision(A)), PlaceUnder(p)), completion);
      end if;
      A`CompleteFields[p] := <completion, embedding, local_embedding>;
    end if;
  end if;
  entry := A`CompleteFields[p];
  if IsRationalField(F) then
    return entry[1], entry[2];
  else
    return entry[1], entry[2], entry[3];
  end if;
end intrinsic;

intrinsic CompleteField(I::GrpIdel, p::Any) -> Fld, Map, .
{Returns the local field of A at p, an embedding of the global field into the local field and,
 if the global field is not rational, an embedding of the underlying completion.}
  return CompleteField(AdeleRing(I), p);
end intrinsic;

intrinsic IsExact(a::RngAdelElt, p::Any) -> BoolElt
{Returns true iff the p-component of a is exact.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  return FieldOfFractions(Parent(GetComponent(a, p : ForceEmbedding := false))) cmpeq F;
end intrinsic;

intrinsic IsExact(i::GrpIdelElt, p::Any) -> BoolElt
{Returns true iff the p-component of i is exact.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(i) cmpeq F : "Incompatible arguments!"; //cor
  return FieldOfFractions(Parent(GetComponent(i, p : ForceEmbedding := false))) cmpeq F;
end intrinsic;

intrinsic GetComponent(a::RngAdelElt, p::Any : ForceEmbedding := true) -> FldElt
{Returns the component of a at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  require Category(ForceEmbedding) eq BoolElt : "Invalid parameter ForceEmbedding!"; //cor
  component := IsDefined(a`NonPrincipalComponents, p) select a`NonPrincipalComponents[p] else a`PrincipalComponent;
  if ForceEmbedding then
    local_field, embedding, _ := CompleteField(Parent(a), p);
    if Parent(component) cmpne local_field then
      component := embedding(F!component);
    end if;
  end if;
  return component;
end intrinsic;

intrinsic GetComponent(i::GrpIdelElt, p::Any : ForceEmbedding := true) -> FldElt
{Returns the component of i at p.}
  return GetComponent(Adele(i), p : ForceEmbedding := ForceEmbedding);
end intrinsic;

intrinsic SetComponent(~a::RngAdelElt, p::Any, ap::RngElt)
{Sets the component of a at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  if FieldOfFractions(Parent(ap)) cmpne F then
    local_field, embedding, _ := CompleteField(Parent(a), p);
    require FieldOfFractions(Parent(ap)) cmpeq local_field : "Argument 3 is neither in the global nor in the local field!"; //cor
  end if;
  ap := FieldOfFractions(Parent(ap))!ap;
  if FieldOfFractions(Parent(ap)) cmpeq F then
    if ap ne a`PrincipalComponent then
      a`NonPrincipalComponents[p] := ap;
    elif IsDefined(a`NonPrincipalComponents, p) then
      Remove(~a`NonPrincipalComponents, p);
    end if;
  else
    if ap ne embedding(a`PrincipalComponent) then
      a`NonPrincipalComponents[p] := ap;
    elif IsDefined(a`NonPrincipalComponents, p) then
      Remove(~a`NonPrincipalComponents, p);
    end if;
  end if;
end intrinsic;

intrinsic SetComponent(~i::GrpIdelElt, p::Any, ip::RngElt)
{Sets the component of i at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(i) cmpeq F : "Incompatible arguments!"; //cor
  if FieldOfFractions(Parent(ip)) cmpne F then
    local_field, embedding, _ := CompleteField(Parent(i), p);
    require FieldOfFractions(Parent(ip)) cmpeq local_field : "Argument 3 is neither in the global nor in the local field!"; //cor
  end if;
  require not IsZero(ip) : "Argument 3 is zero!"; //cor
  ip := FieldOfFractions(Parent(ip))!ip;
  if FieldOfFractions(Parent(ip)) cmpeq F then
    if ip ne i`PrincipalComponent then
      i`NonPrincipalComponents[p] := ip;
    elif IsDefined(i`NonPrincipalComponents, p) then
      Remove(~i`NonPrincipalComponents, p);
    end if;
  else
    if ip ne embedding(i`PrincipalComponent) then
      i`NonPrincipalComponents[p] := ip;
    elif IsDefined(i`NonPrincipalComponents, p) then
      Remove(~i`NonPrincipalComponents, p);
    end if;
  end if;
end intrinsic;

intrinsic SetComponent(a::RngAdelElt, p::Any, ap::RngElt) -> RngAdelElt
{Returns a copy of a with the component at p set to ap.}
  result := Adele(a);
  SetComponent(~result, p, ap);
  return result;
end intrinsic;

intrinsic SetComponent(i::GrpIdelElt, p::Any, ip::RngElt) -> GrpIdelElt
{Returns a copy of i with the component at p set to ip.}
  result := Idele(i);
  SetComponent(~result, p, ip);
  return result;
end intrinsic;

intrinsic Valuation(a::RngAdelElt, p::Any) -> RngElt
{The exponential valuation of a at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  if IsArchimedeanPlace(p) then
    return -Log(AbsoluteValue(GetComponent(a, p : ForceEmbedding := true)));
  else
    if IsExact(a, p) then
      if IsRationalField(F) and IsInfinitePlace(p) then
        x := GetComponent(a, p : ForceEmbedding := false);
        return Degree(Denominator(x))-Degree(Numerator(x));
      end if;
      return Valuation(GetComponent(a, p : ForceEmbedding := false), IsRationalField(F) select ideal<MaximalOrder(F)|p> else p);
    end if;
    return Valuation(GetComponent(a, p : ForceEmbedding := true));
  end if;
end intrinsic;

intrinsic Valuation(i::GrpIdelElt, p::Any) -> RngElt
{The exponential valuation of a at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(i) cmpeq F : "Incompatible arguments!"; //cor
  if IsArchimedeanPlace(p) then
    return -Log(AbsoluteValue(GetComponent(i, p : ForceEmbedding := true)));
  else
    if IsExact(i, p) then
      if IsRationalField(F) and IsInfinitePlace(p) then
        x := GetComponent(i, p : ForceEmbedding := false);
        return Degree(Denominator(x))-Degree(Numerator(x));
      end if;
      return Valuation(GetComponent(i, p : ForceEmbedding := false), IsRationalField(F) select ideal<MaximalOrder(F)|p> else p);
    end if;
    return Valuation(GetComponent(i, p : ForceEmbedding := true));
  end if;
end intrinsic;

intrinsic NormalizedValuation(a::RngAdelElt, p::Any) -> FldRatElt
{The normalized valuation of a at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  if IsArchimedeanPlace(p) then
    if IsExact(a, p) and GetComponent(a, p : ForceEmbedding := false) in Rationals() then
      x := Rationals()!GetComponent(a, p : ForceEmbedding := false);
    else
      x := GetComponent(a, p : ForceEmbedding := true);
    end if;
    if IsComplexPlace(p) then
      return AbsoluteValue(x)^2;
    end if;
    return AbsoluteValue(x);
  end if;
  return PlaceNorm(p)^-Valuation(a, p);
end intrinsic;

intrinsic NormalizedValuation(i::GrpIdelElt, p::Any) -> FldRatElt
{The normalized valuation of i at p.}
  test, F := IsPlace(p);
  require test : "Argument 2 is not a place!"; //cor
  require GlobalField(i) cmpeq F : "Incompatible arguments!"; //cor
  if IsArchimedeanPlace(p) then
    if IsExact(i, p) and GetComponent(i, p : ForceEmbedding := false) in Rationals() then
      x := Rationals()!GetComponent(i, p : ForceEmbedding := false);
    else
      x := GetComponent(i, p : ForceEmbedding := true);
    end if;
    if IsComplexPlace(p) then
      return AbsoluteValue(x)^2;
    end if;
    return AbsoluteValue(x);
  end if;
  return PlaceNorm(p)^-Valuation(i, p);
end intrinsic;

intrinsic InfiniteFactorization(i::GrpIdelElt) -> SeqEnum
{The infinite part of the factorization of the idele i into pairs of places and exponential valuations.}
  return [<p, Valuation(i, p)> : p in InfinitePlaces(GlobalField(i)) | not IsOne(NormalizedValuation(i, p))];
end intrinsic;

intrinsic FiniteFactorization(i::GrpIdelElt) -> SeqEnum
{The finite part of the factorization of the idele i into pairs of places and exponential valuations.}
  S := NonPrincipalPlaces(i);
  fin := [<p, v> : p in S | IsFinitePlace(p) and not IsZero(v) where v is Valuation(i, p)];
  if IsRationalField(GlobalField(i)) then
    fin cat:= [<f[1], f[2]> : f in Factorization(Numerator(i`PrincipalComponent)) | not f[1] in S];
    fin cat:= [<f[1], -f[2]> : f in Factorization(Denominator(i`PrincipalComponent)) | not f[1] in S];
  else
    fin cat:= [<Place(f[1]), f[2]> : f in Factorization(i`PrincipalComponent*MaximalOrder(GlobalField(i))) | not f[1] in S];
  end if;
  return fin;
end intrinsic;

intrinsic Factorization(i::GrpIdelElt) -> SeqEnum, SeqEnum
{The factorization of the idele i into pairs of places and exponential valuations, seperated into infinite and finite places.}
  return InfiniteFactorization(i), FiniteFactorization(i);
end intrinsic;

intrinsic FiniteSupport(i::GrpIdelElt) -> SetEnum
{The finite support of the idele i.}
  S := Keys(i`NonPrincipalComponents);
  result := {p : p in S | IsFinitePlace(p) and not IsOne(NormalizedValuation(i, p))};
  if IsRationalField(GlobalField(i)) then
    result join:= {f[1] : f in Factorization(Numerator(i`PrincipalComponent)) | not f[1] in S};
    result join:= {f[1] : f in Factorization(Denominator(i`PrincipalComponent)) | not f[1] in S};
  else
    result join:= {Place(f[1]) : f in Factorization(i`PrincipalComponent*MaximalOrder(GlobalField(i))) | not Place(f[1]) in S};
  end if;
  return result;
end intrinsic;

intrinsic InfiniteSupport(i::GrpIdelElt) -> SetEnum
{The infinite support of the idele i.}
  return { p : p in InfinitePlaces(GlobalField(i)) | not IsOne(NormalizedValuation(i, p)) };
end intrinsic;

intrinsic Support(i::GrpIdelElt) -> SetEnum
{The support of the idele i.}
  return InfiniteSupport(i) join FiniteSupport(i);
end intrinsic;

intrinsic Volume(i::GrpIdelElt) -> RngElt
{The volume of the idele i.}
  // principal ideles
  if IsEmpty(Keys(i`NonPrincipalComponents)) then
    return 1;
  end if;
  S := Support(i);
  // remainder
  return &*([1] cat [NormalizedValuation(i, p) : p in S]);
end intrinsic;

intrinsic 'eq'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff a equals b.}
  if Parent(a) ne Parent(b) then
    return false;
  end if;
  if a`PrincipalComponent ne b`PrincipalComponent then
    return false;
  end if;
  for p in Keys(a`NonPrincipalComponents) join Keys(b`NonPrincipalComponents) do
    embedded := not IsExact(a, p) or not IsExact(b, p);
    ap := GetComponent(a, p : ForceEmbedding := embedded);
    bp := GetComponent(b, p : ForceEmbedding := embedded);
    if ap ne bp then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic 'ne'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff a does not equal b.}
  return not a eq b;
end intrinsic;

intrinsic 'eq'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff a equals b.}
  if Parent(a) ne Parent(b) then
    return false;
  end if;
  if a`PrincipalComponent ne b`PrincipalComponent then
    return false;
  end if;
  for p in Keys(a`NonPrincipalComponents) join Keys(b`NonPrincipalComponents) do
    embedded := not IsExact(a, p) or not IsExact(b, p);
    ap := GetComponent(a, p : ForceEmbedding := embedded);
    bp := GetComponent(b, p : ForceEmbedding := embedded);
    if ap ne bp then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic 'ne'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff a does not equal b.}
  return not a eq b;
end intrinsic;

intrinsic NormalizedValuationComparison(a::RngAdelElt, op::Intrinsic, b::RngAdelElt, p::Any) -> BoolElt
{Returns true iff |a|_p op |b|_p where op in \{lt,le,eq,ne,ge,gt\}.}
  test, F := IsPlace(p);
  require test : "Argument 4 is not a place!"; //cor
  require GlobalField(a) cmpeq F : "Incompatible arguments!"; //cor
  require GlobalField(b) cmpeq F : "Incompatible arguments!"; //cor
  require op in {'lt', 'le', 'eq', 'ne', 'ge', 'gt'} : "Argument 2 is invalid!";
  ap := GetComponent(a, p : ForceEmbedding := false);
  bp := GetComponent(b, p : ForceEmbedding := false);
  if IsZero(ap) then
    if IsZero(bp) then
      return op in {'le', 'eq', 'ge'};
    end if;
    return op in {'lt', 'le', 'ne'};
  end if;
  if IsZero(bp) then
    return op in {'ne', 'ge', 'gt'};
  end if;
  if IsArchimedeanPlace(p) and Parent(ap) cmpeq F and Parent(bp) cmpeq F then
    if RationalDegree(F) eq 1 then
      return op(Abs(ap), Abs(bp));
    end if;
    eps := Abs(Conjugate(ap/bp, i : Precision := 2*Precision(a))) - 1 where _,i is IsInfinite(p);
    if Abs(eps) le 10^-Precision(a) then
      return op in {'le', 'eq', 'ge'};
    end if;
    if eps lt 0 then
      return op in {'lt', 'le', 'ne'};
    end if;
    return op in {'gt', 'ge', 'ne'};
  else
    return op(NormalizedValuation(a, p), NormalizedValuation(b, p));
  end if;
end intrinsic;

intrinsic NormalizedValuationComparison(a::RngAdelElt, op::Intrinsic, b::GrpIdelElt, p::Any) -> BoolElt
{Returns true iff |a|_p op |b|_p where op in \{lt,le,eq,ne,ge,gt\}.}
  return NormalizedValuationComparison(a, op, Adele(b), p);
end intrinsic;

intrinsic NormalizedValuationComparison(a::GrpIdelElt, op::Intrinsic, b::RngAdelElt, p::Any) -> BoolElt
{Returns true iff |a|_p op |b|_p where op in \{lt,le,eq,ne,ge,gt\}.}
  return NormalizedValuationComparison(Adele(a), op, b, p);
end intrinsic;

intrinsic NormalizedValuationComparison(a::GrpIdelElt, op::Intrinsic, b::GrpIdelElt, p::Any) -> BoolElt
{Returns true iff |a|_p op |b|_p where op in \{lt,le,eq,ne,ge,gt\}.}
  return NormalizedValuationComparison(Adele(a), op, Adele(b), p);
end intrinsic;

intrinsic NormalizedValuationComparison(a::RngAdelElt, op::Intrinsic, b::RngAdelElt) -> BoolElt
{Compares the valuations of a and b.}
  require Parent(a) eq Parent(b) : "Argument 1 and 3 three are not in the same adele ring!"; //cor
  require op in {'lt','le','eq','ne','ge','gt'} : "Argument 2 is not a valid comparison operator!"; //cor
  
  S := NonPrincipalPlaces(a) join NonPrincipalPlaces(b);
  
  for p in S do
    if not NormalizedValuationComparison(a, op, b, p) then
      return false;
    end if;
  end for;
  
  if IsZero(a`PrincipalComponent-b`PrincipalComponent) then
    return op in {'le', 'eq', 'ge'};
  end if;
  if IsZero(a`PrincipalComponent) then
    return op in {'lt', 'le', 'ne'};
  end if;
  if IsZero(b`PrincipalComponent) then
    return op in {'ne', 'ge', 'gt'};
  end if;
  I := IdeleGroup(Parent(a));
  T := (Support(I!(a`PrincipalComponent)) join Support(I!(b`PrincipalComponent))) diff S;
  if IsEmpty(T) then
    return op in {'le', 'eq', 'ge'};
  end if;
  for p in T do
    if not op(NormalizedValuation(a, p), NormalizedValuation(b, p)) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic NormalizedValuationComparison(a::GrpIdelElt, op::Intrinsic, b::RngAdelElt) -> BoolElt
{Compares the valuations of a and b.}
  return NormalizedValuationComparison(Adele(a), op, b);
end intrinsic;

intrinsic NormalizedValuationComparison(a::RngAdelElt, op::Intrinsic, b::GrpIdelElt) -> BoolElt
{Compares the valuations of a and b.}
  return NormalizedValuationComparison(a, op, Adele(b));
end intrinsic;

intrinsic NormalizedValuationComparison(a::GrpIdelElt, op::Intrinsic, b::GrpIdelElt) -> BoolElt
{Compares the valuations of a and b.}
  return NormalizedValuationComparison(Adele(a), op, Adele(b));
end intrinsic;

intrinsic 'lt'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  return NormalizedValuationComparison(a, 'lt', b);
end intrinsic;

intrinsic 'le'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'le', b);
end intrinsic;

intrinsic 'ge'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'ge', b);
end intrinsic;

intrinsic 'gt'(a::RngAdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  return NormalizedValuationComparison(a, 'gt', b);
end intrinsic;

intrinsic 'lt'(a::GrpIdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  return NormalizedValuationComparison(a, 'lt', b);
end intrinsic;

intrinsic 'le'(a::GrpIdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'le', b);
end intrinsic;

intrinsic 'ge'(a::GrpIdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'ge', b);
end intrinsic;

intrinsic 'gt'(a::GrpIdelElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  return NormalizedValuationComparison(a, 'gt', b);
end intrinsic;

intrinsic 'lt'(a::RngAdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  return NormalizedValuationComparison(a, 'lt', b);
end intrinsic;

intrinsic 'le'(a::RngAdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'le', b);
end intrinsic;

intrinsic 'ge'(a::RngAdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'ge', b);
end intrinsic;

intrinsic 'gt'(a::RngAdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  return NormalizedValuationComparison(a, 'gt', b);
end intrinsic;

intrinsic 'lt'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  return NormalizedValuationComparison(a, 'lt', b);
end intrinsic;

intrinsic 'le'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'le', b);
end intrinsic;

intrinsic 'ge'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  return NormalizedValuationComparison(a, 'ge', b);
end intrinsic;

intrinsic 'gt'(a::GrpIdelElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  return NormalizedValuationComparison(a, 'gt', b);
end intrinsic;

intrinsic 'lt'(a::RngElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) lt b;
end intrinsic;

intrinsic 'le'(a::RngElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) le b;
end intrinsic;

intrinsic 'ge'(a::RngElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) ge b;
end intrinsic;

intrinsic 'gt'(a::RngElt, b::RngAdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) gt b;
end intrinsic;

intrinsic 'lt'(a::RngAdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a lt Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'le'(a::RngAdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a le Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'ge'(a::RngAdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a ge Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'gt'(a::RngAdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a gt Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'lt'(a::RngElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) lt b;
end intrinsic;

intrinsic 'le'(a::RngElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) le b;
end intrinsic;

intrinsic 'ge'(a::RngElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) ge b;
end intrinsic;

intrinsic 'gt'(a::RngElt, b::GrpIdelElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  require FieldOfFractions(Parent(a)) cmpeq GlobalField(b) : "Incompatible arguments!"; //cor
  return Adele(a : Precision := Precision(b)) gt b;
end intrinsic;

intrinsic 'lt'(a::GrpIdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a lt Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'le'(a::GrpIdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are less than or equal to those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a le Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'ge'(a::GrpIdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than or equal to those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a ge Adele(b : Precision := Precision(a));
end intrinsic;

intrinsic 'gt'(a::GrpIdelElt, b::RngElt) -> BoolElt
{Returns true iff the normalized valuations of a are greater than those of b for all places.}
  require FieldOfFractions(Parent(b)) cmpeq GlobalField(a) : "Incompatible arguments!"; //cor
  return a gt Adele(b : Precision := Precision(a));
end intrinsic;

function binary_inner_operation(a, op, b, cons)
  pc := op(a`PrincipalComponent, b`PrincipalComponent);
  npc := AssociativeArray(Places(GlobalField(a)));
  for p in Keys(a`NonPrincipalComponents) join Keys(b`NonPrincipalComponents) do
    embedded := not IsExact(a, p) or not IsExact(b, p);
    if embedded then
      _, embedding, _ := CompleteField(Parent(a), p);
    else
      embedding := Identity(Parent(GetComponent(a, p : ForceEmbedding := false)));
    end if;
    ap := GetComponent(a, p : ForceEmbedding := embedded);
    bp := GetComponent(b, p : ForceEmbedding := embedded);
    element := op(ap, bp);
    if element ne (embedded select embedding(pc) else pc) then
      npc[p] := element;
    end if;
  end for;
  return cons(pc, npc : Precision := Precision(a));
end function;

intrinsic '+'(a::RngAdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::GrpIdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  require AdeleRing(Parent(a)) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::RngAdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  require Parent(a) eq AdeleRing(Parent(b)) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::GrpIdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::RngElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::RngElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::RngAdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '+'(a::GrpIdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '+', b, Adele);
end intrinsic;

intrinsic '-'(a::RngAdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the difference of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::GrpIdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the difference of a and b.}
  require AdeleRing(Parent(a)) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::RngAdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the difference of a and b.}
  require Parent(a) eq AdeleRing(Parent(b)) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::GrpIdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the difference of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::RngElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::RngElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::RngAdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '-'(a::GrpIdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '-', b, Adele);
end intrinsic;

intrinsic '*'(a::RngAdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the product of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::GrpIdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the product of a and b.}
  require AdeleRing(Parent(a)) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::RngAdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the product of a and b.}
  require Parent(a) eq AdeleRing(Parent(b)) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::GrpIdelElt, b::GrpIdelElt) -> GrpIdelElt
{Returns the product of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Idele);
end intrinsic;

intrinsic '*'(a::RngElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::RngElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::RngAdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '*'(a::GrpIdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '*', b, Adele);
end intrinsic;

intrinsic '/'(a::RngAdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the quotient of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::GrpIdelElt, b::RngAdelElt) -> RngAdelElt
{Returns the quotient of a and b.}
  require AdeleRing(Parent(a)) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::RngAdelElt, b::GrpIdelElt) -> RngAdelElt
{Returns the quotient of a and b.}
  require Parent(a) eq AdeleRing(Parent(b)) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::GrpIdelElt, b::GrpIdelElt) -> GrpIdelElt
{Returns the quotient of a and b.}
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Idele);
end intrinsic;

intrinsic '/'(a::RngElt, b::RngAdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::RngElt, b::GrpIdelElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, a := IsCoercible(Parent(b), a);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::RngAdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Adele);
end intrinsic;

intrinsic '/'(a::GrpIdelElt, b::RngElt) -> RngAdelElt
{Returns the sum of a and b.}
  test, b := IsCoercible(Parent(a), b);
  require test : "Argument 2 is not coercible into the adele ring!"; //cor
  require Parent(a) eq Parent(b) : "The arguments are not in the same adele ring!"; //cor
  return binary_inner_operation(a, '/', b, Idele);
end intrinsic;

function power(b, e, constructor)
  F := GlobalField(b);
  y := constructor(F!1);
  if (e lt 0) then
    x := y/b;
    e := -e;
  else
    x := b;
  end if;
  z := constructor(x);
  while e gt 0 do
    if e mod 2 eq 1 then
      y *:= z;
    end if;
    z *:= z;
    e := e div 2;
  end while;
  return y;
end function;

intrinsic '^'(a::RngAdelElt, n::RngIntElt) -> RngAdelElt
{Returns a to the power of n.}
  require IsCoercible(IdeleGroup(Parent(a)), a) or n ge 0 : "Argument 1 is not invertible!!"; //cor
  return power(a, n, Adele);
end intrinsic;

intrinsic '^'(i::GrpIdelElt, n::RngIntElt) -> GrpIdelElt
{Returns a to the power of n.}
  return power(i, n, Idele);
end intrinsic;

intrinsic UnitGroup(A::RngAdel) -> GrpIdel
{Returns the unit group of the adele ring A, i.e. the idele group.}
  return IdeleGroup(A);
end intrinsic;

intrinsic Divisor(i::GrpIdelElt) -> Any
{Returns the corresponding divisor.}
  F := GlobalField(i);
  case Category(F) :
    when FldRat :
      error "There's currently no support for divisors of the rational field in MAGMA!";
    when FldFunRat :
      return &+(
                {f[2]*Divisor(Zeroes(F!f[1])[1]) : f in FiniteFactorization(i)}
                join {Valuation(i, 1/F.1)*Divisor(Poles(F.1)[1])}
               );
    when FldNum, FldFun :
      fin := {f[2]*Divisor(f[1]) : f in FiniteFactorization(i)};
      inf := {f[2]*Divisor(f[1]) : f in InfiniteFactorization(i) | IsNonarchimedeanPlace(f[1])};
      return &+(fin join inf join {Divisor(F!1)});
  end case;
end intrinsic;

intrinsic Ideal(i::GrpIdelElt) -> Any
{Returns the corresponding ideal.}
  F := GlobalField(i);
  OF := MaximalOrder(F);
  f := FiniteFactorization(i);
  if IsEmpty(f) then
    return OF;
  else
    return &*[(IsRationalField(F) select ideal<OF|c[1]> else Ideal(c[1]))^c[2] : c in f];
  end if;
end intrinsic;

intrinsic Enumerate(b::RngAdelElt, callback::UserProgram) -> SetEnum, BoolElt
{internal}
  is_idele, b := IsCoercible(IdeleGroup(Parent(b)), b);
  if not is_idele then
    // there's a zero component!
    result, _ := callback(GlobalField(b)!0, {});
    return result, true;
  end if;
  return Enumerate(b, callback);
end intrinsic;

intrinsic Enumerate(b::GrpIdelElt, callback::UserProgram) -> SetEnum, BoolElt
{internal}
  A := AdeleRing(b);
  F := GlobalField(b);
  result := [];
  case Category(F) :
    when FldRat :
      minimum := &*({ f[1]^f[2] : f in FiniteFactorization(b)} join {1});
      for x in [0..Floor(NormalizedValuation(b, Infinity()) / minimum)+1] do
        for sign in (x eq F!0 select {0} else {1,-1}) do
          element := F!sign*x*minimum;
          if element le b then
            result, done := callback(element, result);
            if done then
              return result, false;
            end if;
          end if;
        end for;
      end for;
    when FldFunRat, FldFun :
      // simple
      M, m := RiemannRochSpace(-Divisor(b));
      for x in M do
	result, done := callback(F!m(x), result);
	if done then
	  return result, false;
	end if;
      end for;
    when FldNum :

      // we'll consider the Minkowski lattice and calculate
      // upper bound for the coordinates using the (inverse) basis matrix
      // ShortVectorsProcess() etc. is much slower!

      // taken from AlgQuat/enumerate.m, John Voigt, 2006

      //////////////////////////////////////////////////////////////////////////////
      //
      // Enumerative Algorithms for Quadratic Forms and Quaternion Algebras
      // April 2006, John Voight
      //
      //////////////////////////////////////////////////////////////////////////////

      // make I the integral ideal
      if IsEmpty(FiniteSupport(b)) then
        I := MaximalOrder(F);
        denom := 1;
      else
        I := &*{Ideal(f[1])^f[2] : f in FiniteFactorization(b)};
        denom := Denominator(I);
      end if;
      I := MaximalOrder(F)!!(denom*I);
      Ibasis := Basis(I);

      // and consider the minkowski lattice
      L, l := MinkowskiLattice(I : Precision := Precision(b));

      // now fix the archimedean bounds for the integral ideal
      B := [ denom*NormalizedValuation(b, p) : p in RealPlaces(F)];
      S := ComplexPlaces(F);
      // we have to take care of Sqrt(2) in the traditional mapping, as well as of the square for complex places
      B cat:= &cat[ [ v, v ] : v in {denom*Sqrt(2*NormalizedValuation(b, p))}, p in S];

      // equality is always a problem for representations of real numbers
      // this one uses a rather enormous estimate
      eps := 10^(-Precision(b) div 2);

      // preconditiong: LLL-reduce the lattice basis
      LL, T := LLL(L);
      LLbasis := Basis(LL);

      // the rank of our lattice
      d := RationalDegree(F);

      // inverse basis matrix, i.e. LLL-reduced basis :-> canonical basis
      Minv := Matrix(Basis(LL))^(-1);

      // by Minv, the d-dimensional compact interval B is transformed into
      // the corresponding parallelepiped in coordinate space.
      // in order to find upper bound for the coordinates, we'll consider the
      // 2^d vertices under this transformation. as in fincke-pohst, complexity
      // is reduced by considering symmetry using the first coordinate
      Bs := [];
      RR := BaseRing(L);
      for nu in CartesianPower([-1,1],d-1) do
        Append(~Bs, Eltseq(Matrix(RR,1,d,[B[1]] cat [nu[i]*B[i+1] : i in [1..d-1]])*Minv));
      end for;
      // now use the axis-parallel box which contains this parallelepiped
      C := [ Floor(Max([Abs(Bs[i][j]) : i in [1..#Bs]])+eps) : j in [1..d] ];

      // set up an enumeration for the coordinates using the upper bounds C
      coords := [0 : i in [1..d]];
      function Increment(aa);
        if #aa eq 1 or aa[1] lt C[d-#aa+1] then
          aa[1] +:= 1;
          return aa;
        else
          return  [-C[d-#aa+1]] cat ($$)(aa[2..#aa]);
        end if;
      end function;

      // and now enumerate the field elements
      while coords[d] le C[d] do  // once the last coordinate has reached it's upper bound, we're completely done
        v := &+[ coords[i]*LLbasis[i] : i in [1..d]]; // take the vector in minkowski space
        if &and[ Abs(v[i]) le B[i]+eps : i in [1..d]] then // ...and check the archimedean valutions
          // now for the field element
          element := (&+[x[1][i]*(F!Ibasis[i]) where x is Matrix(Integers(),1,d,coords)*T : i in [1..Degree(F)]])/denom;
          result, done := callback(element, result); // another field element (which is skipped here), is given by -element
          if done then
            return result, false;
          end if;
        end if;
        coords := Increment(coords); // go on
      end while;
    end case;

  // complete enumeration
  return result, true;
end intrinsic;

intrinsic Enumerate(a::RngAdelElt,
                    b::GrpIdelElt :
                    StopCardinality := Infinity(),
                    OnlyNonZeroElements := false,
                    StrictLowerBoundPlaces := {},
                    StrictUpperBoundPlaces := {}) -> SetEnum, BoolElt
{Returns up to StopCardinality field elements bounded by the valuations of a as a lower bound and b as an upper bound.}
   require GlobalField(a) cmpeq GlobalField(b) : "Incompatible arguments!";
   require Category(StopCardinality) in {RngIntElt, Infty} and StopCardinality gt 0 : "Invalid StopCardinality parameter!"; //cor
   require Category(OnlyNonZeroElements) eq BoolElt : "Invalid OnlyNonZeroElements parameter!"; //cor
   require IsEmpty(StrictLowerBoundPlaces) or IsSetOfPlaces(StrictLowerBoundPlaces) : "Invalid StrictLowerBoundPlaces parameter!"; //cor
   require IsEmpty(StrictUpperBoundPlaces) or IsSetOfPlaces(StrictUpperBoundPlaces) : "Invalid StrictUpperBoundPlaces parameter!"; //cor
  
  function callback(element, result)
    // sort out 0 if wanted
    if (OnlyNonZeroElements and IsZero(element)) then
      return result, false;
    end if;
    // check lower bound
    if not (a le element) then
      return result, false;
    end if;
    // strict upper bound places
    if &or[NormalizedValuationComparison(Parent(a)!element, 'ge', b, p) : p in StrictUpperBoundPlaces] then
      return result, false;
    end if;
    // strict lower bound places
    if &or[NormalizedValuationComparison(a, 'ge', Parent(a)!element, p) : p in StrictLowerBoundPlaces] then
      return result, false;
    end if;
    // ok, we've got one
    Append(~result, element);
    return result, #result eq StopCardinality;
  end function;

  bound := Idele(b);
  
  // for nonarchimedean (i.e. discret) places, we can alter the upper bound accordingly
  for p in {p : p in StrictUpperBoundPlaces | IsNonarchimedeanPlace(p)} do
    parameter := IsExact(bound, p) // we'll leave it exact
      select GlobalParameter(p) // this is an element of the global field
      else LocalParameter(Parent(bound), p); // ... and this one's a prime element of the local field
    // decrease normalized valution by multiplication with a prime element
    SetComponent(~bound, p, GetComponent(bound, p : ForceEmbedding := false) * parameter);
  end for;

  // enumerate
  return Enumerate(bound, callback);
end intrinsic;

intrinsic Enumerate(b::GrpIdelElt :
                    StopCardinality := Infinity(),
                    OnlyNonZeroElements := false,
                    StrictBoundPlaces := {}) -> SetEnum, BoolElt
{Returns up to StopCardinality field elements bounded by the valuations of b as an upper bound.}
   require Category(StopCardinality) in {RngIntElt, Infty} and StopCardinality gt 0 : "Invalid StopCardinality parameter!"; //cor
   require Category(OnlyNonZeroElements) eq BoolElt : "Invalid OnlyNonZeroElements parameter!"; //cor
   require IsEmpty(StrictBoundPlaces) or IsSetOfPlaces(StrictBoundPlaces) : "Invalid StrictBoundPlaces parameter!"; //cor
  function callback(element, result)
    // sort out 0 for convenience
    if (OnlyNonZeroElements and IsZero(element)) then
      return result, false;
    end if;
    // check strict upper bounds
    if &or[NormalizedValuationComparison(AdeleRing(Parent(b))!element, 'ge', b, p) : p in StrictBoundPlaces] then
      return result, false;
    end if;
    // gotcha
    Append(~result, element);
    return result, #result eq StopCardinality;
  end function;

  bound := Adele(b);

  // again, there's no need to consider a "larger" ideal if we only want a subset (by valuations)
  for p in {p : p in StrictBoundPlaces | IsNonarchimedeanPlace(p)} do
    parameter := IsExact(bound, p) select GlobalParameter(p) else LocalParameter(Parent(bound), p);
    SetComponent(~bound, p, GetComponent(bound, p : ForceEmbedding := false) * parameter);
  end for;

  // do it
  return Enumerate(bound, callback);
end intrinsic;

intrinsic IsPrincipal(a::RngAdelElt) ->  BoolElt, .
{Returns true iff a is a principal adele, and in this case also the generator. CAUTION:
Prinicipality is only checked for the representation, no reconstruction is performed!}
  if IsEmpty(Keys(a`NonPrincipalComponents)) then
    return true, a`PrincipalComponent;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic IsPrincipal(i::GrpIdelElt) ->  BoolElt, .
{Returns true iff i is a principal idele, and in this case also the generator. CAUTION:
Prinicipality is only checked for the representation, no reconstruction is performed!}
  if IsEmpty(Keys(i`NonPrincipalComponents)) then
    return true, i`PrincipalComponent;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::RngIntElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  return UniformizingElement(CompleteField(A, p));
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::Infty) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  F, embedding := CompleteField(A, p);
  return F!Exp(RealField(Precision(A))!-1);
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::RngUPolElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  return UniformizingElement(CompleteField(A, p));
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::FldFunRatUElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  return UniformizingElement(CompleteField(A, p));
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::PlcNumElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  F, embedding := CompleteField(A, p);
  if IsInfinitePlace(p) then
    return F!Exp(RealField(Precision(A))!-1);
  else
    return UniformizingElement(F);
  end if;
end intrinsic;

intrinsic LocalParameter(A::RngAdel, p::PlcFunElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  require GlobalField(A) cmpeq GlobalField(p) : "Incompatible arguments!"; //cor
  require IsPlaceForField(p, GlobalField(p)) : "Argument 2 is not a place representative!"; //cor
  return UniformizingElement(CompleteField(A, p));
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::RngIntElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::Infty) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::RngUPolElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::FldFunRatUElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::PlcNumElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;

intrinsic LocalParameter(I::GrpIdel, p::PlcFunElt) -> RngElt
{Returns a local parameter for the prime place p in the correct local field.}
  return LocalParameter(AdeleRing(I), p);
end intrinsic;
