__modules :=
[
  "adeles.m",
  "lagrange.m"
];

procedure  __attach()
  for module in __modules do
    Attach(module);
  end for;
end procedure;

procedure __detach()
  for module in Reverse(__modules) do
    Detach(module);
  end for;
end procedure;

procedure reload()
  __detach();
  __attach();
end procedure;

__attach();

function dirichlet_map(X, S, precision)
  return Matrix([m(x, S) : x in X]) where m is AdeleRing(GlobalField(S[1]) : Precision := precision)`DirichletMap;
end function;

function s_regulator(units, S, precision)
  assert #units eq #S-1;

  if #units eq 1 then
    return Abs(dirichlet_map(units, S, precision)[1,1]);
  end if;

  return Abs(Determinant(Submatrix(dirichlet_map(units, S, precision), 1, 1, #units, #units)));
end function;

function test(K)
  precision := 30;

  if #InfinitePlaces(K) eq 1 then
    return false;
  end if;

  O := MaximalOrder(K);

  print "--------------------------------------------------------------|";

  tg := Cputime();
  units1 := GlobalFieldIndependentUnits(K);
  tg := Cputime(tg);

  for u in units1 do
    assert IsUnit(O!u);
  end for;

  if Characteristic(K) gt 0 then
    tm := Cputime();
    units2 := IndependentUnits(O);
    tm := Cputime(tm);
  else
    tm := Cputime();
    U, u := IndependentUnits(O);
    tm := Cputime(tm);
    units2 := [u(U.i) : i in [2..#InfinitePlaces(K)]];
  end if;

  U, u := UnitGroup(O);
  fund :=  [u(U.i) : i in [2-fix..#InfinitePlaces(K)-fix] where fix is Characteristic(K) gt 0 and #ExactConstantField(K) eq 2 select 1 else 0];

  regulator := s_regulator(fund, InfinitePlaces(K), precision);
  // class_group := ClassGroup(O);
  class_number := ClassNumber(O);
  discriminant := Discriminant(O);
  Q := RationalSubfield(K);
  chi := Characteristic(K);
  abs_val_disc := chi eq 0 select Abs(discriminant) else #ConstantField(Q)^Degree(discriminant);
  reg1 := s_regulator(units1, InfinitePlaces(K), precision);
  reg2 := s_regulator(units2, InfinitePlaces(K), precision);
  indexg := Round(reg1/regulator);
  // at least for number fields, there's a nasty bug in the built-in unit group computation (MAGMA)
  // leading to (at least) integral multiples in regulator computation
  // K := NumberField(Polynomial([1,1,0,1,0,1]));
  // Regulator(K);
  // 1.5727420927851952946520177454972652914049233676532522
  // ...and that's wrong ...
  // 0.786371046392597647326008872748
  // is more like it, see
  // http://qaos.math.tu-berlin.de/qaos/query.scm?type=anf&mode=keyword&query=d+%3D+5+and+sr+%3D+1&action=Go&order=disc&count=186906
  //assert Abs(indexg - reg1/regulator) le 10^(-precision div 2);
  indexm := Round(reg2/regulator);
  //assert Abs(indexm - reg2/regulator) le 10^(-precision div 2);
  f := DefiningPolynomial(K);
  P<X> := Parent(f);
  if chi gt 0 then
    R<t> := Parent(discriminant);
    GF<w> := CoefficientRing(R);
  end if;
  
  printf "rational field:                Q = %o |\n", Characteristic(K) eq 0 
    select "\\mathbb{Q}" 
    else Sprintf("\\mathbb{F}_{%o}\\left[t\\right]", IsPrime(#ConstantField(Q))
      select chi
      else Sprintf("%o^%o", chi, Round(Log(chi, #ConstantField(Q)))));
  printf "defining polynomial:           f = %o |\n", f;
  factors, unit := Factorization(discriminant);
  tmp := IsOne(unit) select "" else Sprintf("%o", unit);
  for factor in factors do
    tmp cat:= Sprintf("%o %o%o", tmp eq "" select "" else "\\cdot", chi gt 0 and factor[1] ne Parent(discriminant).1 select Sprintf("\\left(%o\\right)", factor[1]) else factor[1], IsOne(factor[2]) select "" else Sprintf("^%o", factor[2]));
  end for;
  printf "discriminant:                  \\Delta_K = %o |\n", tmp;
  factors, unit := Factorization(abs_val_disc);
  tmp := IsOne(unit) select "" else Sprintf("%o", unit);
  for factor in factors do
    tmp cat:= Sprintf("%o %o%o", tmp eq "" select "" else "\\cdot", factor[1], IsOne(factor[2]) select "" else Sprintf("^%o", factor[2]));
  end for;
  printf "discriminant absolute value:   \\left\\vert\\Delta_K\\right\\vert_\\infty = %o |\n", tmp;
  printf "signature:                     \\mathfrak{S}_K = \\left\\{";
  for p in InfinitePlaces(K) do
    printf "\\left(%o,%o\\right)%o", RamificationIndex(p), InertiaDegree(p), p eq InfinitePlaces(K)[#InfinitePlaces(K)] select "" else ",";
  end for;
  printf "\\right\\} |\n";
  if chi eq 0 then
    tmp := Sprintf(" C_%o", #TorsionUnitGroup(K));
  else
    if #ExactConstantField(K) eq 2 then
      tmp := "";
    else
      tmp := Sprintf(" C_{%o}", IsPrime(#ExactConstantField(Q))
    select chi-1
    else Sprintf("%o^%o-1", chi, Round(Log(chi, #ExactConstantField(Q)))));
    end if;
  end if;
  printf "unit group:                    \\mathfrak{u}_K \\cong %o %o C_{\\infty}%o |\n", tmp, tmp eq "" select "" else "\\times", #InfinitePlaces(K) eq 2 select "" else Sprintf("^%o", #InfinitePlaces(K)-1);
  //tmp := "";
  //for g in Generators(class_group) do
  //  tmp cat:= Sprintf("%o C_%o", tmp eq "" select "" else "\\times", Order(g));
  //end for;
  //printf "class group:                   \\mathfrak{c}_K \\cong %o |\n", tmp eq "" select "C_1" else tmp;
  printf "regulator:                     \\mathfrak{R}_K %o %o |\n", chi eq 0 select "\\approx" else "=", chi gt 0 select regulator else RealField(4)!regulator;
  printf "class number:                  \\mathfrak{h}_K = %o |\n", class_number;
  printf "Magma subgroup index:          \\left(\\mathfrak{u}_K \\colon U_\\text{M} \\right) = %o |\n", indexm;
  printf "Generic subgroup index:        \\left(\\mathfrak{u}_K \\colon U_\\text{G} \\right) = %o |\n", indexg;
  printf "Magma CPU time:                t_\\text{M} = %o |\n", tm;
  printf "Generic CPU time:              t_\\text{G} = %o |\n", tg;
  print "--------------------------------------------------------------|";
  return true;
end function;

print "Use 'reload();' to reattach all custom modules.\n";
