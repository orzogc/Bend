assert cong:
  forall -A: Type
  forall -B: Type
  forall -f: A -> B
  forall -a: A
  forall -b: A
  forall  e: {a == b : A}
  {f(a) == f(b) : B}

def cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}
  {==}

type Nat is Data:
  Z{}
  S{pred: Nat}

type Sigma<-A: Type, -B: @-x: A -> Type> is Type:
  Tuple{fst: A, snd: B(fst)}

assert Pair:
  forall -A: Type
  forall -B: Type
  Type

def Pair(A, B):
  Sigma<A, _ => B>

assert Cpy:
  forall -A: Type
  forall -x: A
  Type

def Cpy(A, x):
  Sigma<A, y => {x == y : A}>

assert Cpyable:
  forall -T: Type
  Type

def Cpyable(T):
  @x: T -> Cpy(T, x) & Cpy(T, x)

assert Equal.cong2:
  forall -A: Type
  forall -B: Type
  forall -C: Type
  forall -f: A -> @y: B -> C
  forall -a: A
  forall -c: A
  forall -b: B
  forall -d: B
  forall ea: {a == c : A}
  forall eb: {b == d : B}
  {f(a)(b) == f(c)(d) : C}

def Equal.cong2(A, B, C, f, a, c, b, d, ea, eb):
  %eb : {f(a)(b) == f(c)(_) : C}
  %ea : {f(a)(b) == f(_)(b) : C}
  {==}

assert add:
  forall a: Nat
  forall b: Nat
  Nat

def add(a, b):
  match a:
    case Z{}:
      b
    case S{a}:
      S{add(a, b)}

assert Nat.cpy:
  forall n: Nat
  Cpy(Nat, n) & Cpy(Nat, n)

assert Nat.cpy.succ:
  forall -p: Nat
  forall c: Cpy(Nat, p) & Cpy(Nat, p)
  Cpy(Nat, S{p}) & Cpy(Nat, S{p})

def Nat.cpy.succ(p, c):
  ((a, ea), (b, eb)) = c
  ((S{a}, cong(Nat, Nat, x => S{x}, p, a, ea)), (S{b}, cong(Nat, Nat, x => S{x}, p, b, eb)))

def Nat.cpy(n):
  match n:
    case Z{}:
      ((Z{}, {==}), (Z{}, {==}))
    case S{p}:
      Nat.cpy.succ(p, Nat.cpy(p))

assert mul:
  forall a: Nat
  forall +b: Nat
  Nat

def mul(a, b):
  match a:
    case Z{}:
      Z{}
    case S{a}:
      add(b, mul(a, b))

assert n0:
  Nat

def n0():
  Z{}

assert n1:
  Nat

def n1():
  S{n0()}

assert n2:
  Nat

def n2():
  S{n1()}

assert n3:
  Nat

def n3():
  S{n2()}

assert n4:
  Nat

def n4():
  S{n3()}

assert n5:
  Nat

def n5():
  S{n4()}

assert n6:
  Nat

def n6():
  S{n5()}

assert n7:
  Nat

def n7():
  S{n6()}

assert n8:
  Nat

def n8():
  S{n7()}

assert n9:
  Nat

def n9():
  S{n8()}

assert n10:
  Nat

def n10():
  S{n9()}

assert n11:
  Nat

def n11():
  S{n10()}

assert n12:
  Nat

def n12():
  S{n11()}

assert n13:
  Nat

def n13():
  S{n12()}

assert n14:
  Nat

def n14():
  S{n13()}

assert n15:
  Nat

def n15():
  S{n14()}

assert n16:
  Nat

def n16():
  S{n15()}

assert n17:
  Nat

def n17():
  S{n16()}

assert n18:
  Nat

def n18():
  S{n17()}

assert n19:
  Nat

def n19():
  S{n18()}

assert n20:
  Nat

def n20():
  S{n19()}

assert n21:
  Nat

def n21():
  S{n20()}

assert n22:
  Nat

def n22():
  S{n21()}

assert n23:
  Nat

def n23():
  S{n22()}

assert n24:
  Nat

def n24():
  S{n23()}

assert n25:
  Nat

def n25():
  S{n24()}

assert n26:
  Nat

def n26():
  S{n25()}

assert n27:
  Nat

def n27():
  S{n26()}

assert n28:
  Nat

def n28():
  S{n27()}

assert n29:
  Nat

def n29():
  S{n28()}

assert n30:
  Nat

def n30():
  S{n29()}

assert n31:
  Nat

def n31():
  S{n30()}

assert n32:
  Nat

def n32():
  S{n31()}

type Duo<-A: Type, -B: Type> is Type:
  Duo{fst: A, snd: B}

assert Tup:
  forall n: Nat
  Type

def Tup(n):
  match n:
    case Z{}:
      Nat
    case S{p}:
      Duo<Nat, Tup(p)>

assert cm0:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm0():
  {==}

assert tv0:
  Tup(n4())

def tv0():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1():
  {==}

assert tv1:
  Tup(n7())

def tv1():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm2:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm2():
  {==}

assert tv2:
  Tup(n10())

def tv2():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm3:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm3():
  {==}

assert tv3:
  Tup(n13())

def tv3():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm4:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm4():
  {==}

assert tv4:
  Tup(n16())

def tv4():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm5:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm5():
  {==}

assert tv5:
  Tup(n19())

def tv5():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm6:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm6():
  {==}

assert tv6:
  Tup(n22())

def tv6():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm7:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm7():
  {==}

assert tv7:
  Tup(n25())

def tv7():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm8:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm8():
  {==}

assert tv8:
  Tup(n28())

def tv8():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm9:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm9():
  {==}

assert tv9:
  Tup(n31())

def tv9():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm10:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm10():
  {==}

assert tv10:
  Tup(n6())

def tv10():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm11:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm11():
  {==}

assert tv11:
  Tup(n9())

def tv11():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm12:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm12():
  {==}

assert tv12:
  Tup(n12())

def tv12():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm13:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm13():
  {==}

assert tv13:
  Tup(n15())

def tv13():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm14:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm14():
  {==}

assert tv14:
  Tup(n18())

def tv14():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm15:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm15():
  {==}

assert tv15:
  Tup(n21())

def tv15():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm16:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm16():
  {==}

assert tv16:
  Tup(n24())

def tv16():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm17:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm17():
  {==}

assert tv17:
  Tup(n27())

def tv17():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm18:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm18():
  {==}

assert tv18:
  Tup(n30())

def tv18():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm19:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm19():
  {==}

assert tv19:
  Tup(n5())

def tv19():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm20:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm20():
  {==}

assert tv20:
  Tup(n8())

def tv20():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm21:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm21():
  {==}

assert tv21:
  Tup(n11())

def tv21():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm22:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm22():
  {==}

assert tv22:
  Tup(n14())

def tv22():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm23:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm23():
  {==}

assert tv23:
  Tup(n17())

def tv23():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm24:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm24():
  {==}

assert tv24:
  Tup(n20())

def tv24():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm25:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm25():
  {==}

assert tv25:
  Tup(n23())

def tv25():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm26:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm26():
  {==}

assert tv26:
  Tup(n26())

def tv26():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm27:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm27():
  {==}

assert tv27:
  Tup(n29())

def tv27():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm28:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm28():
  {==}

assert tv28:
  Tup(n4())

def tv28():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm29:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm29():
  {==}

assert tv29:
  Tup(n7())

def tv29():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm30:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm30():
  {==}

assert tv30:
  Tup(n10())

def tv30():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm31:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm31():
  {==}

assert tv31:
  Tup(n13())

def tv31():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm32:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm32():
  {==}

assert tv32:
  Tup(n16())

def tv32():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm33:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm33():
  {==}

assert tv33:
  Tup(n19())

def tv33():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm34:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm34():
  {==}

assert tv34:
  Tup(n22())

def tv34():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm35:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm35():
  {==}

assert tv35:
  Tup(n25())

def tv35():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm36:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm36():
  {==}

assert tv36:
  Tup(n28())

def tv36():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm37:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm37():
  {==}

assert tv37:
  Tup(n31())

def tv37():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm38:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm38():
  {==}

assert tv38:
  Tup(n6())

def tv38():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm39:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm39():
  {==}

assert tv39:
  Tup(n9())

def tv39():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm40:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm40():
  {==}

assert tv40:
  Tup(n12())

def tv40():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm41:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm41():
  {==}

assert tv41:
  Tup(n15())

def tv41():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm42:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm42():
  {==}

assert tv42:
  Tup(n18())

def tv42():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm43:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm43():
  {==}

assert tv43:
  Tup(n21())

def tv43():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm44:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm44():
  {==}

assert tv44:
  Tup(n24())

def tv44():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm45:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm45():
  {==}

assert tv45:
  Tup(n27())

def tv45():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm46:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm46():
  {==}

assert tv46:
  Tup(n30())

def tv46():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm47:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm47():
  {==}

assert tv47:
  Tup(n5())

def tv47():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm48:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm48():
  {==}

assert tv48:
  Tup(n8())

def tv48():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm49:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm49():
  {==}

assert tv49:
  Tup(n11())

def tv49():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm50:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm50():
  {==}

assert tv50:
  Tup(n14())

def tv50():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm51:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm51():
  {==}

assert tv51:
  Tup(n17())

def tv51():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm52:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm52():
  {==}

assert tv52:
  Tup(n20())

def tv52():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm53:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm53():
  {==}

assert tv53:
  Tup(n23())

def tv53():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm54:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm54():
  {==}

assert tv54:
  Tup(n26())

def tv54():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm55:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm55():
  {==}

assert tv55:
  Tup(n29())

def tv55():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm56:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm56():
  {==}

assert tv56:
  Tup(n4())

def tv56():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm57:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm57():
  {==}

assert tv57:
  Tup(n7())

def tv57():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm58:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm58():
  {==}

assert tv58:
  Tup(n10())

def tv58():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm59:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm59():
  {==}

assert tv59:
  Tup(n13())

def tv59():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm60:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm60():
  {==}

assert tv60:
  Tup(n16())

def tv60():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm61:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm61():
  {==}

assert tv61:
  Tup(n19())

def tv61():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm62:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm62():
  {==}

assert tv62:
  Tup(n22())

def tv62():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm63:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm63():
  {==}

assert tv63:
  Tup(n25())

def tv63():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm64:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm64():
  {==}

assert tv64:
  Tup(n28())

def tv64():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm65:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm65():
  {==}

assert tv65:
  Tup(n31())

def tv65():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm66:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm66():
  {==}

assert tv66:
  Tup(n6())

def tv66():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm67:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm67():
  {==}

assert tv67:
  Tup(n9())

def tv67():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm68:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm68():
  {==}

assert tv68:
  Tup(n12())

def tv68():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm69:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm69():
  {==}

assert tv69:
  Tup(n15())

def tv69():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm70:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm70():
  {==}

assert tv70:
  Tup(n18())

def tv70():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm71:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm71():
  {==}

assert tv71:
  Tup(n21())

def tv71():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm72:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm72():
  {==}

assert tv72:
  Tup(n24())

def tv72():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm73:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm73():
  {==}

assert tv73:
  Tup(n27())

def tv73():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm74:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm74():
  {==}

assert tv74:
  Tup(n30())

def tv74():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm75:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm75():
  {==}

assert tv75:
  Tup(n5())

def tv75():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm76:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm76():
  {==}

assert tv76:
  Tup(n8())

def tv76():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm77:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm77():
  {==}

assert tv77:
  Tup(n11())

def tv77():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm78:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm78():
  {==}

assert tv78:
  Tup(n14())

def tv78():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm79:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm79():
  {==}

assert tv79:
  Tup(n17())

def tv79():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm80:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm80():
  {==}

assert tv80:
  Tup(n20())

def tv80():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm81:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm81():
  {==}

assert tv81:
  Tup(n23())

def tv81():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm82:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm82():
  {==}

assert tv82:
  Tup(n26())

def tv82():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm83:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm83():
  {==}

assert tv83:
  Tup(n29())

def tv83():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm84:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm84():
  {==}

assert tv84:
  Tup(n4())

def tv84():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm85:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm85():
  {==}

assert tv85:
  Tup(n7())

def tv85():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm86:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm86():
  {==}

assert tv86:
  Tup(n10())

def tv86():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm87:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm87():
  {==}

assert tv87:
  Tup(n13())

def tv87():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm88:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm88():
  {==}

assert tv88:
  Tup(n16())

def tv88():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm89:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm89():
  {==}

assert tv89:
  Tup(n19())

def tv89():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm90:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm90():
  {==}

assert tv90:
  Tup(n22())

def tv90():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm91:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm91():
  {==}

assert tv91:
  Tup(n25())

def tv91():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm92:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm92():
  {==}

assert tv92:
  Tup(n28())

def tv92():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm93:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm93():
  {==}

assert tv93:
  Tup(n31())

def tv93():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm94:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm94():
  {==}

assert tv94:
  Tup(n6())

def tv94():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm95:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm95():
  {==}

assert tv95:
  Tup(n9())

def tv95():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm96:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm96():
  {==}

assert tv96:
  Tup(n12())

def tv96():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm97:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm97():
  {==}

assert tv97:
  Tup(n15())

def tv97():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm98:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm98():
  {==}

assert tv98:
  Tup(n18())

def tv98():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm99:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm99():
  {==}

assert tv99:
  Tup(n21())

def tv99():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm100:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm100():
  {==}

assert tv100:
  Tup(n24())

def tv100():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm101:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm101():
  {==}

assert tv101:
  Tup(n27())

def tv101():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm102:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm102():
  {==}

assert tv102:
  Tup(n30())

def tv102():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm103:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm103():
  {==}

assert tv103:
  Tup(n5())

def tv103():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm104:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm104():
  {==}

assert tv104:
  Tup(n8())

def tv104():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm105:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm105():
  {==}

assert tv105:
  Tup(n11())

def tv105():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm106:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm106():
  {==}

assert tv106:
  Tup(n14())

def tv106():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm107:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm107():
  {==}

assert tv107:
  Tup(n17())

def tv107():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm108:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm108():
  {==}

assert tv108:
  Tup(n20())

def tv108():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm109:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm109():
  {==}

assert tv109:
  Tup(n23())

def tv109():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm110:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm110():
  {==}

assert tv110:
  Tup(n26())

def tv110():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm111:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm111():
  {==}

assert tv111:
  Tup(n29())

def tv111():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm112:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm112():
  {==}

assert tv112:
  Tup(n4())

def tv112():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm113:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm113():
  {==}

assert tv113:
  Tup(n7())

def tv113():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm114:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm114():
  {==}

assert tv114:
  Tup(n10())

def tv114():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm115:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm115():
  {==}

assert tv115:
  Tup(n13())

def tv115():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm116:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm116():
  {==}

assert tv116:
  Tup(n16())

def tv116():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm117:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm117():
  {==}

assert tv117:
  Tup(n19())

def tv117():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm118:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm118():
  {==}

assert tv118:
  Tup(n22())

def tv118():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm119:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm119():
  {==}

assert tv119:
  Tup(n25())

def tv119():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm120:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm120():
  {==}

assert tv120:
  Tup(n28())

def tv120():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm121:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm121():
  {==}

assert tv121:
  Tup(n31())

def tv121():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm122:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm122():
  {==}

assert tv122:
  Tup(n6())

def tv122():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm123:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm123():
  {==}

assert tv123:
  Tup(n9())

def tv123():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm124:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm124():
  {==}

assert tv124:
  Tup(n12())

def tv124():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm125:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm125():
  {==}

assert tv125:
  Tup(n15())

def tv125():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm126:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm126():
  {==}

assert tv126:
  Tup(n18())

def tv126():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm127:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm127():
  {==}

assert tv127:
  Tup(n21())

def tv127():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm128:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm128():
  {==}

assert tv128:
  Tup(n24())

def tv128():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm129:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm129():
  {==}

assert tv129:
  Tup(n27())

def tv129():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm130:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm130():
  {==}

assert tv130:
  Tup(n30())

def tv130():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm131:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm131():
  {==}

assert tv131:
  Tup(n5())

def tv131():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm132:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm132():
  {==}

assert tv132:
  Tup(n8())

def tv132():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm133:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm133():
  {==}

assert tv133:
  Tup(n11())

def tv133():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm134:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm134():
  {==}

assert tv134:
  Tup(n14())

def tv134():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm135:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm135():
  {==}

assert tv135:
  Tup(n17())

def tv135():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm136:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm136():
  {==}

assert tv136:
  Tup(n20())

def tv136():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm137:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm137():
  {==}

assert tv137:
  Tup(n23())

def tv137():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm138:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm138():
  {==}

assert tv138:
  Tup(n26())

def tv138():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm139:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm139():
  {==}

assert tv139:
  Tup(n29())

def tv139():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm140:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm140():
  {==}

assert tv140:
  Tup(n4())

def tv140():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm141:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm141():
  {==}

assert tv141:
  Tup(n7())

def tv141():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm142:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm142():
  {==}

assert tv142:
  Tup(n10())

def tv142():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm143:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm143():
  {==}

assert tv143:
  Tup(n13())

def tv143():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm144:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm144():
  {==}

assert tv144:
  Tup(n16())

def tv144():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm145:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm145():
  {==}

assert tv145:
  Tup(n19())

def tv145():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm146:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm146():
  {==}

assert tv146:
  Tup(n22())

def tv146():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm147:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm147():
  {==}

assert tv147:
  Tup(n25())

def tv147():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm148:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm148():
  {==}

assert tv148:
  Tup(n28())

def tv148():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm149:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm149():
  {==}

assert tv149:
  Tup(n31())

def tv149():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm150:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm150():
  {==}

assert tv150:
  Tup(n6())

def tv150():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm151:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm151():
  {==}

assert tv151:
  Tup(n9())

def tv151():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm152:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm152():
  {==}

assert tv152:
  Tup(n12())

def tv152():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm153:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm153():
  {==}

assert tv153:
  Tup(n15())

def tv153():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm154:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm154():
  {==}

assert tv154:
  Tup(n18())

def tv154():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm155:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm155():
  {==}

assert tv155:
  Tup(n21())

def tv155():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm156:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm156():
  {==}

assert tv156:
  Tup(n24())

def tv156():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm157:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm157():
  {==}

assert tv157:
  Tup(n27())

def tv157():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm158:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm158():
  {==}

assert tv158:
  Tup(n30())

def tv158():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm159:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm159():
  {==}

assert tv159:
  Tup(n5())

def tv159():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm160:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm160():
  {==}

assert tv160:
  Tup(n8())

def tv160():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm161:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm161():
  {==}

assert tv161:
  Tup(n11())

def tv161():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm162:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm162():
  {==}

assert tv162:
  Tup(n14())

def tv162():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm163:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm163():
  {==}

assert tv163:
  Tup(n17())

def tv163():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm164:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm164():
  {==}

assert tv164:
  Tup(n20())

def tv164():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm165:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm165():
  {==}

assert tv165:
  Tup(n23())

def tv165():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm166:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm166():
  {==}

assert tv166:
  Tup(n26())

def tv166():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm167:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm167():
  {==}

assert tv167:
  Tup(n29())

def tv167():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm168:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm168():
  {==}

assert tv168:
  Tup(n4())

def tv168():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm169:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm169():
  {==}

assert tv169:
  Tup(n7())

def tv169():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm170:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm170():
  {==}

assert tv170:
  Tup(n10())

def tv170():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm171:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm171():
  {==}

assert tv171:
  Tup(n13())

def tv171():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm172:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm172():
  {==}

assert tv172:
  Tup(n16())

def tv172():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm173:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm173():
  {==}

assert tv173:
  Tup(n19())

def tv173():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm174:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm174():
  {==}

assert tv174:
  Tup(n22())

def tv174():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm175:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm175():
  {==}

assert tv175:
  Tup(n25())

def tv175():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm176:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm176():
  {==}

assert tv176:
  Tup(n28())

def tv176():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm177:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm177():
  {==}

assert tv177:
  Tup(n31())

def tv177():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm178:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm178():
  {==}

assert tv178:
  Tup(n6())

def tv178():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm179:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm179():
  {==}

assert tv179:
  Tup(n9())

def tv179():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm180:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm180():
  {==}

assert tv180:
  Tup(n12())

def tv180():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm181:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm181():
  {==}

assert tv181:
  Tup(n15())

def tv181():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm182:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm182():
  {==}

assert tv182:
  Tup(n18())

def tv182():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm183:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm183():
  {==}

assert tv183:
  Tup(n21())

def tv183():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm184:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm184():
  {==}

assert tv184:
  Tup(n24())

def tv184():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm185:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm185():
  {==}

assert tv185:
  Tup(n27())

def tv185():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm186:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm186():
  {==}

assert tv186:
  Tup(n30())

def tv186():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm187:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm187():
  {==}

assert tv187:
  Tup(n5())

def tv187():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm188:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm188():
  {==}

assert tv188:
  Tup(n8())

def tv188():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm189:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm189():
  {==}

assert tv189:
  Tup(n11())

def tv189():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm190:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm190():
  {==}

assert tv190:
  Tup(n14())

def tv190():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm191:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm191():
  {==}

assert tv191:
  Tup(n17())

def tv191():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm192:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm192():
  {==}

assert tv192:
  Tup(n20())

def tv192():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm193:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm193():
  {==}

assert tv193:
  Tup(n23())

def tv193():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm194:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm194():
  {==}

assert tv194:
  Tup(n26())

def tv194():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm195:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm195():
  {==}

assert tv195:
  Tup(n29())

def tv195():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm196:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm196():
  {==}

assert tv196:
  Tup(n4())

def tv196():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm197:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm197():
  {==}

assert tv197:
  Tup(n7())

def tv197():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm198:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm198():
  {==}

assert tv198:
  Tup(n10())

def tv198():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm199:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm199():
  {==}

assert tv199:
  Tup(n13())

def tv199():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm200:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm200():
  {==}

assert tv200:
  Tup(n16())

def tv200():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm201:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm201():
  {==}

assert tv201:
  Tup(n19())

def tv201():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm202:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm202():
  {==}

assert tv202:
  Tup(n22())

def tv202():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm203:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm203():
  {==}

assert tv203:
  Tup(n25())

def tv203():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm204:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm204():
  {==}

assert tv204:
  Tup(n28())

def tv204():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm205:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm205():
  {==}

assert tv205:
  Tup(n31())

def tv205():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm206:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm206():
  {==}

assert tv206:
  Tup(n6())

def tv206():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm207:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm207():
  {==}

assert tv207:
  Tup(n9())

def tv207():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm208:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm208():
  {==}

assert tv208:
  Tup(n12())

def tv208():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm209:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm209():
  {==}

assert tv209:
  Tup(n15())

def tv209():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm210:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm210():
  {==}

assert tv210:
  Tup(n18())

def tv210():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm211:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm211():
  {==}

assert tv211:
  Tup(n21())

def tv211():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm212:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm212():
  {==}

assert tv212:
  Tup(n24())

def tv212():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm213:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm213():
  {==}

assert tv213:
  Tup(n27())

def tv213():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm214:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm214():
  {==}

assert tv214:
  Tup(n30())

def tv214():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm215:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm215():
  {==}

assert tv215:
  Tup(n5())

def tv215():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm216:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm216():
  {==}

assert tv216:
  Tup(n8())

def tv216():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm217:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm217():
  {==}

assert tv217:
  Tup(n11())

def tv217():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm218:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm218():
  {==}

assert tv218:
  Tup(n14())

def tv218():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm219:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm219():
  {==}

assert tv219:
  Tup(n17())

def tv219():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm220:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm220():
  {==}

assert tv220:
  Tup(n20())

def tv220():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm221:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm221():
  {==}

assert tv221:
  Tup(n23())

def tv221():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm222:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm222():
  {==}

assert tv222:
  Tup(n26())

def tv222():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm223:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm223():
  {==}

assert tv223:
  Tup(n29())

def tv223():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm224:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm224():
  {==}

assert tv224:
  Tup(n4())

def tv224():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm225:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm225():
  {==}

assert tv225:
  Tup(n7())

def tv225():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm226:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm226():
  {==}

assert tv226:
  Tup(n10())

def tv226():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm227:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm227():
  {==}

assert tv227:
  Tup(n13())

def tv227():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm228:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm228():
  {==}

assert tv228:
  Tup(n16())

def tv228():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm229:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm229():
  {==}

assert tv229:
  Tup(n19())

def tv229():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm230:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm230():
  {==}

assert tv230:
  Tup(n22())

def tv230():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm231:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm231():
  {==}

assert tv231:
  Tup(n25())

def tv231():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm232:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm232():
  {==}

assert tv232:
  Tup(n28())

def tv232():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm233:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm233():
  {==}

assert tv233:
  Tup(n31())

def tv233():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm234:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm234():
  {==}

assert tv234:
  Tup(n6())

def tv234():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm235:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm235():
  {==}

assert tv235:
  Tup(n9())

def tv235():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm236:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm236():
  {==}

assert tv236:
  Tup(n12())

def tv236():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm237:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm237():
  {==}

assert tv237:
  Tup(n15())

def tv237():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm238:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm238():
  {==}

assert tv238:
  Tup(n18())

def tv238():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm239:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm239():
  {==}

assert tv239:
  Tup(n21())

def tv239():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm240:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm240():
  {==}

assert tv240:
  Tup(n24())

def tv240():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm241:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm241():
  {==}

assert tv241:
  Tup(n27())

def tv241():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm242:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm242():
  {==}

assert tv242:
  Tup(n30())

def tv242():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm243:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm243():
  {==}

assert tv243:
  Tup(n5())

def tv243():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm244:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm244():
  {==}

assert tv244:
  Tup(n8())

def tv244():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm245:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm245():
  {==}

assert tv245:
  Tup(n11())

def tv245():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm246:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm246():
  {==}

assert tv246:
  Tup(n14())

def tv246():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm247:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm247():
  {==}

assert tv247:
  Tup(n17())

def tv247():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm248:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm248():
  {==}

assert tv248:
  Tup(n20())

def tv248():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm249:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm249():
  {==}

assert tv249:
  Tup(n23())

def tv249():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm250:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm250():
  {==}

assert tv250:
  Tup(n26())

def tv250():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm251:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm251():
  {==}

assert tv251:
  Tup(n29())

def tv251():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm252:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm252():
  {==}

assert tv252:
  Tup(n4())

def tv252():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm253:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm253():
  {==}

assert tv253:
  Tup(n7())

def tv253():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm254:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm254():
  {==}

assert tv254:
  Tup(n10())

def tv254():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm255:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm255():
  {==}

assert tv255:
  Tup(n13())

def tv255():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm256:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm256():
  {==}

assert tv256:
  Tup(n16())

def tv256():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm257:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm257():
  {==}

assert tv257:
  Tup(n19())

def tv257():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm258:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm258():
  {==}

assert tv258:
  Tup(n22())

def tv258():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm259:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm259():
  {==}

assert tv259:
  Tup(n25())

def tv259():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm260:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm260():
  {==}

assert tv260:
  Tup(n28())

def tv260():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm261:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm261():
  {==}

assert tv261:
  Tup(n31())

def tv261():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm262:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm262():
  {==}

assert tv262:
  Tup(n6())

def tv262():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm263:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm263():
  {==}

assert tv263:
  Tup(n9())

def tv263():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm264:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm264():
  {==}

assert tv264:
  Tup(n12())

def tv264():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm265:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm265():
  {==}

assert tv265:
  Tup(n15())

def tv265():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm266:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm266():
  {==}

assert tv266:
  Tup(n18())

def tv266():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm267:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm267():
  {==}

assert tv267:
  Tup(n21())

def tv267():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm268:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm268():
  {==}

assert tv268:
  Tup(n24())

def tv268():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm269:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm269():
  {==}

assert tv269:
  Tup(n27())

def tv269():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm270:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm270():
  {==}

assert tv270:
  Tup(n30())

def tv270():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm271:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm271():
  {==}

assert tv271:
  Tup(n5())

def tv271():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm272:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm272():
  {==}

assert tv272:
  Tup(n8())

def tv272():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm273:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm273():
  {==}

assert tv273:
  Tup(n11())

def tv273():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm274:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm274():
  {==}

assert tv274:
  Tup(n14())

def tv274():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm275:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm275():
  {==}

assert tv275:
  Tup(n17())

def tv275():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm276:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm276():
  {==}

assert tv276:
  Tup(n20())

def tv276():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm277:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm277():
  {==}

assert tv277:
  Tup(n23())

def tv277():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm278:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm278():
  {==}

assert tv278:
  Tup(n26())

def tv278():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm279:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm279():
  {==}

assert tv279:
  Tup(n29())

def tv279():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm280:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm280():
  {==}

assert tv280:
  Tup(n4())

def tv280():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm281:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm281():
  {==}

assert tv281:
  Tup(n7())

def tv281():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm282:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm282():
  {==}

assert tv282:
  Tup(n10())

def tv282():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm283:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm283():
  {==}

assert tv283:
  Tup(n13())

def tv283():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm284:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm284():
  {==}

assert tv284:
  Tup(n16())

def tv284():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm285:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm285():
  {==}

assert tv285:
  Tup(n19())

def tv285():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm286:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm286():
  {==}

assert tv286:
  Tup(n22())

def tv286():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm287:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm287():
  {==}

assert tv287:
  Tup(n25())

def tv287():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm288:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm288():
  {==}

assert tv288:
  Tup(n28())

def tv288():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm289:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm289():
  {==}

assert tv289:
  Tup(n31())

def tv289():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm290:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm290():
  {==}

assert tv290:
  Tup(n6())

def tv290():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm291:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm291():
  {==}

assert tv291:
  Tup(n9())

def tv291():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm292:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm292():
  {==}

assert tv292:
  Tup(n12())

def tv292():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm293:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm293():
  {==}

assert tv293:
  Tup(n15())

def tv293():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm294:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm294():
  {==}

assert tv294:
  Tup(n18())

def tv294():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm295:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm295():
  {==}

assert tv295:
  Tup(n21())

def tv295():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm296:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm296():
  {==}

assert tv296:
  Tup(n24())

def tv296():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm297:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm297():
  {==}

assert tv297:
  Tup(n27())

def tv297():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm298:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm298():
  {==}

assert tv298:
  Tup(n30())

def tv298():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm299:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm299():
  {==}

assert tv299:
  Tup(n5())

def tv299():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm300:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm300():
  {==}

assert tv300:
  Tup(n8())

def tv300():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm301:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm301():
  {==}

assert tv301:
  Tup(n11())

def tv301():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm302:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm302():
  {==}

assert tv302:
  Tup(n14())

def tv302():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm303:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm303():
  {==}

assert tv303:
  Tup(n17())

def tv303():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm304:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm304():
  {==}

assert tv304:
  Tup(n20())

def tv304():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm305:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm305():
  {==}

assert tv305:
  Tup(n23())

def tv305():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm306:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm306():
  {==}

assert tv306:
  Tup(n26())

def tv306():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm307:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm307():
  {==}

assert tv307:
  Tup(n29())

def tv307():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm308:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm308():
  {==}

assert tv308:
  Tup(n4())

def tv308():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm309:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm309():
  {==}

assert tv309:
  Tup(n7())

def tv309():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm310:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm310():
  {==}

assert tv310:
  Tup(n10())

def tv310():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm311:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm311():
  {==}

assert tv311:
  Tup(n13())

def tv311():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm312:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm312():
  {==}

assert tv312:
  Tup(n16())

def tv312():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm313:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm313():
  {==}

assert tv313:
  Tup(n19())

def tv313():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm314:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm314():
  {==}

assert tv314:
  Tup(n22())

def tv314():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm315:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm315():
  {==}

assert tv315:
  Tup(n25())

def tv315():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm316:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm316():
  {==}

assert tv316:
  Tup(n28())

def tv316():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm317:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm317():
  {==}

assert tv317:
  Tup(n31())

def tv317():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm318:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm318():
  {==}

assert tv318:
  Tup(n6())

def tv318():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm319:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm319():
  {==}

assert tv319:
  Tup(n9())

def tv319():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm320:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm320():
  {==}

assert tv320:
  Tup(n12())

def tv320():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm321:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm321():
  {==}

assert tv321:
  Tup(n15())

def tv321():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm322:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm322():
  {==}

assert tv322:
  Tup(n18())

def tv322():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm323:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm323():
  {==}

assert tv323:
  Tup(n21())

def tv323():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm324:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm324():
  {==}

assert tv324:
  Tup(n24())

def tv324():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm325:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm325():
  {==}

assert tv325:
  Tup(n27())

def tv325():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm326:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm326():
  {==}

assert tv326:
  Tup(n30())

def tv326():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm327:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm327():
  {==}

assert tv327:
  Tup(n5())

def tv327():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm328:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm328():
  {==}

assert tv328:
  Tup(n8())

def tv328():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm329:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm329():
  {==}

assert tv329:
  Tup(n11())

def tv329():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm330:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm330():
  {==}

assert tv330:
  Tup(n14())

def tv330():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm331:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm331():
  {==}

assert tv331:
  Tup(n17())

def tv331():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm332:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm332():
  {==}

assert tv332:
  Tup(n20())

def tv332():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm333:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm333():
  {==}

assert tv333:
  Tup(n23())

def tv333():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm334:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm334():
  {==}

assert tv334:
  Tup(n26())

def tv334():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm335:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm335():
  {==}

assert tv335:
  Tup(n29())

def tv335():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm336:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm336():
  {==}

assert tv336:
  Tup(n4())

def tv336():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm337:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm337():
  {==}

assert tv337:
  Tup(n7())

def tv337():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm338:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm338():
  {==}

assert tv338:
  Tup(n10())

def tv338():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm339:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm339():
  {==}

assert tv339:
  Tup(n13())

def tv339():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm340:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm340():
  {==}

assert tv340:
  Tup(n16())

def tv340():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm341:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm341():
  {==}

assert tv341:
  Tup(n19())

def tv341():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm342:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm342():
  {==}

assert tv342:
  Tup(n22())

def tv342():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm343:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm343():
  {==}

assert tv343:
  Tup(n25())

def tv343():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm344:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm344():
  {==}

assert tv344:
  Tup(n28())

def tv344():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm345:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm345():
  {==}

assert tv345:
  Tup(n31())

def tv345():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm346:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm346():
  {==}

assert tv346:
  Tup(n6())

def tv346():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm347:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm347():
  {==}

assert tv347:
  Tup(n9())

def tv347():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm348:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm348():
  {==}

assert tv348:
  Tup(n12())

def tv348():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm349:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm349():
  {==}

assert tv349:
  Tup(n15())

def tv349():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm350:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm350():
  {==}

assert tv350:
  Tup(n18())

def tv350():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm351:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm351():
  {==}

assert tv351:
  Tup(n21())

def tv351():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm352:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm352():
  {==}

assert tv352:
  Tup(n24())

def tv352():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm353:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm353():
  {==}

assert tv353:
  Tup(n27())

def tv353():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm354:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm354():
  {==}

assert tv354:
  Tup(n30())

def tv354():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm355:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm355():
  {==}

assert tv355:
  Tup(n5())

def tv355():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm356:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm356():
  {==}

assert tv356:
  Tup(n8())

def tv356():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm357:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm357():
  {==}

assert tv357:
  Tup(n11())

def tv357():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm358:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm358():
  {==}

assert tv358:
  Tup(n14())

def tv358():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm359:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm359():
  {==}

assert tv359:
  Tup(n17())

def tv359():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm360:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm360():
  {==}

assert tv360:
  Tup(n20())

def tv360():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm361:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm361():
  {==}

assert tv361:
  Tup(n23())

def tv361():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm362:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm362():
  {==}

assert tv362:
  Tup(n26())

def tv362():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm363:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm363():
  {==}

assert tv363:
  Tup(n29())

def tv363():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm364:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm364():
  {==}

assert tv364:
  Tup(n4())

def tv364():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm365:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm365():
  {==}

assert tv365:
  Tup(n7())

def tv365():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm366:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm366():
  {==}

assert tv366:
  Tup(n10())

def tv366():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm367:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm367():
  {==}

assert tv367:
  Tup(n13())

def tv367():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm368:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm368():
  {==}

assert tv368:
  Tup(n16())

def tv368():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm369:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm369():
  {==}

assert tv369:
  Tup(n19())

def tv369():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm370:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm370():
  {==}

assert tv370:
  Tup(n22())

def tv370():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm371:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm371():
  {==}

assert tv371:
  Tup(n25())

def tv371():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm372:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm372():
  {==}

assert tv372:
  Tup(n28())

def tv372():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm373:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm373():
  {==}

assert tv373:
  Tup(n31())

def tv373():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm374:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm374():
  {==}

assert tv374:
  Tup(n6())

def tv374():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm375:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm375():
  {==}

assert tv375:
  Tup(n9())

def tv375():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm376:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm376():
  {==}

assert tv376:
  Tup(n12())

def tv376():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm377:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm377():
  {==}

assert tv377:
  Tup(n15())

def tv377():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm378:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm378():
  {==}

assert tv378:
  Tup(n18())

def tv378():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm379:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm379():
  {==}

assert tv379:
  Tup(n21())

def tv379():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm380:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm380():
  {==}

assert tv380:
  Tup(n24())

def tv380():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm381:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm381():
  {==}

assert tv381:
  Tup(n27())

def tv381():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm382:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm382():
  {==}

assert tv382:
  Tup(n30())

def tv382():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm383:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm383():
  {==}

assert tv383:
  Tup(n5())

def tv383():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm384:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm384():
  {==}

assert tv384:
  Tup(n8())

def tv384():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm385:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm385():
  {==}

assert tv385:
  Tup(n11())

def tv385():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm386:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm386():
  {==}

assert tv386:
  Tup(n14())

def tv386():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm387:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm387():
  {==}

assert tv387:
  Tup(n17())

def tv387():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm388:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm388():
  {==}

assert tv388:
  Tup(n20())

def tv388():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm389:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm389():
  {==}

assert tv389:
  Tup(n23())

def tv389():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm390:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm390():
  {==}

assert tv390:
  Tup(n26())

def tv390():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm391:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm391():
  {==}

assert tv391:
  Tup(n29())

def tv391():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm392:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm392():
  {==}

assert tv392:
  Tup(n4())

def tv392():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm393:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm393():
  {==}

assert tv393:
  Tup(n7())

def tv393():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm394:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm394():
  {==}

assert tv394:
  Tup(n10())

def tv394():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm395:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm395():
  {==}

assert tv395:
  Tup(n13())

def tv395():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm396:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm396():
  {==}

assert tv396:
  Tup(n16())

def tv396():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm397:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm397():
  {==}

assert tv397:
  Tup(n19())

def tv397():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm398:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm398():
  {==}

assert tv398:
  Tup(n22())

def tv398():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm399:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm399():
  {==}

assert tv399:
  Tup(n25())

def tv399():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm400:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm400():
  {==}

assert tv400:
  Tup(n28())

def tv400():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm401:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm401():
  {==}

assert tv401:
  Tup(n31())

def tv401():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm402:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm402():
  {==}

assert tv402:
  Tup(n6())

def tv402():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm403:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm403():
  {==}

assert tv403:
  Tup(n9())

def tv403():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm404:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm404():
  {==}

assert tv404:
  Tup(n12())

def tv404():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm405:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm405():
  {==}

assert tv405:
  Tup(n15())

def tv405():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm406:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm406():
  {==}

assert tv406:
  Tup(n18())

def tv406():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm407:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm407():
  {==}

assert tv407:
  Tup(n21())

def tv407():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm408:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm408():
  {==}

assert tv408:
  Tup(n24())

def tv408():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm409:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm409():
  {==}

assert tv409:
  Tup(n27())

def tv409():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm410:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm410():
  {==}

assert tv410:
  Tup(n30())

def tv410():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm411:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm411():
  {==}

assert tv411:
  Tup(n5())

def tv411():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm412:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm412():
  {==}

assert tv412:
  Tup(n8())

def tv412():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm413:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm413():
  {==}

assert tv413:
  Tup(n11())

def tv413():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm414:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm414():
  {==}

assert tv414:
  Tup(n14())

def tv414():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm415:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm415():
  {==}

assert tv415:
  Tup(n17())

def tv415():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm416:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm416():
  {==}

assert tv416:
  Tup(n20())

def tv416():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm417:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm417():
  {==}

assert tv417:
  Tup(n23())

def tv417():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm418:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm418():
  {==}

assert tv418:
  Tup(n26())

def tv418():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm419:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm419():
  {==}

assert tv419:
  Tup(n29())

def tv419():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm420:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm420():
  {==}

assert tv420:
  Tup(n4())

def tv420():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm421:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm421():
  {==}

assert tv421:
  Tup(n7())

def tv421():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm422:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm422():
  {==}

assert tv422:
  Tup(n10())

def tv422():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm423:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm423():
  {==}

assert tv423:
  Tup(n13())

def tv423():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm424:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm424():
  {==}

assert tv424:
  Tup(n16())

def tv424():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm425:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm425():
  {==}

assert tv425:
  Tup(n19())

def tv425():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm426:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm426():
  {==}

assert tv426:
  Tup(n22())

def tv426():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm427:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm427():
  {==}

assert tv427:
  Tup(n25())

def tv427():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm428:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm428():
  {==}

assert tv428:
  Tup(n28())

def tv428():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm429:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm429():
  {==}

assert tv429:
  Tup(n31())

def tv429():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm430:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm430():
  {==}

assert tv430:
  Tup(n6())

def tv430():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm431:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm431():
  {==}

assert tv431:
  Tup(n9())

def tv431():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm432:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm432():
  {==}

assert tv432:
  Tup(n12())

def tv432():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm433:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm433():
  {==}

assert tv433:
  Tup(n15())

def tv433():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm434:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm434():
  {==}

assert tv434:
  Tup(n18())

def tv434():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm435:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm435():
  {==}

assert tv435:
  Tup(n21())

def tv435():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm436:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm436():
  {==}

assert tv436:
  Tup(n24())

def tv436():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm437:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm437():
  {==}

assert tv437:
  Tup(n27())

def tv437():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm438:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm438():
  {==}

assert tv438:
  Tup(n30())

def tv438():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm439:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm439():
  {==}

assert tv439:
  Tup(n5())

def tv439():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm440:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm440():
  {==}

assert tv440:
  Tup(n8())

def tv440():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm441:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm441():
  {==}

assert tv441:
  Tup(n11())

def tv441():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm442:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm442():
  {==}

assert tv442:
  Tup(n14())

def tv442():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm443:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm443():
  {==}

assert tv443:
  Tup(n17())

def tv443():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm444:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm444():
  {==}

assert tv444:
  Tup(n20())

def tv444():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm445:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm445():
  {==}

assert tv445:
  Tup(n23())

def tv445():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm446:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm446():
  {==}

assert tv446:
  Tup(n26())

def tv446():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm447:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm447():
  {==}

assert tv447:
  Tup(n29())

def tv447():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm448:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm448():
  {==}

assert tv448:
  Tup(n4())

def tv448():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm449:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm449():
  {==}

assert tv449:
  Tup(n7())

def tv449():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm450:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm450():
  {==}

assert tv450:
  Tup(n10())

def tv450():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm451:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm451():
  {==}

assert tv451:
  Tup(n13())

def tv451():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm452:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm452():
  {==}

assert tv452:
  Tup(n16())

def tv452():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm453:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm453():
  {==}

assert tv453:
  Tup(n19())

def tv453():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm454:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm454():
  {==}

assert tv454:
  Tup(n22())

def tv454():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm455:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm455():
  {==}

assert tv455:
  Tup(n25())

def tv455():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm456:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm456():
  {==}

assert tv456:
  Tup(n28())

def tv456():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm457:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm457():
  {==}

assert tv457:
  Tup(n31())

def tv457():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm458:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm458():
  {==}

assert tv458:
  Tup(n6())

def tv458():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm459:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm459():
  {==}

assert tv459:
  Tup(n9())

def tv459():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm460:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm460():
  {==}

assert tv460:
  Tup(n12())

def tv460():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm461:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm461():
  {==}

assert tv461:
  Tup(n15())

def tv461():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm462:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm462():
  {==}

assert tv462:
  Tup(n18())

def tv462():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm463:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm463():
  {==}

assert tv463:
  Tup(n21())

def tv463():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm464:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm464():
  {==}

assert tv464:
  Tup(n24())

def tv464():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm465:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm465():
  {==}

assert tv465:
  Tup(n27())

def tv465():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm466:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm466():
  {==}

assert tv466:
  Tup(n30())

def tv466():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm467:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm467():
  {==}

assert tv467:
  Tup(n5())

def tv467():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm468:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm468():
  {==}

assert tv468:
  Tup(n8())

def tv468():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm469:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm469():
  {==}

assert tv469:
  Tup(n11())

def tv469():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm470:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm470():
  {==}

assert tv470:
  Tup(n14())

def tv470():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm471:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm471():
  {==}

assert tv471:
  Tup(n17())

def tv471():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm472:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm472():
  {==}

assert tv472:
  Tup(n20())

def tv472():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm473:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm473():
  {==}

assert tv473:
  Tup(n23())

def tv473():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm474:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm474():
  {==}

assert tv474:
  Tup(n26())

def tv474():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm475:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm475():
  {==}

assert tv475:
  Tup(n29())

def tv475():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm476:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm476():
  {==}

assert tv476:
  Tup(n4())

def tv476():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm477:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm477():
  {==}

assert tv477:
  Tup(n7())

def tv477():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm478:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm478():
  {==}

assert tv478:
  Tup(n10())

def tv478():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm479:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm479():
  {==}

assert tv479:
  Tup(n13())

def tv479():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm480:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm480():
  {==}

assert tv480:
  Tup(n16())

def tv480():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm481:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm481():
  {==}

assert tv481:
  Tup(n19())

def tv481():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm482:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm482():
  {==}

assert tv482:
  Tup(n22())

def tv482():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm483:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm483():
  {==}

assert tv483:
  Tup(n25())

def tv483():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm484:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm484():
  {==}

assert tv484:
  Tup(n28())

def tv484():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm485:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm485():
  {==}

assert tv485:
  Tup(n31())

def tv485():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm486:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm486():
  {==}

assert tv486:
  Tup(n6())

def tv486():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm487:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm487():
  {==}

assert tv487:
  Tup(n9())

def tv487():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm488:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm488():
  {==}

assert tv488:
  Tup(n12())

def tv488():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm489:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm489():
  {==}

assert tv489:
  Tup(n15())

def tv489():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm490:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm490():
  {==}

assert tv490:
  Tup(n18())

def tv490():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm491:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm491():
  {==}

assert tv491:
  Tup(n21())

def tv491():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm492:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm492():
  {==}

assert tv492:
  Tup(n24())

def tv492():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm493:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm493():
  {==}

assert tv493:
  Tup(n27())

def tv493():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm494:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm494():
  {==}

assert tv494:
  Tup(n30())

def tv494():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm495:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm495():
  {==}

assert tv495:
  Tup(n5())

def tv495():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm496:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm496():
  {==}

assert tv496:
  Tup(n8())

def tv496():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm497:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm497():
  {==}

assert tv497:
  Tup(n11())

def tv497():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm498:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm498():
  {==}

assert tv498:
  Tup(n14())

def tv498():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm499:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm499():
  {==}

assert tv499:
  Tup(n17())

def tv499():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm500:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm500():
  {==}

assert tv500:
  Tup(n20())

def tv500():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm501:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm501():
  {==}

assert tv501:
  Tup(n23())

def tv501():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm502:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm502():
  {==}

assert tv502:
  Tup(n26())

def tv502():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm503:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm503():
  {==}

assert tv503:
  Tup(n29())

def tv503():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm504:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm504():
  {==}

assert tv504:
  Tup(n4())

def tv504():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm505:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm505():
  {==}

assert tv505:
  Tup(n7())

def tv505():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm506:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm506():
  {==}

assert tv506:
  Tup(n10())

def tv506():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm507:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm507():
  {==}

assert tv507:
  Tup(n13())

def tv507():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm508:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm508():
  {==}

assert tv508:
  Tup(n16())

def tv508():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm509:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm509():
  {==}

assert tv509:
  Tup(n19())

def tv509():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm510:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm510():
  {==}

assert tv510:
  Tup(n22())

def tv510():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm511:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm511():
  {==}

assert tv511:
  Tup(n25())

def tv511():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm512:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm512():
  {==}

assert tv512:
  Tup(n28())

def tv512():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm513:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm513():
  {==}

assert tv513:
  Tup(n31())

def tv513():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm514:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm514():
  {==}

assert tv514:
  Tup(n6())

def tv514():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm515:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm515():
  {==}

assert tv515:
  Tup(n9())

def tv515():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm516:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm516():
  {==}

assert tv516:
  Tup(n12())

def tv516():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm517:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm517():
  {==}

assert tv517:
  Tup(n15())

def tv517():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm518:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm518():
  {==}

assert tv518:
  Tup(n18())

def tv518():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm519:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm519():
  {==}

assert tv519:
  Tup(n21())

def tv519():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm520:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm520():
  {==}

assert tv520:
  Tup(n24())

def tv520():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm521:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm521():
  {==}

assert tv521:
  Tup(n27())

def tv521():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm522:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm522():
  {==}

assert tv522:
  Tup(n30())

def tv522():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm523:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm523():
  {==}

assert tv523:
  Tup(n5())

def tv523():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm524:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm524():
  {==}

assert tv524:
  Tup(n8())

def tv524():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm525:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm525():
  {==}

assert tv525:
  Tup(n11())

def tv525():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm526:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm526():
  {==}

assert tv526:
  Tup(n14())

def tv526():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm527:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm527():
  {==}

assert tv527:
  Tup(n17())

def tv527():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm528:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm528():
  {==}

assert tv528:
  Tup(n20())

def tv528():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm529:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm529():
  {==}

assert tv529:
  Tup(n23())

def tv529():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm530:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm530():
  {==}

assert tv530:
  Tup(n26())

def tv530():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm531:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm531():
  {==}

assert tv531:
  Tup(n29())

def tv531():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm532:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm532():
  {==}

assert tv532:
  Tup(n4())

def tv532():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm533:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm533():
  {==}

assert tv533:
  Tup(n7())

def tv533():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm534:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm534():
  {==}

assert tv534:
  Tup(n10())

def tv534():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm535:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm535():
  {==}

assert tv535:
  Tup(n13())

def tv535():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm536:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm536():
  {==}

assert tv536:
  Tup(n16())

def tv536():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm537:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm537():
  {==}

assert tv537:
  Tup(n19())

def tv537():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm538:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm538():
  {==}

assert tv538:
  Tup(n22())

def tv538():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm539:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm539():
  {==}

assert tv539:
  Tup(n25())

def tv539():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm540:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm540():
  {==}

assert tv540:
  Tup(n28())

def tv540():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm541:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm541():
  {==}

assert tv541:
  Tup(n31())

def tv541():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm542:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm542():
  {==}

assert tv542:
  Tup(n6())

def tv542():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm543:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm543():
  {==}

assert tv543:
  Tup(n9())

def tv543():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm544:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm544():
  {==}

assert tv544:
  Tup(n12())

def tv544():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm545:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm545():
  {==}

assert tv545:
  Tup(n15())

def tv545():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm546:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm546():
  {==}

assert tv546:
  Tup(n18())

def tv546():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm547:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm547():
  {==}

assert tv547:
  Tup(n21())

def tv547():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm548:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm548():
  {==}

assert tv548:
  Tup(n24())

def tv548():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm549:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm549():
  {==}

assert tv549:
  Tup(n27())

def tv549():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm550:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm550():
  {==}

assert tv550:
  Tup(n30())

def tv550():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm551:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm551():
  {==}

assert tv551:
  Tup(n5())

def tv551():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm552:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm552():
  {==}

assert tv552:
  Tup(n8())

def tv552():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm553:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm553():
  {==}

assert tv553:
  Tup(n11())

def tv553():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm554:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm554():
  {==}

assert tv554:
  Tup(n14())

def tv554():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm555:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm555():
  {==}

assert tv555:
  Tup(n17())

def tv555():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm556:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm556():
  {==}

assert tv556:
  Tup(n20())

def tv556():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm557:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm557():
  {==}

assert tv557:
  Tup(n23())

def tv557():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm558:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm558():
  {==}

assert tv558:
  Tup(n26())

def tv558():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm559:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm559():
  {==}

assert tv559:
  Tup(n29())

def tv559():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm560:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm560():
  {==}

assert tv560:
  Tup(n4())

def tv560():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm561:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm561():
  {==}

assert tv561:
  Tup(n7())

def tv561():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm562:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm562():
  {==}

assert tv562:
  Tup(n10())

def tv562():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm563:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm563():
  {==}

assert tv563:
  Tup(n13())

def tv563():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm564:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm564():
  {==}

assert tv564:
  Tup(n16())

def tv564():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm565:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm565():
  {==}

assert tv565:
  Tup(n19())

def tv565():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm566:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm566():
  {==}

assert tv566:
  Tup(n22())

def tv566():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm567:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm567():
  {==}

assert tv567:
  Tup(n25())

def tv567():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm568:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm568():
  {==}

assert tv568:
  Tup(n28())

def tv568():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm569:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm569():
  {==}

assert tv569:
  Tup(n31())

def tv569():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm570:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm570():
  {==}

assert tv570:
  Tup(n6())

def tv570():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm571:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm571():
  {==}

assert tv571:
  Tup(n9())

def tv571():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm572:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm572():
  {==}

assert tv572:
  Tup(n12())

def tv572():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm573:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm573():
  {==}

assert tv573:
  Tup(n15())

def tv573():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm574:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm574():
  {==}

assert tv574:
  Tup(n18())

def tv574():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm575:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm575():
  {==}

assert tv575:
  Tup(n21())

def tv575():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm576:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm576():
  {==}

assert tv576:
  Tup(n24())

def tv576():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm577:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm577():
  {==}

assert tv577:
  Tup(n27())

def tv577():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm578:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm578():
  {==}

assert tv578:
  Tup(n30())

def tv578():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm579:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm579():
  {==}

assert tv579:
  Tup(n5())

def tv579():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm580:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm580():
  {==}

assert tv580:
  Tup(n8())

def tv580():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm581:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm581():
  {==}

assert tv581:
  Tup(n11())

def tv581():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm582:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm582():
  {==}

assert tv582:
  Tup(n14())

def tv582():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm583:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm583():
  {==}

assert tv583:
  Tup(n17())

def tv583():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm584:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm584():
  {==}

assert tv584:
  Tup(n20())

def tv584():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm585:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm585():
  {==}

assert tv585:
  Tup(n23())

def tv585():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm586:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm586():
  {==}

assert tv586:
  Tup(n26())

def tv586():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm587:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm587():
  {==}

assert tv587:
  Tup(n29())

def tv587():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm588:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm588():
  {==}

assert tv588:
  Tup(n4())

def tv588():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm589:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm589():
  {==}

assert tv589:
  Tup(n7())

def tv589():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm590:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm590():
  {==}

assert tv590:
  Tup(n10())

def tv590():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm591:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm591():
  {==}

assert tv591:
  Tup(n13())

def tv591():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm592:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm592():
  {==}

assert tv592:
  Tup(n16())

def tv592():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm593:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm593():
  {==}

assert tv593:
  Tup(n19())

def tv593():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm594:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm594():
  {==}

assert tv594:
  Tup(n22())

def tv594():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm595:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm595():
  {==}

assert tv595:
  Tup(n25())

def tv595():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm596:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm596():
  {==}

assert tv596:
  Tup(n28())

def tv596():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm597:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm597():
  {==}

assert tv597:
  Tup(n31())

def tv597():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm598:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm598():
  {==}

assert tv598:
  Tup(n6())

def tv598():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm599:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm599():
  {==}

assert tv599:
  Tup(n9())

def tv599():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm600:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm600():
  {==}

assert tv600:
  Tup(n12())

def tv600():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm601:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm601():
  {==}

assert tv601:
  Tup(n15())

def tv601():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm602:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm602():
  {==}

assert tv602:
  Tup(n18())

def tv602():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm603:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm603():
  {==}

assert tv603:
  Tup(n21())

def tv603():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm604:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm604():
  {==}

assert tv604:
  Tup(n24())

def tv604():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm605:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm605():
  {==}

assert tv605:
  Tup(n27())

def tv605():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm606:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm606():
  {==}

assert tv606:
  Tup(n30())

def tv606():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm607:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm607():
  {==}

assert tv607:
  Tup(n5())

def tv607():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm608:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm608():
  {==}

assert tv608:
  Tup(n8())

def tv608():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm609:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm609():
  {==}

assert tv609:
  Tup(n11())

def tv609():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm610:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm610():
  {==}

assert tv610:
  Tup(n14())

def tv610():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm611:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm611():
  {==}

assert tv611:
  Tup(n17())

def tv611():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm612:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm612():
  {==}

assert tv612:
  Tup(n20())

def tv612():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm613:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm613():
  {==}

assert tv613:
  Tup(n23())

def tv613():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm614:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm614():
  {==}

assert tv614:
  Tup(n26())

def tv614():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm615:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm615():
  {==}

assert tv615:
  Tup(n29())

def tv615():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm616:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm616():
  {==}

assert tv616:
  Tup(n4())

def tv616():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm617:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm617():
  {==}

assert tv617:
  Tup(n7())

def tv617():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm618:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm618():
  {==}

assert tv618:
  Tup(n10())

def tv618():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm619:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm619():
  {==}

assert tv619:
  Tup(n13())

def tv619():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm620:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm620():
  {==}

assert tv620:
  Tup(n16())

def tv620():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm621:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm621():
  {==}

assert tv621:
  Tup(n19())

def tv621():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm622:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm622():
  {==}

assert tv622:
  Tup(n22())

def tv622():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm623:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm623():
  {==}

assert tv623:
  Tup(n25())

def tv623():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm624:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm624():
  {==}

assert tv624:
  Tup(n28())

def tv624():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm625:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm625():
  {==}

assert tv625:
  Tup(n31())

def tv625():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm626:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm626():
  {==}

assert tv626:
  Tup(n6())

def tv626():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm627:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm627():
  {==}

assert tv627:
  Tup(n9())

def tv627():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm628:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm628():
  {==}

assert tv628:
  Tup(n12())

def tv628():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm629:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm629():
  {==}

assert tv629:
  Tup(n15())

def tv629():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm630:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm630():
  {==}

assert tv630:
  Tup(n18())

def tv630():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm631:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm631():
  {==}

assert tv631:
  Tup(n21())

def tv631():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm632:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm632():
  {==}

assert tv632:
  Tup(n24())

def tv632():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm633:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm633():
  {==}

assert tv633:
  Tup(n27())

def tv633():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm634:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm634():
  {==}

assert tv634:
  Tup(n30())

def tv634():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm635:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm635():
  {==}

assert tv635:
  Tup(n5())

def tv635():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm636:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm636():
  {==}

assert tv636:
  Tup(n8())

def tv636():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm637:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm637():
  {==}

assert tv637:
  Tup(n11())

def tv637():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm638:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm638():
  {==}

assert tv638:
  Tup(n14())

def tv638():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm639:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm639():
  {==}

assert tv639:
  Tup(n17())

def tv639():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm640:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm640():
  {==}

assert tv640:
  Tup(n20())

def tv640():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm641:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm641():
  {==}

assert tv641:
  Tup(n23())

def tv641():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm642:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm642():
  {==}

assert tv642:
  Tup(n26())

def tv642():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm643:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm643():
  {==}

assert tv643:
  Tup(n29())

def tv643():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm644:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm644():
  {==}

assert tv644:
  Tup(n4())

def tv644():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm645:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm645():
  {==}

assert tv645:
  Tup(n7())

def tv645():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm646:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm646():
  {==}

assert tv646:
  Tup(n10())

def tv646():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm647:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm647():
  {==}

assert tv647:
  Tup(n13())

def tv647():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm648:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm648():
  {==}

assert tv648:
  Tup(n16())

def tv648():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm649:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm649():
  {==}

assert tv649:
  Tup(n19())

def tv649():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm650:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm650():
  {==}

assert tv650:
  Tup(n22())

def tv650():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm651:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm651():
  {==}

assert tv651:
  Tup(n25())

def tv651():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm652:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm652():
  {==}

assert tv652:
  Tup(n28())

def tv652():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm653:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm653():
  {==}

assert tv653:
  Tup(n31())

def tv653():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm654:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm654():
  {==}

assert tv654:
  Tup(n6())

def tv654():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm655:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm655():
  {==}

assert tv655:
  Tup(n9())

def tv655():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm656:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm656():
  {==}

assert tv656:
  Tup(n12())

def tv656():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm657:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm657():
  {==}

assert tv657:
  Tup(n15())

def tv657():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm658:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm658():
  {==}

assert tv658:
  Tup(n18())

def tv658():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm659:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm659():
  {==}

assert tv659:
  Tup(n21())

def tv659():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm660:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm660():
  {==}

assert tv660:
  Tup(n24())

def tv660():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm661:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm661():
  {==}

assert tv661:
  Tup(n27())

def tv661():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm662:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm662():
  {==}

assert tv662:
  Tup(n30())

def tv662():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm663:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm663():
  {==}

assert tv663:
  Tup(n5())

def tv663():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm664:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm664():
  {==}

assert tv664:
  Tup(n8())

def tv664():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm665:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm665():
  {==}

assert tv665:
  Tup(n11())

def tv665():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm666:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm666():
  {==}

assert tv666:
  Tup(n14())

def tv666():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm667:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm667():
  {==}

assert tv667:
  Tup(n17())

def tv667():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm668:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm668():
  {==}

assert tv668:
  Tup(n20())

def tv668():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm669:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm669():
  {==}

assert tv669:
  Tup(n23())

def tv669():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm670:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm670():
  {==}

assert tv670:
  Tup(n26())

def tv670():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm671:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm671():
  {==}

assert tv671:
  Tup(n29())

def tv671():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm672:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm672():
  {==}

assert tv672:
  Tup(n4())

def tv672():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm673:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm673():
  {==}

assert tv673:
  Tup(n7())

def tv673():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm674:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm674():
  {==}

assert tv674:
  Tup(n10())

def tv674():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm675:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm675():
  {==}

assert tv675:
  Tup(n13())

def tv675():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm676:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm676():
  {==}

assert tv676:
  Tup(n16())

def tv676():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm677:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm677():
  {==}

assert tv677:
  Tup(n19())

def tv677():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm678:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm678():
  {==}

assert tv678:
  Tup(n22())

def tv678():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm679:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm679():
  {==}

assert tv679:
  Tup(n25())

def tv679():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm680:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm680():
  {==}

assert tv680:
  Tup(n28())

def tv680():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm681:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm681():
  {==}

assert tv681:
  Tup(n31())

def tv681():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm682:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm682():
  {==}

assert tv682:
  Tup(n6())

def tv682():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm683:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm683():
  {==}

assert tv683:
  Tup(n9())

def tv683():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm684:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm684():
  {==}

assert tv684:
  Tup(n12())

def tv684():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm685:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm685():
  {==}

assert tv685:
  Tup(n15())

def tv685():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm686:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm686():
  {==}

assert tv686:
  Tup(n18())

def tv686():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm687:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm687():
  {==}

assert tv687:
  Tup(n21())

def tv687():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm688:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm688():
  {==}

assert tv688:
  Tup(n24())

def tv688():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm689:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm689():
  {==}

assert tv689:
  Tup(n27())

def tv689():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm690:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm690():
  {==}

assert tv690:
  Tup(n30())

def tv690():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm691:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm691():
  {==}

assert tv691:
  Tup(n5())

def tv691():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm692:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm692():
  {==}

assert tv692:
  Tup(n8())

def tv692():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm693:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm693():
  {==}

assert tv693:
  Tup(n11())

def tv693():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm694:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm694():
  {==}

assert tv694:
  Tup(n14())

def tv694():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm695:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm695():
  {==}

assert tv695:
  Tup(n17())

def tv695():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm696:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm696():
  {==}

assert tv696:
  Tup(n20())

def tv696():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm697:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm697():
  {==}

assert tv697:
  Tup(n23())

def tv697():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm698:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm698():
  {==}

assert tv698:
  Tup(n26())

def tv698():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm699:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm699():
  {==}

assert tv699:
  Tup(n29())

def tv699():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm700:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm700():
  {==}

assert tv700:
  Tup(n4())

def tv700():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm701:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm701():
  {==}

assert tv701:
  Tup(n7())

def tv701():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm702:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm702():
  {==}

assert tv702:
  Tup(n10())

def tv702():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm703:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm703():
  {==}

assert tv703:
  Tup(n13())

def tv703():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm704:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm704():
  {==}

assert tv704:
  Tup(n16())

def tv704():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm705:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm705():
  {==}

assert tv705:
  Tup(n19())

def tv705():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm706:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm706():
  {==}

assert tv706:
  Tup(n22())

def tv706():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm707:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm707():
  {==}

assert tv707:
  Tup(n25())

def tv707():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm708:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm708():
  {==}

assert tv708:
  Tup(n28())

def tv708():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm709:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm709():
  {==}

assert tv709:
  Tup(n31())

def tv709():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm710:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm710():
  {==}

assert tv710:
  Tup(n6())

def tv710():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm711:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm711():
  {==}

assert tv711:
  Tup(n9())

def tv711():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm712:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm712():
  {==}

assert tv712:
  Tup(n12())

def tv712():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm713:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm713():
  {==}

assert tv713:
  Tup(n15())

def tv713():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm714:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm714():
  {==}

assert tv714:
  Tup(n18())

def tv714():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm715:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm715():
  {==}

assert tv715:
  Tup(n21())

def tv715():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm716:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm716():
  {==}

assert tv716:
  Tup(n24())

def tv716():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm717:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm717():
  {==}

assert tv717:
  Tup(n27())

def tv717():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm718:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm718():
  {==}

assert tv718:
  Tup(n30())

def tv718():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm719:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm719():
  {==}

assert tv719:
  Tup(n5())

def tv719():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm720:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm720():
  {==}

assert tv720:
  Tup(n8())

def tv720():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm721:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm721():
  {==}

assert tv721:
  Tup(n11())

def tv721():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm722:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm722():
  {==}

assert tv722:
  Tup(n14())

def tv722():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm723:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm723():
  {==}

assert tv723:
  Tup(n17())

def tv723():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm724:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm724():
  {==}

assert tv724:
  Tup(n20())

def tv724():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm725:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm725():
  {==}

assert tv725:
  Tup(n23())

def tv725():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm726:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm726():
  {==}

assert tv726:
  Tup(n26())

def tv726():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm727:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm727():
  {==}

assert tv727:
  Tup(n29())

def tv727():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm728:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm728():
  {==}

assert tv728:
  Tup(n4())

def tv728():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm729:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm729():
  {==}

assert tv729:
  Tup(n7())

def tv729():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm730:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm730():
  {==}

assert tv730:
  Tup(n10())

def tv730():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm731:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm731():
  {==}

assert tv731:
  Tup(n13())

def tv731():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm732:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm732():
  {==}

assert tv732:
  Tup(n16())

def tv732():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm733:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm733():
  {==}

assert tv733:
  Tup(n19())

def tv733():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm734:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm734():
  {==}

assert tv734:
  Tup(n22())

def tv734():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm735:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm735():
  {==}

assert tv735:
  Tup(n25())

def tv735():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm736:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm736():
  {==}

assert tv736:
  Tup(n28())

def tv736():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm737:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm737():
  {==}

assert tv737:
  Tup(n31())

def tv737():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm738:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm738():
  {==}

assert tv738:
  Tup(n6())

def tv738():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm739:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm739():
  {==}

assert tv739:
  Tup(n9())

def tv739():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm740:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm740():
  {==}

assert tv740:
  Tup(n12())

def tv740():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm741:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm741():
  {==}

assert tv741:
  Tup(n15())

def tv741():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm742:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm742():
  {==}

assert tv742:
  Tup(n18())

def tv742():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm743:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm743():
  {==}

assert tv743:
  Tup(n21())

def tv743():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm744:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm744():
  {==}

assert tv744:
  Tup(n24())

def tv744():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm745:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm745():
  {==}

assert tv745:
  Tup(n27())

def tv745():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm746:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm746():
  {==}

assert tv746:
  Tup(n30())

def tv746():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm747:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm747():
  {==}

assert tv747:
  Tup(n5())

def tv747():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm748:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm748():
  {==}

assert tv748:
  Tup(n8())

def tv748():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm749:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm749():
  {==}

assert tv749:
  Tup(n11())

def tv749():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm750:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm750():
  {==}

assert tv750:
  Tup(n14())

def tv750():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm751:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm751():
  {==}

assert tv751:
  Tup(n17())

def tv751():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm752:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm752():
  {==}

assert tv752:
  Tup(n20())

def tv752():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm753:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm753():
  {==}

assert tv753:
  Tup(n23())

def tv753():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm754:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm754():
  {==}

assert tv754:
  Tup(n26())

def tv754():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm755:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm755():
  {==}

assert tv755:
  Tup(n29())

def tv755():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm756:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm756():
  {==}

assert tv756:
  Tup(n4())

def tv756():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm757:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm757():
  {==}

assert tv757:
  Tup(n7())

def tv757():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm758:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm758():
  {==}

assert tv758:
  Tup(n10())

def tv758():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm759:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm759():
  {==}

assert tv759:
  Tup(n13())

def tv759():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm760:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm760():
  {==}

assert tv760:
  Tup(n16())

def tv760():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm761:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm761():
  {==}

assert tv761:
  Tup(n19())

def tv761():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm762:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm762():
  {==}

assert tv762:
  Tup(n22())

def tv762():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm763:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm763():
  {==}

assert tv763:
  Tup(n25())

def tv763():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm764:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm764():
  {==}

assert tv764:
  Tup(n28())

def tv764():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm765:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm765():
  {==}

assert tv765:
  Tup(n31())

def tv765():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm766:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm766():
  {==}

assert tv766:
  Tup(n6())

def tv766():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm767:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm767():
  {==}

assert tv767:
  Tup(n9())

def tv767():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm768:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm768():
  {==}

assert tv768:
  Tup(n12())

def tv768():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm769:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm769():
  {==}

assert tv769:
  Tup(n15())

def tv769():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm770:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm770():
  {==}

assert tv770:
  Tup(n18())

def tv770():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm771:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm771():
  {==}

assert tv771:
  Tup(n21())

def tv771():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm772:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm772():
  {==}

assert tv772:
  Tup(n24())

def tv772():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm773:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm773():
  {==}

assert tv773:
  Tup(n27())

def tv773():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm774:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm774():
  {==}

assert tv774:
  Tup(n30())

def tv774():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm775:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm775():
  {==}

assert tv775:
  Tup(n5())

def tv775():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm776:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm776():
  {==}

assert tv776:
  Tup(n8())

def tv776():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm777:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm777():
  {==}

assert tv777:
  Tup(n11())

def tv777():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm778:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm778():
  {==}

assert tv778:
  Tup(n14())

def tv778():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm779:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm779():
  {==}

assert tv779:
  Tup(n17())

def tv779():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm780:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm780():
  {==}

assert tv780:
  Tup(n20())

def tv780():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm781:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm781():
  {==}

assert tv781:
  Tup(n23())

def tv781():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm782:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm782():
  {==}

assert tv782:
  Tup(n26())

def tv782():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm783:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm783():
  {==}

assert tv783:
  Tup(n29())

def tv783():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm784:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm784():
  {==}

assert tv784:
  Tup(n4())

def tv784():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm785:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm785():
  {==}

assert tv785:
  Tup(n7())

def tv785():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm786:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm786():
  {==}

assert tv786:
  Tup(n10())

def tv786():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm787:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm787():
  {==}

assert tv787:
  Tup(n13())

def tv787():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm788:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm788():
  {==}

assert tv788:
  Tup(n16())

def tv788():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm789:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm789():
  {==}

assert tv789:
  Tup(n19())

def tv789():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm790:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm790():
  {==}

assert tv790:
  Tup(n22())

def tv790():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm791:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm791():
  {==}

assert tv791:
  Tup(n25())

def tv791():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm792:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm792():
  {==}

assert tv792:
  Tup(n28())

def tv792():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm793:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm793():
  {==}

assert tv793:
  Tup(n31())

def tv793():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm794:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm794():
  {==}

assert tv794:
  Tup(n6())

def tv794():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm795:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm795():
  {==}

assert tv795:
  Tup(n9())

def tv795():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm796:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm796():
  {==}

assert tv796:
  Tup(n12())

def tv796():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm797:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm797():
  {==}

assert tv797:
  Tup(n15())

def tv797():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm798:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm798():
  {==}

assert tv798:
  Tup(n18())

def tv798():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm799:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm799():
  {==}

assert tv799:
  Tup(n21())

def tv799():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm800:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm800():
  {==}

assert tv800:
  Tup(n24())

def tv800():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm801:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm801():
  {==}

assert tv801:
  Tup(n27())

def tv801():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm802:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm802():
  {==}

assert tv802:
  Tup(n30())

def tv802():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm803:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm803():
  {==}

assert tv803:
  Tup(n5())

def tv803():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm804:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm804():
  {==}

assert tv804:
  Tup(n8())

def tv804():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm805:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm805():
  {==}

assert tv805:
  Tup(n11())

def tv805():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm806:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm806():
  {==}

assert tv806:
  Tup(n14())

def tv806():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm807:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm807():
  {==}

assert tv807:
  Tup(n17())

def tv807():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm808:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm808():
  {==}

assert tv808:
  Tup(n20())

def tv808():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm809:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm809():
  {==}

assert tv809:
  Tup(n23())

def tv809():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm810:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm810():
  {==}

assert tv810:
  Tup(n26())

def tv810():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm811:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm811():
  {==}

assert tv811:
  Tup(n29())

def tv811():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm812:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm812():
  {==}

assert tv812:
  Tup(n4())

def tv812():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm813:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm813():
  {==}

assert tv813:
  Tup(n7())

def tv813():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm814:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm814():
  {==}

assert tv814:
  Tup(n10())

def tv814():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm815:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm815():
  {==}

assert tv815:
  Tup(n13())

def tv815():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm816:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm816():
  {==}

assert tv816:
  Tup(n16())

def tv816():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm817:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm817():
  {==}

assert tv817:
  Tup(n19())

def tv817():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm818:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm818():
  {==}

assert tv818:
  Tup(n22())

def tv818():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm819:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm819():
  {==}

assert tv819:
  Tup(n25())

def tv819():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm820:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm820():
  {==}

assert tv820:
  Tup(n28())

def tv820():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm821:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm821():
  {==}

assert tv821:
  Tup(n31())

def tv821():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm822:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm822():
  {==}

assert tv822:
  Tup(n6())

def tv822():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm823:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm823():
  {==}

assert tv823:
  Tup(n9())

def tv823():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm824:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm824():
  {==}

assert tv824:
  Tup(n12())

def tv824():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm825:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm825():
  {==}

assert tv825:
  Tup(n15())

def tv825():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm826:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm826():
  {==}

assert tv826:
  Tup(n18())

def tv826():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm827:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm827():
  {==}

assert tv827:
  Tup(n21())

def tv827():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm828:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm828():
  {==}

assert tv828:
  Tup(n24())

def tv828():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm829:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm829():
  {==}

assert tv829:
  Tup(n27())

def tv829():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm830:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm830():
  {==}

assert tv830:
  Tup(n30())

def tv830():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm831:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm831():
  {==}

assert tv831:
  Tup(n5())

def tv831():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm832:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm832():
  {==}

assert tv832:
  Tup(n8())

def tv832():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm833:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm833():
  {==}

assert tv833:
  Tup(n11())

def tv833():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm834:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm834():
  {==}

assert tv834:
  Tup(n14())

def tv834():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm835:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm835():
  {==}

assert tv835:
  Tup(n17())

def tv835():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm836:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm836():
  {==}

assert tv836:
  Tup(n20())

def tv836():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm837:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm837():
  {==}

assert tv837:
  Tup(n23())

def tv837():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm838:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm838():
  {==}

assert tv838:
  Tup(n26())

def tv838():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm839:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm839():
  {==}

assert tv839:
  Tup(n29())

def tv839():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm840:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm840():
  {==}

assert tv840:
  Tup(n4())

def tv840():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm841:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm841():
  {==}

assert tv841:
  Tup(n7())

def tv841():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm842:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm842():
  {==}

assert tv842:
  Tup(n10())

def tv842():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm843:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm843():
  {==}

assert tv843:
  Tup(n13())

def tv843():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm844:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm844():
  {==}

assert tv844:
  Tup(n16())

def tv844():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm845:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm845():
  {==}

assert tv845:
  Tup(n19())

def tv845():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm846:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm846():
  {==}

assert tv846:
  Tup(n22())

def tv846():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm847:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm847():
  {==}

assert tv847:
  Tup(n25())

def tv847():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm848:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm848():
  {==}

assert tv848:
  Tup(n28())

def tv848():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm849:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm849():
  {==}

assert tv849:
  Tup(n31())

def tv849():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm850:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm850():
  {==}

assert tv850:
  Tup(n6())

def tv850():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm851:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm851():
  {==}

assert tv851:
  Tup(n9())

def tv851():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm852:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm852():
  {==}

assert tv852:
  Tup(n12())

def tv852():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm853:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm853():
  {==}

assert tv853:
  Tup(n15())

def tv853():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm854:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm854():
  {==}

assert tv854:
  Tup(n18())

def tv854():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm855:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm855():
  {==}

assert tv855:
  Tup(n21())

def tv855():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm856:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm856():
  {==}

assert tv856:
  Tup(n24())

def tv856():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm857:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm857():
  {==}

assert tv857:
  Tup(n27())

def tv857():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm858:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm858():
  {==}

assert tv858:
  Tup(n30())

def tv858():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm859:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm859():
  {==}

assert tv859:
  Tup(n5())

def tv859():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm860:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm860():
  {==}

assert tv860:
  Tup(n8())

def tv860():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm861:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm861():
  {==}

assert tv861:
  Tup(n11())

def tv861():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm862:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm862():
  {==}

assert tv862:
  Tup(n14())

def tv862():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm863:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm863():
  {==}

assert tv863:
  Tup(n17())

def tv863():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm864:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm864():
  {==}

assert tv864:
  Tup(n20())

def tv864():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm865:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm865():
  {==}

assert tv865:
  Tup(n23())

def tv865():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm866:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm866():
  {==}

assert tv866:
  Tup(n26())

def tv866():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm867:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm867():
  {==}

assert tv867:
  Tup(n29())

def tv867():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm868:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm868():
  {==}

assert tv868:
  Tup(n4())

def tv868():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm869:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm869():
  {==}

assert tv869:
  Tup(n7())

def tv869():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm870:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm870():
  {==}

assert tv870:
  Tup(n10())

def tv870():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm871:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm871():
  {==}

assert tv871:
  Tup(n13())

def tv871():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm872:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm872():
  {==}

assert tv872:
  Tup(n16())

def tv872():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm873:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm873():
  {==}

assert tv873:
  Tup(n19())

def tv873():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm874:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm874():
  {==}

assert tv874:
  Tup(n22())

def tv874():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm875:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm875():
  {==}

assert tv875:
  Tup(n25())

def tv875():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm876:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm876():
  {==}

assert tv876:
  Tup(n28())

def tv876():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm877:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm877():
  {==}

assert tv877:
  Tup(n31())

def tv877():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm878:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm878():
  {==}

assert tv878:
  Tup(n6())

def tv878():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm879:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm879():
  {==}

assert tv879:
  Tup(n9())

def tv879():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm880:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm880():
  {==}

assert tv880:
  Tup(n12())

def tv880():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm881:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm881():
  {==}

assert tv881:
  Tup(n15())

def tv881():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm882:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm882():
  {==}

assert tv882:
  Tup(n18())

def tv882():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm883:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm883():
  {==}

assert tv883:
  Tup(n21())

def tv883():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm884:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm884():
  {==}

assert tv884:
  Tup(n24())

def tv884():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm885:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm885():
  {==}

assert tv885:
  Tup(n27())

def tv885():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm886:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm886():
  {==}

assert tv886:
  Tup(n30())

def tv886():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm887:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm887():
  {==}

assert tv887:
  Tup(n5())

def tv887():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm888:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm888():
  {==}

assert tv888:
  Tup(n8())

def tv888():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm889:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm889():
  {==}

assert tv889:
  Tup(n11())

def tv889():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm890:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm890():
  {==}

assert tv890:
  Tup(n14())

def tv890():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm891:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm891():
  {==}

assert tv891:
  Tup(n17())

def tv891():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm892:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm892():
  {==}

assert tv892:
  Tup(n20())

def tv892():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm893:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm893():
  {==}

assert tv893:
  Tup(n23())

def tv893():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm894:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm894():
  {==}

assert tv894:
  Tup(n26())

def tv894():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm895:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm895():
  {==}

assert tv895:
  Tup(n29())

def tv895():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm896:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm896():
  {==}

assert tv896:
  Tup(n4())

def tv896():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm897:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm897():
  {==}

assert tv897:
  Tup(n7())

def tv897():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm898:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm898():
  {==}

assert tv898:
  Tup(n10())

def tv898():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm899:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm899():
  {==}

assert tv899:
  Tup(n13())

def tv899():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm900:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm900():
  {==}

assert tv900:
  Tup(n16())

def tv900():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm901:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm901():
  {==}

assert tv901:
  Tup(n19())

def tv901():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm902:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm902():
  {==}

assert tv902:
  Tup(n22())

def tv902():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm903:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm903():
  {==}

assert tv903:
  Tup(n25())

def tv903():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm904:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm904():
  {==}

assert tv904:
  Tup(n28())

def tv904():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm905:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm905():
  {==}

assert tv905:
  Tup(n31())

def tv905():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm906:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm906():
  {==}

assert tv906:
  Tup(n6())

def tv906():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm907:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm907():
  {==}

assert tv907:
  Tup(n9())

def tv907():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm908:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm908():
  {==}

assert tv908:
  Tup(n12())

def tv908():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm909:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm909():
  {==}

assert tv909:
  Tup(n15())

def tv909():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm910:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm910():
  {==}

assert tv910:
  Tup(n18())

def tv910():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm911:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm911():
  {==}

assert tv911:
  Tup(n21())

def tv911():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm912:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm912():
  {==}

assert tv912:
  Tup(n24())

def tv912():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm913:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm913():
  {==}

assert tv913:
  Tup(n27())

def tv913():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm914:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm914():
  {==}

assert tv914:
  Tup(n30())

def tv914():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm915:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm915():
  {==}

assert tv915:
  Tup(n5())

def tv915():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm916:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm916():
  {==}

assert tv916:
  Tup(n8())

def tv916():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm917:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm917():
  {==}

assert tv917:
  Tup(n11())

def tv917():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm918:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm918():
  {==}

assert tv918:
  Tup(n14())

def tv918():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm919:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm919():
  {==}

assert tv919:
  Tup(n17())

def tv919():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm920:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm920():
  {==}

assert tv920:
  Tup(n20())

def tv920():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm921:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm921():
  {==}

assert tv921:
  Tup(n23())

def tv921():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm922:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm922():
  {==}

assert tv922:
  Tup(n26())

def tv922():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm923:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm923():
  {==}

assert tv923:
  Tup(n29())

def tv923():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm924:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm924():
  {==}

assert tv924:
  Tup(n4())

def tv924():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm925:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm925():
  {==}

assert tv925:
  Tup(n7())

def tv925():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm926:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm926():
  {==}

assert tv926:
  Tup(n10())

def tv926():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm927:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm927():
  {==}

assert tv927:
  Tup(n13())

def tv927():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm928:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm928():
  {==}

assert tv928:
  Tup(n16())

def tv928():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm929:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm929():
  {==}

assert tv929:
  Tup(n19())

def tv929():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm930:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm930():
  {==}

assert tv930:
  Tup(n22())

def tv930():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm931:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm931():
  {==}

assert tv931:
  Tup(n25())

def tv931():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm932:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm932():
  {==}

assert tv932:
  Tup(n28())

def tv932():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm933:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm933():
  {==}

assert tv933:
  Tup(n31())

def tv933():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm934:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm934():
  {==}

assert tv934:
  Tup(n6())

def tv934():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm935:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm935():
  {==}

assert tv935:
  Tup(n9())

def tv935():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm936:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm936():
  {==}

assert tv936:
  Tup(n12())

def tv936():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm937:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm937():
  {==}

assert tv937:
  Tup(n15())

def tv937():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm938:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm938():
  {==}

assert tv938:
  Tup(n18())

def tv938():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm939:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm939():
  {==}

assert tv939:
  Tup(n21())

def tv939():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm940:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm940():
  {==}

assert tv940:
  Tup(n24())

def tv940():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm941:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm941():
  {==}

assert tv941:
  Tup(n27())

def tv941():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm942:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm942():
  {==}

assert tv942:
  Tup(n30())

def tv942():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm943:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm943():
  {==}

assert tv943:
  Tup(n5())

def tv943():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm944:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm944():
  {==}

assert tv944:
  Tup(n8())

def tv944():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm945:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm945():
  {==}

assert tv945:
  Tup(n11())

def tv945():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm946:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm946():
  {==}

assert tv946:
  Tup(n14())

def tv946():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm947:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm947():
  {==}

assert tv947:
  Tup(n17())

def tv947():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm948:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm948():
  {==}

assert tv948:
  Tup(n20())

def tv948():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm949:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm949():
  {==}

assert tv949:
  Tup(n23())

def tv949():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm950:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm950():
  {==}

assert tv950:
  Tup(n26())

def tv950():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm951:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm951():
  {==}

assert tv951:
  Tup(n29())

def tv951():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm952:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm952():
  {==}

assert tv952:
  Tup(n4())

def tv952():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm953:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm953():
  {==}

assert tv953:
  Tup(n7())

def tv953():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm954:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm954():
  {==}

assert tv954:
  Tup(n10())

def tv954():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm955:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm955():
  {==}

assert tv955:
  Tup(n13())

def tv955():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm956:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm956():
  {==}

assert tv956:
  Tup(n16())

def tv956():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm957:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm957():
  {==}

assert tv957:
  Tup(n19())

def tv957():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm958:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm958():
  {==}

assert tv958:
  Tup(n22())

def tv958():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm959:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm959():
  {==}

assert tv959:
  Tup(n25())

def tv959():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm960:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm960():
  {==}

assert tv960:
  Tup(n28())

def tv960():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm961:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm961():
  {==}

assert tv961:
  Tup(n31())

def tv961():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm962:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm962():
  {==}

assert tv962:
  Tup(n6())

def tv962():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm963:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm963():
  {==}

assert tv963:
  Tup(n9())

def tv963():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm964:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm964():
  {==}

assert tv964:
  Tup(n12())

def tv964():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm965:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm965():
  {==}

assert tv965:
  Tup(n15())

def tv965():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm966:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm966():
  {==}

assert tv966:
  Tup(n18())

def tv966():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm967:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm967():
  {==}

assert tv967:
  Tup(n21())

def tv967():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm968:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm968():
  {==}

assert tv968:
  Tup(n24())

def tv968():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm969:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm969():
  {==}

assert tv969:
  Tup(n27())

def tv969():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm970:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm970():
  {==}

assert tv970:
  Tup(n30())

def tv970():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm971:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm971():
  {==}

assert tv971:
  Tup(n5())

def tv971():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm972:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm972():
  {==}

assert tv972:
  Tup(n8())

def tv972():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm973:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm973():
  {==}

assert tv973:
  Tup(n11())

def tv973():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm974:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm974():
  {==}

assert tv974:
  Tup(n14())

def tv974():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm975:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm975():
  {==}

assert tv975:
  Tup(n17())

def tv975():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm976:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm976():
  {==}

assert tv976:
  Tup(n20())

def tv976():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm977:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm977():
  {==}

assert tv977:
  Tup(n23())

def tv977():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm978:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm978():
  {==}

assert tv978:
  Tup(n26())

def tv978():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm979:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm979():
  {==}

assert tv979:
  Tup(n29())

def tv979():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm980:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm980():
  {==}

assert tv980:
  Tup(n4())

def tv980():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm981:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm981():
  {==}

assert tv981:
  Tup(n7())

def tv981():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm982:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm982():
  {==}

assert tv982:
  Tup(n10())

def tv982():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm983:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm983():
  {==}

assert tv983:
  Tup(n13())

def tv983():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm984:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm984():
  {==}

assert tv984:
  Tup(n16())

def tv984():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm985:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm985():
  {==}

assert tv985:
  Tup(n19())

def tv985():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm986:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm986():
  {==}

assert tv986:
  Tup(n22())

def tv986():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm987:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm987():
  {==}

assert tv987:
  Tup(n25())

def tv987():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm988:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm988():
  {==}

assert tv988:
  Tup(n28())

def tv988():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm989:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm989():
  {==}

assert tv989:
  Tup(n31())

def tv989():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm990:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm990():
  {==}

assert tv990:
  Tup(n6())

def tv990():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm991:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm991():
  {==}

assert tv991:
  Tup(n9())

def tv991():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm992:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm992():
  {==}

assert tv992:
  Tup(n12())

def tv992():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm993:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm993():
  {==}

assert tv993:
  Tup(n15())

def tv993():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm994:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm994():
  {==}

assert tv994:
  Tup(n18())

def tv994():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm995:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm995():
  {==}

assert tv995:
  Tup(n21())

def tv995():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm996:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm996():
  {==}

assert tv996:
  Tup(n24())

def tv996():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm997:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm997():
  {==}

assert tv997:
  Tup(n27())

def tv997():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm998:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm998():
  {==}

assert tv998:
  Tup(n30())

def tv998():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm999:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm999():
  {==}

assert tv999:
  Tup(n5())

def tv999():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1000:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1000():
  {==}

assert tv1000:
  Tup(n8())

def tv1000():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1001:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1001():
  {==}

assert tv1001:
  Tup(n11())

def tv1001():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1002:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1002():
  {==}

assert tv1002:
  Tup(n14())

def tv1002():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1003:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1003():
  {==}

assert tv1003:
  Tup(n17())

def tv1003():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1004:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1004():
  {==}

assert tv1004:
  Tup(n20())

def tv1004():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1005:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1005():
  {==}

assert tv1005:
  Tup(n23())

def tv1005():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1006:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1006():
  {==}

assert tv1006:
  Tup(n26())

def tv1006():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1007:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1007():
  {==}

assert tv1007:
  Tup(n29())

def tv1007():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1008:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1008():
  {==}

assert tv1008:
  Tup(n4())

def tv1008():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1009:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1009():
  {==}

assert tv1009:
  Tup(n7())

def tv1009():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1010:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1010():
  {==}

assert tv1010:
  Tup(n10())

def tv1010():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1011:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1011():
  {==}

assert tv1011:
  Tup(n13())

def tv1011():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1012:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1012():
  {==}

assert tv1012:
  Tup(n16())

def tv1012():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1013:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1013():
  {==}

assert tv1013:
  Tup(n19())

def tv1013():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1014:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1014():
  {==}

assert tv1014:
  Tup(n22())

def tv1014():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1015:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1015():
  {==}

assert tv1015:
  Tup(n25())

def tv1015():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1016:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1016():
  {==}

assert tv1016:
  Tup(n28())

def tv1016():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1017:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1017():
  {==}

assert tv1017:
  Tup(n31())

def tv1017():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1018:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1018():
  {==}

assert tv1018:
  Tup(n6())

def tv1018():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1019:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1019():
  {==}

assert tv1019:
  Tup(n9())

def tv1019():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1020:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1020():
  {==}

assert tv1020:
  Tup(n12())

def tv1020():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1021:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1021():
  {==}

assert tv1021:
  Tup(n15())

def tv1021():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1022:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1022():
  {==}

assert tv1022:
  Tup(n18())

def tv1022():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1023:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1023():
  {==}

assert tv1023:
  Tup(n21())

def tv1023():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1024:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1024():
  {==}

assert tv1024:
  Tup(n24())

def tv1024():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1025:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1025():
  {==}

assert tv1025:
  Tup(n27())

def tv1025():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1026:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1026():
  {==}

assert tv1026:
  Tup(n30())

def tv1026():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1027:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1027():
  {==}

assert tv1027:
  Tup(n5())

def tv1027():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1028:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1028():
  {==}

assert tv1028:
  Tup(n8())

def tv1028():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1029:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1029():
  {==}

assert tv1029:
  Tup(n11())

def tv1029():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1030:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1030():
  {==}

assert tv1030:
  Tup(n14())

def tv1030():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1031:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1031():
  {==}

assert tv1031:
  Tup(n17())

def tv1031():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1032:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1032():
  {==}

assert tv1032:
  Tup(n20())

def tv1032():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1033:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1033():
  {==}

assert tv1033:
  Tup(n23())

def tv1033():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1034:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1034():
  {==}

assert tv1034:
  Tup(n26())

def tv1034():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1035:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1035():
  {==}

assert tv1035:
  Tup(n29())

def tv1035():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1036:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1036():
  {==}

assert tv1036:
  Tup(n4())

def tv1036():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1037:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1037():
  {==}

assert tv1037:
  Tup(n7())

def tv1037():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1038:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1038():
  {==}

assert tv1038:
  Tup(n10())

def tv1038():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1039:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1039():
  {==}

assert tv1039:
  Tup(n13())

def tv1039():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1040:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1040():
  {==}

assert tv1040:
  Tup(n16())

def tv1040():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1041:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1041():
  {==}

assert tv1041:
  Tup(n19())

def tv1041():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1042:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1042():
  {==}

assert tv1042:
  Tup(n22())

def tv1042():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1043:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1043():
  {==}

assert tv1043:
  Tup(n25())

def tv1043():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1044:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1044():
  {==}

assert tv1044:
  Tup(n28())

def tv1044():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1045:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1045():
  {==}

assert tv1045:
  Tup(n31())

def tv1045():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1046:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1046():
  {==}

assert tv1046:
  Tup(n6())

def tv1046():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1047:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1047():
  {==}

assert tv1047:
  Tup(n9())

def tv1047():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1048:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1048():
  {==}

assert tv1048:
  Tup(n12())

def tv1048():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1049:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1049():
  {==}

assert tv1049:
  Tup(n15())

def tv1049():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1050:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1050():
  {==}

assert tv1050:
  Tup(n18())

def tv1050():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1051:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1051():
  {==}

assert tv1051:
  Tup(n21())

def tv1051():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1052:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1052():
  {==}

assert tv1052:
  Tup(n24())

def tv1052():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1053:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1053():
  {==}

assert tv1053:
  Tup(n27())

def tv1053():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1054:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1054():
  {==}

assert tv1054:
  Tup(n30())

def tv1054():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1055:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1055():
  {==}

assert tv1055:
  Tup(n5())

def tv1055():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1056:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1056():
  {==}

assert tv1056:
  Tup(n8())

def tv1056():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1057:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1057():
  {==}

assert tv1057:
  Tup(n11())

def tv1057():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1058:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1058():
  {==}

assert tv1058:
  Tup(n14())

def tv1058():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1059:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1059():
  {==}

assert tv1059:
  Tup(n17())

def tv1059():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1060:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1060():
  {==}

assert tv1060:
  Tup(n20())

def tv1060():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1061:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1061():
  {==}

assert tv1061:
  Tup(n23())

def tv1061():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1062:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1062():
  {==}

assert tv1062:
  Tup(n26())

def tv1062():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1063:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1063():
  {==}

assert tv1063:
  Tup(n29())

def tv1063():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1064:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1064():
  {==}

assert tv1064:
  Tup(n4())

def tv1064():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1065:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1065():
  {==}

assert tv1065:
  Tup(n7())

def tv1065():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1066:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1066():
  {==}

assert tv1066:
  Tup(n10())

def tv1066():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1067:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1067():
  {==}

assert tv1067:
  Tup(n13())

def tv1067():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1068:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1068():
  {==}

assert tv1068:
  Tup(n16())

def tv1068():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1069:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1069():
  {==}

assert tv1069:
  Tup(n19())

def tv1069():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1070:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1070():
  {==}

assert tv1070:
  Tup(n22())

def tv1070():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1071:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1071():
  {==}

assert tv1071:
  Tup(n25())

def tv1071():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1072:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1072():
  {==}

assert tv1072:
  Tup(n28())

def tv1072():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1073:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1073():
  {==}

assert tv1073:
  Tup(n31())

def tv1073():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1074:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1074():
  {==}

assert tv1074:
  Tup(n6())

def tv1074():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1075:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1075():
  {==}

assert tv1075:
  Tup(n9())

def tv1075():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1076:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1076():
  {==}

assert tv1076:
  Tup(n12())

def tv1076():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1077:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1077():
  {==}

assert tv1077:
  Tup(n15())

def tv1077():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1078:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1078():
  {==}

assert tv1078:
  Tup(n18())

def tv1078():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1079:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1079():
  {==}

assert tv1079:
  Tup(n21())

def tv1079():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1080:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1080():
  {==}

assert tv1080:
  Tup(n24())

def tv1080():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1081:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1081():
  {==}

assert tv1081:
  Tup(n27())

def tv1081():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1082:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1082():
  {==}

assert tv1082:
  Tup(n30())

def tv1082():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1083:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1083():
  {==}

assert tv1083:
  Tup(n5())

def tv1083():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1084:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1084():
  {==}

assert tv1084:
  Tup(n8())

def tv1084():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1085:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1085():
  {==}

assert tv1085:
  Tup(n11())

def tv1085():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1086:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1086():
  {==}

assert tv1086:
  Tup(n14())

def tv1086():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1087:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1087():
  {==}

assert tv1087:
  Tup(n17())

def tv1087():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1088:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1088():
  {==}

assert tv1088:
  Tup(n20())

def tv1088():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1089:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1089():
  {==}

assert tv1089:
  Tup(n23())

def tv1089():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1090:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1090():
  {==}

assert tv1090:
  Tup(n26())

def tv1090():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1091:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1091():
  {==}

assert tv1091:
  Tup(n29())

def tv1091():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1092:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1092():
  {==}

assert tv1092:
  Tup(n4())

def tv1092():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1093:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1093():
  {==}

assert tv1093:
  Tup(n7())

def tv1093():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1094:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1094():
  {==}

assert tv1094:
  Tup(n10())

def tv1094():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1095:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1095():
  {==}

assert tv1095:
  Tup(n13())

def tv1095():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1096:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1096():
  {==}

assert tv1096:
  Tup(n16())

def tv1096():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1097:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1097():
  {==}

assert tv1097:
  Tup(n19())

def tv1097():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1098:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1098():
  {==}

assert tv1098:
  Tup(n22())

def tv1098():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1099:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1099():
  {==}

assert tv1099:
  Tup(n25())

def tv1099():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1100:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1100():
  {==}

assert tv1100:
  Tup(n28())

def tv1100():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1101:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1101():
  {==}

assert tv1101:
  Tup(n31())

def tv1101():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1102:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1102():
  {==}

assert tv1102:
  Tup(n6())

def tv1102():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1103:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1103():
  {==}

assert tv1103:
  Tup(n9())

def tv1103():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1104:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1104():
  {==}

assert tv1104:
  Tup(n12())

def tv1104():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1105:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1105():
  {==}

assert tv1105:
  Tup(n15())

def tv1105():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1106:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1106():
  {==}

assert tv1106:
  Tup(n18())

def tv1106():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1107:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1107():
  {==}

assert tv1107:
  Tup(n21())

def tv1107():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1108:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1108():
  {==}

assert tv1108:
  Tup(n24())

def tv1108():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1109:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1109():
  {==}

assert tv1109:
  Tup(n27())

def tv1109():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1110:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1110():
  {==}

assert tv1110:
  Tup(n30())

def tv1110():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1111:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1111():
  {==}

assert tv1111:
  Tup(n5())

def tv1111():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1112:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1112():
  {==}

assert tv1112:
  Tup(n8())

def tv1112():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1113:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1113():
  {==}

assert tv1113:
  Tup(n11())

def tv1113():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1114:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1114():
  {==}

assert tv1114:
  Tup(n14())

def tv1114():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1115:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1115():
  {==}

assert tv1115:
  Tup(n17())

def tv1115():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1116:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1116():
  {==}

assert tv1116:
  Tup(n20())

def tv1116():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1117:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1117():
  {==}

assert tv1117:
  Tup(n23())

def tv1117():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1118:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1118():
  {==}

assert tv1118:
  Tup(n26())

def tv1118():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1119:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1119():
  {==}

assert tv1119:
  Tup(n29())

def tv1119():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1120:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1120():
  {==}

assert tv1120:
  Tup(n4())

def tv1120():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1121:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1121():
  {==}

assert tv1121:
  Tup(n7())

def tv1121():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1122:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1122():
  {==}

assert tv1122:
  Tup(n10())

def tv1122():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1123:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1123():
  {==}

assert tv1123:
  Tup(n13())

def tv1123():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1124:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1124():
  {==}

assert tv1124:
  Tup(n16())

def tv1124():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1125:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1125():
  {==}

assert tv1125:
  Tup(n19())

def tv1125():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1126:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1126():
  {==}

assert tv1126:
  Tup(n22())

def tv1126():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1127:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1127():
  {==}

assert tv1127:
  Tup(n25())

def tv1127():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1128:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1128():
  {==}

assert tv1128:
  Tup(n28())

def tv1128():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1129:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1129():
  {==}

assert tv1129:
  Tup(n31())

def tv1129():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1130:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1130():
  {==}

assert tv1130:
  Tup(n6())

def tv1130():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1131:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1131():
  {==}

assert tv1131:
  Tup(n9())

def tv1131():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1132:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1132():
  {==}

assert tv1132:
  Tup(n12())

def tv1132():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1133:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1133():
  {==}

assert tv1133:
  Tup(n15())

def tv1133():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1134:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1134():
  {==}

assert tv1134:
  Tup(n18())

def tv1134():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1135:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1135():
  {==}

assert tv1135:
  Tup(n21())

def tv1135():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1136:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1136():
  {==}

assert tv1136:
  Tup(n24())

def tv1136():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1137:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1137():
  {==}

assert tv1137:
  Tup(n27())

def tv1137():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1138:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1138():
  {==}

assert tv1138:
  Tup(n30())

def tv1138():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1139:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1139():
  {==}

assert tv1139:
  Tup(n5())

def tv1139():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1140:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1140():
  {==}

assert tv1140:
  Tup(n8())

def tv1140():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1141:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1141():
  {==}

assert tv1141:
  Tup(n11())

def tv1141():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1142:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1142():
  {==}

assert tv1142:
  Tup(n14())

def tv1142():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1143:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1143():
  {==}

assert tv1143:
  Tup(n17())

def tv1143():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1144:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1144():
  {==}

assert tv1144:
  Tup(n20())

def tv1144():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1145:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1145():
  {==}

assert tv1145:
  Tup(n23())

def tv1145():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1146:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1146():
  {==}

assert tv1146:
  Tup(n26())

def tv1146():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1147:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1147():
  {==}

assert tv1147:
  Tup(n29())

def tv1147():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1148:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1148():
  {==}

assert tv1148:
  Tup(n4())

def tv1148():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1149:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1149():
  {==}

assert tv1149:
  Tup(n7())

def tv1149():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1150:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1150():
  {==}

assert tv1150:
  Tup(n10())

def tv1150():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1151:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1151():
  {==}

assert tv1151:
  Tup(n13())

def tv1151():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1152:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1152():
  {==}

assert tv1152:
  Tup(n16())

def tv1152():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1153:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1153():
  {==}

assert tv1153:
  Tup(n19())

def tv1153():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1154:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1154():
  {==}

assert tv1154:
  Tup(n22())

def tv1154():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1155:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1155():
  {==}

assert tv1155:
  Tup(n25())

def tv1155():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1156:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1156():
  {==}

assert tv1156:
  Tup(n28())

def tv1156():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1157:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1157():
  {==}

assert tv1157:
  Tup(n31())

def tv1157():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1158:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1158():
  {==}

assert tv1158:
  Tup(n6())

def tv1158():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1159:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1159():
  {==}

assert tv1159:
  Tup(n9())

def tv1159():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1160:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1160():
  {==}

assert tv1160:
  Tup(n12())

def tv1160():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1161:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1161():
  {==}

assert tv1161:
  Tup(n15())

def tv1161():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1162:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1162():
  {==}

assert tv1162:
  Tup(n18())

def tv1162():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1163:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1163():
  {==}

assert tv1163:
  Tup(n21())

def tv1163():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1164:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1164():
  {==}

assert tv1164:
  Tup(n24())

def tv1164():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1165:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1165():
  {==}

assert tv1165:
  Tup(n27())

def tv1165():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1166:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1166():
  {==}

assert tv1166:
  Tup(n30())

def tv1166():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1167:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1167():
  {==}

assert tv1167:
  Tup(n5())

def tv1167():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1168:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1168():
  {==}

assert tv1168:
  Tup(n8())

def tv1168():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1169:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1169():
  {==}

assert tv1169:
  Tup(n11())

def tv1169():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1170:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1170():
  {==}

assert tv1170:
  Tup(n14())

def tv1170():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1171:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1171():
  {==}

assert tv1171:
  Tup(n17())

def tv1171():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1172:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1172():
  {==}

assert tv1172:
  Tup(n20())

def tv1172():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1173:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1173():
  {==}

assert tv1173:
  Tup(n23())

def tv1173():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1174:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1174():
  {==}

assert tv1174:
  Tup(n26())

def tv1174():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1175:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1175():
  {==}

assert tv1175:
  Tup(n29())

def tv1175():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1176:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1176():
  {==}

assert tv1176:
  Tup(n4())

def tv1176():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1177:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1177():
  {==}

assert tv1177:
  Tup(n7())

def tv1177():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1178:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1178():
  {==}

assert tv1178:
  Tup(n10())

def tv1178():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1179:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1179():
  {==}

assert tv1179:
  Tup(n13())

def tv1179():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1180:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1180():
  {==}

assert tv1180:
  Tup(n16())

def tv1180():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1181:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1181():
  {==}

assert tv1181:
  Tup(n19())

def tv1181():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1182:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1182():
  {==}

assert tv1182:
  Tup(n22())

def tv1182():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1183:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1183():
  {==}

assert tv1183:
  Tup(n25())

def tv1183():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1184:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1184():
  {==}

assert tv1184:
  Tup(n28())

def tv1184():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1185:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1185():
  {==}

assert tv1185:
  Tup(n31())

def tv1185():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1186:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1186():
  {==}

assert tv1186:
  Tup(n6())

def tv1186():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1187:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1187():
  {==}

assert tv1187:
  Tup(n9())

def tv1187():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1188:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1188():
  {==}

assert tv1188:
  Tup(n12())

def tv1188():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1189:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1189():
  {==}

assert tv1189:
  Tup(n15())

def tv1189():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1190:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1190():
  {==}

assert tv1190:
  Tup(n18())

def tv1190():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1191:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1191():
  {==}

assert tv1191:
  Tup(n21())

def tv1191():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1192:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1192():
  {==}

assert tv1192:
  Tup(n24())

def tv1192():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1193:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1193():
  {==}

assert tv1193:
  Tup(n27())

def tv1193():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1194:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1194():
  {==}

assert tv1194:
  Tup(n30())

def tv1194():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1195:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1195():
  {==}

assert tv1195:
  Tup(n5())

def tv1195():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1196:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1196():
  {==}

assert tv1196:
  Tup(n8())

def tv1196():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1197:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1197():
  {==}

assert tv1197:
  Tup(n11())

def tv1197():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1198:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1198():
  {==}

assert tv1198:
  Tup(n14())

def tv1198():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1199:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1199():
  {==}

assert tv1199:
  Tup(n17())

def tv1199():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1200:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1200():
  {==}

assert tv1200:
  Tup(n20())

def tv1200():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1201:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1201():
  {==}

assert tv1201:
  Tup(n23())

def tv1201():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1202:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1202():
  {==}

assert tv1202:
  Tup(n26())

def tv1202():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1203:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1203():
  {==}

assert tv1203:
  Tup(n29())

def tv1203():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1204:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1204():
  {==}

assert tv1204:
  Tup(n4())

def tv1204():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1205:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1205():
  {==}

assert tv1205:
  Tup(n7())

def tv1205():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1206:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1206():
  {==}

assert tv1206:
  Tup(n10())

def tv1206():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1207:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1207():
  {==}

assert tv1207:
  Tup(n13())

def tv1207():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1208:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1208():
  {==}

assert tv1208:
  Tup(n16())

def tv1208():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1209:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1209():
  {==}

assert tv1209:
  Tup(n19())

def tv1209():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1210:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1210():
  {==}

assert tv1210:
  Tup(n22())

def tv1210():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1211:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1211():
  {==}

assert tv1211:
  Tup(n25())

def tv1211():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1212:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1212():
  {==}

assert tv1212:
  Tup(n28())

def tv1212():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1213:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1213():
  {==}

assert tv1213:
  Tup(n31())

def tv1213():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1214:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1214():
  {==}

assert tv1214:
  Tup(n6())

def tv1214():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1215:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1215():
  {==}

assert tv1215:
  Tup(n9())

def tv1215():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1216:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1216():
  {==}

assert tv1216:
  Tup(n12())

def tv1216():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1217:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1217():
  {==}

assert tv1217:
  Tup(n15())

def tv1217():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1218:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1218():
  {==}

assert tv1218:
  Tup(n18())

def tv1218():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1219:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1219():
  {==}

assert tv1219:
  Tup(n21())

def tv1219():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1220:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1220():
  {==}

assert tv1220:
  Tup(n24())

def tv1220():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1221:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1221():
  {==}

assert tv1221:
  Tup(n27())

def tv1221():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1222:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1222():
  {==}

assert tv1222:
  Tup(n30())

def tv1222():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1223:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1223():
  {==}

assert tv1223:
  Tup(n5())

def tv1223():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1224:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1224():
  {==}

assert tv1224:
  Tup(n8())

def tv1224():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1225:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1225():
  {==}

assert tv1225:
  Tup(n11())

def tv1225():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1226:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1226():
  {==}

assert tv1226:
  Tup(n14())

def tv1226():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1227:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1227():
  {==}

assert tv1227:
  Tup(n17())

def tv1227():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1228:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1228():
  {==}

assert tv1228:
  Tup(n20())

def tv1228():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1229:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1229():
  {==}

assert tv1229:
  Tup(n23())

def tv1229():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1230:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1230():
  {==}

assert tv1230:
  Tup(n26())

def tv1230():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1231:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1231():
  {==}

assert tv1231:
  Tup(n29())

def tv1231():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1232:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1232():
  {==}

assert tv1232:
  Tup(n4())

def tv1232():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1233:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1233():
  {==}

assert tv1233:
  Tup(n7())

def tv1233():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1234:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1234():
  {==}

assert tv1234:
  Tup(n10())

def tv1234():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1235:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1235():
  {==}

assert tv1235:
  Tup(n13())

def tv1235():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1236:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1236():
  {==}

assert tv1236:
  Tup(n16())

def tv1236():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1237:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1237():
  {==}

assert tv1237:
  Tup(n19())

def tv1237():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1238:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1238():
  {==}

assert tv1238:
  Tup(n22())

def tv1238():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1239:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1239():
  {==}

assert tv1239:
  Tup(n25())

def tv1239():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1240:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1240():
  {==}

assert tv1240:
  Tup(n28())

def tv1240():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1241:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1241():
  {==}

assert tv1241:
  Tup(n31())

def tv1241():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1242:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1242():
  {==}

assert tv1242:
  Tup(n6())

def tv1242():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1243:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1243():
  {==}

assert tv1243:
  Tup(n9())

def tv1243():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1244:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1244():
  {==}

assert tv1244:
  Tup(n12())

def tv1244():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1245:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1245():
  {==}

assert tv1245:
  Tup(n15())

def tv1245():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1246:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1246():
  {==}

assert tv1246:
  Tup(n18())

def tv1246():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1247:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1247():
  {==}

assert tv1247:
  Tup(n21())

def tv1247():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1248:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1248():
  {==}

assert tv1248:
  Tup(n24())

def tv1248():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1249:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1249():
  {==}

assert tv1249:
  Tup(n27())

def tv1249():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1250:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1250():
  {==}

assert tv1250:
  Tup(n30())

def tv1250():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1251:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1251():
  {==}

assert tv1251:
  Tup(n5())

def tv1251():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1252:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1252():
  {==}

assert tv1252:
  Tup(n8())

def tv1252():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1253:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1253():
  {==}

assert tv1253:
  Tup(n11())

def tv1253():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1254:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1254():
  {==}

assert tv1254:
  Tup(n14())

def tv1254():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1255:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1255():
  {==}

assert tv1255:
  Tup(n17())

def tv1255():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1256:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1256():
  {==}

assert tv1256:
  Tup(n20())

def tv1256():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1257:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1257():
  {==}

assert tv1257:
  Tup(n23())

def tv1257():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1258:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1258():
  {==}

assert tv1258:
  Tup(n26())

def tv1258():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1259:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1259():
  {==}

assert tv1259:
  Tup(n29())

def tv1259():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1260:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1260():
  {==}

assert tv1260:
  Tup(n4())

def tv1260():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1261:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1261():
  {==}

assert tv1261:
  Tup(n7())

def tv1261():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1262:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1262():
  {==}

assert tv1262:
  Tup(n10())

def tv1262():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1263:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1263():
  {==}

assert tv1263:
  Tup(n13())

def tv1263():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1264:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1264():
  {==}

assert tv1264:
  Tup(n16())

def tv1264():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1265:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1265():
  {==}

assert tv1265:
  Tup(n19())

def tv1265():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1266:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1266():
  {==}

assert tv1266:
  Tup(n22())

def tv1266():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1267:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1267():
  {==}

assert tv1267:
  Tup(n25())

def tv1267():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1268:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1268():
  {==}

assert tv1268:
  Tup(n28())

def tv1268():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1269:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1269():
  {==}

assert tv1269:
  Tup(n31())

def tv1269():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1270:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1270():
  {==}

assert tv1270:
  Tup(n6())

def tv1270():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1271:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1271():
  {==}

assert tv1271:
  Tup(n9())

def tv1271():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1272:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1272():
  {==}

assert tv1272:
  Tup(n12())

def tv1272():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1273:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1273():
  {==}

assert tv1273:
  Tup(n15())

def tv1273():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1274:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1274():
  {==}

assert tv1274:
  Tup(n18())

def tv1274():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1275:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1275():
  {==}

assert tv1275:
  Tup(n21())

def tv1275():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1276:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1276():
  {==}

assert tv1276:
  Tup(n24())

def tv1276():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1277:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1277():
  {==}

assert tv1277:
  Tup(n27())

def tv1277():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1278:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1278():
  {==}

assert tv1278:
  Tup(n30())

def tv1278():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1279:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1279():
  {==}

assert tv1279:
  Tup(n5())

def tv1279():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1280:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1280():
  {==}

assert tv1280:
  Tup(n8())

def tv1280():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1281:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1281():
  {==}

assert tv1281:
  Tup(n11())

def tv1281():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1282:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1282():
  {==}

assert tv1282:
  Tup(n14())

def tv1282():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1283:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1283():
  {==}

assert tv1283:
  Tup(n17())

def tv1283():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1284:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1284():
  {==}

assert tv1284:
  Tup(n20())

def tv1284():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1285:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1285():
  {==}

assert tv1285:
  Tup(n23())

def tv1285():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1286:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1286():
  {==}

assert tv1286:
  Tup(n26())

def tv1286():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1287:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1287():
  {==}

assert tv1287:
  Tup(n29())

def tv1287():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1288:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1288():
  {==}

assert tv1288:
  Tup(n4())

def tv1288():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1289:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1289():
  {==}

assert tv1289:
  Tup(n7())

def tv1289():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1290:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1290():
  {==}

assert tv1290:
  Tup(n10())

def tv1290():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1291:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1291():
  {==}

assert tv1291:
  Tup(n13())

def tv1291():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1292:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1292():
  {==}

assert tv1292:
  Tup(n16())

def tv1292():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1293:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1293():
  {==}

assert tv1293:
  Tup(n19())

def tv1293():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1294:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1294():
  {==}

assert tv1294:
  Tup(n22())

def tv1294():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1295:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1295():
  {==}

assert tv1295:
  Tup(n25())

def tv1295():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1296:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1296():
  {==}

assert tv1296:
  Tup(n28())

def tv1296():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1297:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1297():
  {==}

assert tv1297:
  Tup(n31())

def tv1297():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1298:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1298():
  {==}

assert tv1298:
  Tup(n6())

def tv1298():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1299:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1299():
  {==}

assert tv1299:
  Tup(n9())

def tv1299():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1300:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1300():
  {==}

assert tv1300:
  Tup(n12())

def tv1300():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1301:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1301():
  {==}

assert tv1301:
  Tup(n15())

def tv1301():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1302:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1302():
  {==}

assert tv1302:
  Tup(n18())

def tv1302():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1303:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1303():
  {==}

assert tv1303:
  Tup(n21())

def tv1303():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1304:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1304():
  {==}

assert tv1304:
  Tup(n24())

def tv1304():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1305:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1305():
  {==}

assert tv1305:
  Tup(n27())

def tv1305():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1306:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1306():
  {==}

assert tv1306:
  Tup(n30())

def tv1306():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1307:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1307():
  {==}

assert tv1307:
  Tup(n5())

def tv1307():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1308:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1308():
  {==}

assert tv1308:
  Tup(n8())

def tv1308():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1309:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1309():
  {==}

assert tv1309:
  Tup(n11())

def tv1309():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1310:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1310():
  {==}

assert tv1310:
  Tup(n14())

def tv1310():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1311:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1311():
  {==}

assert tv1311:
  Tup(n17())

def tv1311():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1312:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1312():
  {==}

assert tv1312:
  Tup(n20())

def tv1312():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1313:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1313():
  {==}

assert tv1313:
  Tup(n23())

def tv1313():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1314:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1314():
  {==}

assert tv1314:
  Tup(n26())

def tv1314():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1315:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1315():
  {==}

assert tv1315:
  Tup(n29())

def tv1315():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1316:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1316():
  {==}

assert tv1316:
  Tup(n4())

def tv1316():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1317:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1317():
  {==}

assert tv1317:
  Tup(n7())

def tv1317():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1318:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1318():
  {==}

assert tv1318:
  Tup(n10())

def tv1318():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1319:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1319():
  {==}

assert tv1319:
  Tup(n13())

def tv1319():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1320:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1320():
  {==}

assert tv1320:
  Tup(n16())

def tv1320():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1321:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1321():
  {==}

assert tv1321:
  Tup(n19())

def tv1321():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1322:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1322():
  {==}

assert tv1322:
  Tup(n22())

def tv1322():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1323:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1323():
  {==}

assert tv1323:
  Tup(n25())

def tv1323():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1324:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1324():
  {==}

assert tv1324:
  Tup(n28())

def tv1324():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1325:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1325():
  {==}

assert tv1325:
  Tup(n31())

def tv1325():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1326:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1326():
  {==}

assert tv1326:
  Tup(n6())

def tv1326():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1327:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1327():
  {==}

assert tv1327:
  Tup(n9())

def tv1327():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1328:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1328():
  {==}

assert tv1328:
  Tup(n12())

def tv1328():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1329:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1329():
  {==}

assert tv1329:
  Tup(n15())

def tv1329():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1330:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1330():
  {==}

assert tv1330:
  Tup(n18())

def tv1330():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1331:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1331():
  {==}

assert tv1331:
  Tup(n21())

def tv1331():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1332:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1332():
  {==}

assert tv1332:
  Tup(n24())

def tv1332():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1333:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1333():
  {==}

assert tv1333:
  Tup(n27())

def tv1333():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1334:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1334():
  {==}

assert tv1334:
  Tup(n30())

def tv1334():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1335:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1335():
  {==}

assert tv1335:
  Tup(n5())

def tv1335():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1336:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1336():
  {==}

assert tv1336:
  Tup(n8())

def tv1336():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1337:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1337():
  {==}

assert tv1337:
  Tup(n11())

def tv1337():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1338:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1338():
  {==}

assert tv1338:
  Tup(n14())

def tv1338():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1339:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1339():
  {==}

assert tv1339:
  Tup(n17())

def tv1339():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1340:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1340():
  {==}

assert tv1340:
  Tup(n20())

def tv1340():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1341:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1341():
  {==}

assert tv1341:
  Tup(n23())

def tv1341():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1342:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1342():
  {==}

assert tv1342:
  Tup(n26())

def tv1342():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1343:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1343():
  {==}

assert tv1343:
  Tup(n29())

def tv1343():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1344:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1344():
  {==}

assert tv1344:
  Tup(n4())

def tv1344():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1345:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1345():
  {==}

assert tv1345:
  Tup(n7())

def tv1345():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1346:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1346():
  {==}

assert tv1346:
  Tup(n10())

def tv1346():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1347:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1347():
  {==}

assert tv1347:
  Tup(n13())

def tv1347():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1348:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1348():
  {==}

assert tv1348:
  Tup(n16())

def tv1348():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1349:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1349():
  {==}

assert tv1349:
  Tup(n19())

def tv1349():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1350:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1350():
  {==}

assert tv1350:
  Tup(n22())

def tv1350():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1351:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1351():
  {==}

assert tv1351:
  Tup(n25())

def tv1351():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1352:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1352():
  {==}

assert tv1352:
  Tup(n28())

def tv1352():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1353:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1353():
  {==}

assert tv1353:
  Tup(n31())

def tv1353():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1354:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1354():
  {==}

assert tv1354:
  Tup(n6())

def tv1354():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1355:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1355():
  {==}

assert tv1355:
  Tup(n9())

def tv1355():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1356:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1356():
  {==}

assert tv1356:
  Tup(n12())

def tv1356():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1357:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1357():
  {==}

assert tv1357:
  Tup(n15())

def tv1357():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1358:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1358():
  {==}

assert tv1358:
  Tup(n18())

def tv1358():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1359:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1359():
  {==}

assert tv1359:
  Tup(n21())

def tv1359():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1360:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1360():
  {==}

assert tv1360:
  Tup(n24())

def tv1360():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1361:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1361():
  {==}

assert tv1361:
  Tup(n27())

def tv1361():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1362:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1362():
  {==}

assert tv1362:
  Tup(n30())

def tv1362():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1363:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1363():
  {==}

assert tv1363:
  Tup(n5())

def tv1363():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1364:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1364():
  {==}

assert tv1364:
  Tup(n8())

def tv1364():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1365:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1365():
  {==}

assert tv1365:
  Tup(n11())

def tv1365():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1366:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1366():
  {==}

assert tv1366:
  Tup(n14())

def tv1366():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1367:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1367():
  {==}

assert tv1367:
  Tup(n17())

def tv1367():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1368:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1368():
  {==}

assert tv1368:
  Tup(n20())

def tv1368():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1369:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1369():
  {==}

assert tv1369:
  Tup(n23())

def tv1369():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1370:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1370():
  {==}

assert tv1370:
  Tup(n26())

def tv1370():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1371:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1371():
  {==}

assert tv1371:
  Tup(n29())

def tv1371():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1372:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1372():
  {==}

assert tv1372:
  Tup(n4())

def tv1372():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1373:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1373():
  {==}

assert tv1373:
  Tup(n7())

def tv1373():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1374:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1374():
  {==}

assert tv1374:
  Tup(n10())

def tv1374():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1375:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1375():
  {==}

assert tv1375:
  Tup(n13())

def tv1375():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1376:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1376():
  {==}

assert tv1376:
  Tup(n16())

def tv1376():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1377:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1377():
  {==}

assert tv1377:
  Tup(n19())

def tv1377():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1378:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1378():
  {==}

assert tv1378:
  Tup(n22())

def tv1378():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1379:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1379():
  {==}

assert tv1379:
  Tup(n25())

def tv1379():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1380:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1380():
  {==}

assert tv1380:
  Tup(n28())

def tv1380():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1381:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1381():
  {==}

assert tv1381:
  Tup(n31())

def tv1381():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1382:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1382():
  {==}

assert tv1382:
  Tup(n6())

def tv1382():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1383:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1383():
  {==}

assert tv1383:
  Tup(n9())

def tv1383():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1384:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1384():
  {==}

assert tv1384:
  Tup(n12())

def tv1384():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1385:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1385():
  {==}

assert tv1385:
  Tup(n15())

def tv1385():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1386:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1386():
  {==}

assert tv1386:
  Tup(n18())

def tv1386():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1387:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1387():
  {==}

assert tv1387:
  Tup(n21())

def tv1387():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1388:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1388():
  {==}

assert tv1388:
  Tup(n24())

def tv1388():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1389:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1389():
  {==}

assert tv1389:
  Tup(n27())

def tv1389():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1390:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1390():
  {==}

assert tv1390:
  Tup(n30())

def tv1390():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1391:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1391():
  {==}

assert tv1391:
  Tup(n5())

def tv1391():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1392:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1392():
  {==}

assert tv1392:
  Tup(n8())

def tv1392():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1393:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1393():
  {==}

assert tv1393:
  Tup(n11())

def tv1393():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1394:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1394():
  {==}

assert tv1394:
  Tup(n14())

def tv1394():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1395:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1395():
  {==}

assert tv1395:
  Tup(n17())

def tv1395():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1396:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1396():
  {==}

assert tv1396:
  Tup(n20())

def tv1396():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1397:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1397():
  {==}

assert tv1397:
  Tup(n23())

def tv1397():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1398:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1398():
  {==}

assert tv1398:
  Tup(n26())

def tv1398():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1399:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1399():
  {==}

assert tv1399:
  Tup(n29())

def tv1399():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1400:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1400():
  {==}

assert tv1400:
  Tup(n4())

def tv1400():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1401:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1401():
  {==}

assert tv1401:
  Tup(n7())

def tv1401():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1402:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1402():
  {==}

assert tv1402:
  Tup(n10())

def tv1402():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1403:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1403():
  {==}

assert tv1403:
  Tup(n13())

def tv1403():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1404:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1404():
  {==}

assert tv1404:
  Tup(n16())

def tv1404():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1405:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1405():
  {==}

assert tv1405:
  Tup(n19())

def tv1405():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1406:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1406():
  {==}

assert tv1406:
  Tup(n22())

def tv1406():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1407:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1407():
  {==}

assert tv1407:
  Tup(n25())

def tv1407():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1408:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1408():
  {==}

assert tv1408:
  Tup(n28())

def tv1408():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1409:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1409():
  {==}

assert tv1409:
  Tup(n31())

def tv1409():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1410:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1410():
  {==}

assert tv1410:
  Tup(n6())

def tv1410():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1411:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1411():
  {==}

assert tv1411:
  Tup(n9())

def tv1411():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1412:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1412():
  {==}

assert tv1412:
  Tup(n12())

def tv1412():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1413:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1413():
  {==}

assert tv1413:
  Tup(n15())

def tv1413():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1414:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1414():
  {==}

assert tv1414:
  Tup(n18())

def tv1414():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1415:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1415():
  {==}

assert tv1415:
  Tup(n21())

def tv1415():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1416:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1416():
  {==}

assert tv1416:
  Tup(n24())

def tv1416():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1417:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1417():
  {==}

assert tv1417:
  Tup(n27())

def tv1417():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1418:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1418():
  {==}

assert tv1418:
  Tup(n30())

def tv1418():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1419:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1419():
  {==}

assert tv1419:
  Tup(n5())

def tv1419():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1420:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1420():
  {==}

assert tv1420:
  Tup(n8())

def tv1420():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1421:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1421():
  {==}

assert tv1421:
  Tup(n11())

def tv1421():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1422:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1422():
  {==}

assert tv1422:
  Tup(n14())

def tv1422():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1423:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1423():
  {==}

assert tv1423:
  Tup(n17())

def tv1423():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1424:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1424():
  {==}

assert tv1424:
  Tup(n20())

def tv1424():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1425:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1425():
  {==}

assert tv1425:
  Tup(n23())

def tv1425():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1426:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1426():
  {==}

assert tv1426:
  Tup(n26())

def tv1426():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1427:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1427():
  {==}

assert tv1427:
  Tup(n29())

def tv1427():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1428:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1428():
  {==}

assert tv1428:
  Tup(n4())

def tv1428():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1429:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1429():
  {==}

assert tv1429:
  Tup(n7())

def tv1429():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1430:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1430():
  {==}

assert tv1430:
  Tup(n10())

def tv1430():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1431:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1431():
  {==}

assert tv1431:
  Tup(n13())

def tv1431():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1432:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1432():
  {==}

assert tv1432:
  Tup(n16())

def tv1432():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1433:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1433():
  {==}

assert tv1433:
  Tup(n19())

def tv1433():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1434:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1434():
  {==}

assert tv1434:
  Tup(n22())

def tv1434():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1435:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1435():
  {==}

assert tv1435:
  Tup(n25())

def tv1435():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1436:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1436():
  {==}

assert tv1436:
  Tup(n28())

def tv1436():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1437:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1437():
  {==}

assert tv1437:
  Tup(n31())

def tv1437():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1438:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1438():
  {==}

assert tv1438:
  Tup(n6())

def tv1438():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1439:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1439():
  {==}

assert tv1439:
  Tup(n9())

def tv1439():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1440:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1440():
  {==}

assert tv1440:
  Tup(n12())

def tv1440():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1441:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1441():
  {==}

assert tv1441:
  Tup(n15())

def tv1441():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1442:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1442():
  {==}

assert tv1442:
  Tup(n18())

def tv1442():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1443:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1443():
  {==}

assert tv1443:
  Tup(n21())

def tv1443():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1444:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1444():
  {==}

assert tv1444:
  Tup(n24())

def tv1444():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1445:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1445():
  {==}

assert tv1445:
  Tup(n27())

def tv1445():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1446:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1446():
  {==}

assert tv1446:
  Tup(n30())

def tv1446():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1447:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1447():
  {==}

assert tv1447:
  Tup(n5())

def tv1447():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1448:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1448():
  {==}

assert tv1448:
  Tup(n8())

def tv1448():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1449:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1449():
  {==}

assert tv1449:
  Tup(n11())

def tv1449():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1450:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1450():
  {==}

assert tv1450:
  Tup(n14())

def tv1450():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1451:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1451():
  {==}

assert tv1451:
  Tup(n17())

def tv1451():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1452:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1452():
  {==}

assert tv1452:
  Tup(n20())

def tv1452():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1453:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1453():
  {==}

assert tv1453:
  Tup(n23())

def tv1453():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1454:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1454():
  {==}

assert tv1454:
  Tup(n26())

def tv1454():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1455:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1455():
  {==}

assert tv1455:
  Tup(n29())

def tv1455():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1456:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1456():
  {==}

assert tv1456:
  Tup(n4())

def tv1456():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1457:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1457():
  {==}

assert tv1457:
  Tup(n7())

def tv1457():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1458:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1458():
  {==}

assert tv1458:
  Tup(n10())

def tv1458():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1459:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1459():
  {==}

assert tv1459:
  Tup(n13())

def tv1459():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1460:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1460():
  {==}

assert tv1460:
  Tup(n16())

def tv1460():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1461:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1461():
  {==}

assert tv1461:
  Tup(n19())

def tv1461():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1462:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1462():
  {==}

assert tv1462:
  Tup(n22())

def tv1462():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1463:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1463():
  {==}

assert tv1463:
  Tup(n25())

def tv1463():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1464:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1464():
  {==}

assert tv1464:
  Tup(n28())

def tv1464():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1465:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1465():
  {==}

assert tv1465:
  Tup(n31())

def tv1465():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1466:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1466():
  {==}

assert tv1466:
  Tup(n6())

def tv1466():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1467:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1467():
  {==}

assert tv1467:
  Tup(n9())

def tv1467():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1468:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1468():
  {==}

assert tv1468:
  Tup(n12())

def tv1468():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1469:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1469():
  {==}

assert tv1469:
  Tup(n15())

def tv1469():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1470:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1470():
  {==}

assert tv1470:
  Tup(n18())

def tv1470():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1471:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1471():
  {==}

assert tv1471:
  Tup(n21())

def tv1471():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1472:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1472():
  {==}

assert tv1472:
  Tup(n24())

def tv1472():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1473:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1473():
  {==}

assert tv1473:
  Tup(n27())

def tv1473():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1474:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1474():
  {==}

assert tv1474:
  Tup(n30())

def tv1474():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1475:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1475():
  {==}

assert tv1475:
  Tup(n5())

def tv1475():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1476:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1476():
  {==}

assert tv1476:
  Tup(n8())

def tv1476():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1477:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1477():
  {==}

assert tv1477:
  Tup(n11())

def tv1477():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1478:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1478():
  {==}

assert tv1478:
  Tup(n14())

def tv1478():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1479:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1479():
  {==}

assert tv1479:
  Tup(n17())

def tv1479():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1480:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1480():
  {==}

assert tv1480:
  Tup(n20())

def tv1480():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1481:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1481():
  {==}

assert tv1481:
  Tup(n23())

def tv1481():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1482:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1482():
  {==}

assert tv1482:
  Tup(n26())

def tv1482():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1483:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1483():
  {==}

assert tv1483:
  Tup(n29())

def tv1483():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1484:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1484():
  {==}

assert tv1484:
  Tup(n4())

def tv1484():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1485:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1485():
  {==}

assert tv1485:
  Tup(n7())

def tv1485():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1486:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1486():
  {==}

assert tv1486:
  Tup(n10())

def tv1486():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1487:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1487():
  {==}

assert tv1487:
  Tup(n13())

def tv1487():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1488:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1488():
  {==}

assert tv1488:
  Tup(n16())

def tv1488():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1489:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1489():
  {==}

assert tv1489:
  Tup(n19())

def tv1489():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1490:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1490():
  {==}

assert tv1490:
  Tup(n22())

def tv1490():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1491:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1491():
  {==}

assert tv1491:
  Tup(n25())

def tv1491():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1492:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1492():
  {==}

assert tv1492:
  Tup(n28())

def tv1492():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1493:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1493():
  {==}

assert tv1493:
  Tup(n31())

def tv1493():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1494:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1494():
  {==}

assert tv1494:
  Tup(n6())

def tv1494():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1495:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1495():
  {==}

assert tv1495:
  Tup(n9())

def tv1495():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1496:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1496():
  {==}

assert tv1496:
  Tup(n12())

def tv1496():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1497:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1497():
  {==}

assert tv1497:
  Tup(n15())

def tv1497():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1498:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1498():
  {==}

assert tv1498:
  Tup(n18())

def tv1498():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1499:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1499():
  {==}

assert tv1499:
  Tup(n21())

def tv1499():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1500:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1500():
  {==}

assert tv1500:
  Tup(n24())

def tv1500():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1501:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1501():
  {==}

assert tv1501:
  Tup(n27())

def tv1501():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1502:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1502():
  {==}

assert tv1502:
  Tup(n30())

def tv1502():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1503:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1503():
  {==}

assert tv1503:
  Tup(n5())

def tv1503():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1504:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1504():
  {==}

assert tv1504:
  Tup(n8())

def tv1504():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1505:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1505():
  {==}

assert tv1505:
  Tup(n11())

def tv1505():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1506:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1506():
  {==}

assert tv1506:
  Tup(n14())

def tv1506():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1507:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1507():
  {==}

assert tv1507:
  Tup(n17())

def tv1507():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1508:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1508():
  {==}

assert tv1508:
  Tup(n20())

def tv1508():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1509:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1509():
  {==}

assert tv1509:
  Tup(n23())

def tv1509():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1510:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1510():
  {==}

assert tv1510:
  Tup(n26())

def tv1510():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1511:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1511():
  {==}

assert tv1511:
  Tup(n29())

def tv1511():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1512:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1512():
  {==}

assert tv1512:
  Tup(n4())

def tv1512():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1513:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1513():
  {==}

assert tv1513:
  Tup(n7())

def tv1513():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1514:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1514():
  {==}

assert tv1514:
  Tup(n10())

def tv1514():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1515:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1515():
  {==}

assert tv1515:
  Tup(n13())

def tv1515():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1516:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1516():
  {==}

assert tv1516:
  Tup(n16())

def tv1516():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1517:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1517():
  {==}

assert tv1517:
  Tup(n19())

def tv1517():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1518:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1518():
  {==}

assert tv1518:
  Tup(n22())

def tv1518():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1519:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1519():
  {==}

assert tv1519:
  Tup(n25())

def tv1519():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1520:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1520():
  {==}

assert tv1520:
  Tup(n28())

def tv1520():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1521:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1521():
  {==}

assert tv1521:
  Tup(n31())

def tv1521():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1522:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1522():
  {==}

assert tv1522:
  Tup(n6())

def tv1522():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1523:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1523():
  {==}

assert tv1523:
  Tup(n9())

def tv1523():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1524:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1524():
  {==}

assert tv1524:
  Tup(n12())

def tv1524():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1525:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1525():
  {==}

assert tv1525:
  Tup(n15())

def tv1525():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1526:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1526():
  {==}

assert tv1526:
  Tup(n18())

def tv1526():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1527:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1527():
  {==}

assert tv1527:
  Tup(n21())

def tv1527():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1528:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1528():
  {==}

assert tv1528:
  Tup(n24())

def tv1528():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1529:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1529():
  {==}

assert tv1529:
  Tup(n27())

def tv1529():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1530:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1530():
  {==}

assert tv1530:
  Tup(n30())

def tv1530():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1531:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1531():
  {==}

assert tv1531:
  Tup(n5())

def tv1531():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1532:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1532():
  {==}

assert tv1532:
  Tup(n8())

def tv1532():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1533:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1533():
  {==}

assert tv1533:
  Tup(n11())

def tv1533():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1534:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1534():
  {==}

assert tv1534:
  Tup(n14())

def tv1534():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1535:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1535():
  {==}

assert tv1535:
  Tup(n17())

def tv1535():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1536:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1536():
  {==}

assert tv1536:
  Tup(n20())

def tv1536():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1537:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1537():
  {==}

assert tv1537:
  Tup(n23())

def tv1537():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1538:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1538():
  {==}

assert tv1538:
  Tup(n26())

def tv1538():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1539:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1539():
  {==}

assert tv1539:
  Tup(n29())

def tv1539():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1540:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1540():
  {==}

assert tv1540:
  Tup(n4())

def tv1540():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1541:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1541():
  {==}

assert tv1541:
  Tup(n7())

def tv1541():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1542:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1542():
  {==}

assert tv1542:
  Tup(n10())

def tv1542():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1543:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1543():
  {==}

assert tv1543:
  Tup(n13())

def tv1543():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1544:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1544():
  {==}

assert tv1544:
  Tup(n16())

def tv1544():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1545:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1545():
  {==}

assert tv1545:
  Tup(n19())

def tv1545():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1546:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1546():
  {==}

assert tv1546:
  Tup(n22())

def tv1546():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1547:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1547():
  {==}

assert tv1547:
  Tup(n25())

def tv1547():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1548:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1548():
  {==}

assert tv1548:
  Tup(n28())

def tv1548():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1549:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1549():
  {==}

assert tv1549:
  Tup(n31())

def tv1549():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1550:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1550():
  {==}

assert tv1550:
  Tup(n6())

def tv1550():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1551:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1551():
  {==}

assert tv1551:
  Tup(n9())

def tv1551():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1552:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1552():
  {==}

assert tv1552:
  Tup(n12())

def tv1552():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1553:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1553():
  {==}

assert tv1553:
  Tup(n15())

def tv1553():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1554:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1554():
  {==}

assert tv1554:
  Tup(n18())

def tv1554():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1555:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1555():
  {==}

assert tv1555:
  Tup(n21())

def tv1555():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1556:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1556():
  {==}

assert tv1556:
  Tup(n24())

def tv1556():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1557:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1557():
  {==}

assert tv1557:
  Tup(n27())

def tv1557():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1558:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1558():
  {==}

assert tv1558:
  Tup(n30())

def tv1558():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1559:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1559():
  {==}

assert tv1559:
  Tup(n5())

def tv1559():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1560:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1560():
  {==}

assert tv1560:
  Tup(n8())

def tv1560():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1561:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1561():
  {==}

assert tv1561:
  Tup(n11())

def tv1561():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1562:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1562():
  {==}

assert tv1562:
  Tup(n14())

def tv1562():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1563:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1563():
  {==}

assert tv1563:
  Tup(n17())

def tv1563():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1564:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1564():
  {==}

assert tv1564:
  Tup(n20())

def tv1564():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1565:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1565():
  {==}

assert tv1565:
  Tup(n23())

def tv1565():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1566:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1566():
  {==}

assert tv1566:
  Tup(n26())

def tv1566():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1567:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1567():
  {==}

assert tv1567:
  Tup(n29())

def tv1567():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1568:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1568():
  {==}

assert tv1568:
  Tup(n4())

def tv1568():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1569:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1569():
  {==}

assert tv1569:
  Tup(n7())

def tv1569():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1570:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1570():
  {==}

assert tv1570:
  Tup(n10())

def tv1570():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1571:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1571():
  {==}

assert tv1571:
  Tup(n13())

def tv1571():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

assert cm1572:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1572():
  {==}

assert tv1572:
  Tup(n16())

def tv1572():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}

assert cm1573:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1573():
  {==}

assert tv1573:
  Tup(n19())

def tv1573():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}

assert cm1574:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1574():
  {==}

assert tv1574:
  Tup(n22())

def tv1574():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}

assert cm1575:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1575():
  {==}

assert tv1575:
  Tup(n25())

def tv1575():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1576:
  {mul(n16(), n16()) == mul(n16(), n16()) : Nat}

def cm1576():
  {==}

assert tv1576:
  Tup(n28())

def tv1576():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1577:
  {mul(n21(), n27()) == mul(n27(), n21()) : Nat}

def cm1577():
  {==}

assert tv1577:
  Tup(n31())

def tv1577():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1578:
  {mul(n26(), n14()) == mul(n14(), n26()) : Nat}

def cm1578():
  {==}

assert tv1578:
  Tup(n6())

def tv1578():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}

assert cm1579:
  {mul(n31(), n25()) == mul(n25(), n31()) : Nat}

def cm1579():
  {==}

assert tv1579:
  Tup(n9())

def tv1579():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}

assert cm1580:
  {mul(n12(), n12()) == mul(n12(), n12()) : Nat}

def cm1580():
  {==}

assert tv1580:
  Tup(n12())

def tv1580():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}

assert cm1581:
  {mul(n17(), n23()) == mul(n23(), n17()) : Nat}

def cm1581():
  {==}

assert tv1581:
  Tup(n15())

def tv1581():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}

assert cm1582:
  {mul(n22(), n10()) == mul(n10(), n22()) : Nat}

def cm1582():
  {==}

assert tv1582:
  Tup(n18())

def tv1582():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}

assert cm1583:
  {mul(n27(), n21()) == mul(n21(), n27()) : Nat}

def cm1583():
  {==}

assert tv1583:
  Tup(n21())

def tv1583():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}

assert cm1584:
  {mul(n8(), n8()) == mul(n8(), n8()) : Nat}

def cm1584():
  {==}

assert tv1584:
  Tup(n24())

def tv1584():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1585:
  {mul(n13(), n19()) == mul(n19(), n13()) : Nat}

def cm1585():
  {==}

assert tv1585:
  Tup(n27())

def tv1585():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1586:
  {mul(n18(), n30()) == mul(n30(), n18()) : Nat}

def cm1586():
  {==}

assert tv1586:
  Tup(n30())

def tv1586():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1587:
  {mul(n23(), n17()) == mul(n17(), n23()) : Nat}

def cm1587():
  {==}

assert tv1587:
  Tup(n5())

def tv1587():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}

assert cm1588:
  {mul(n28(), n28()) == mul(n28(), n28()) : Nat}

def cm1588():
  {==}

assert tv1588:
  Tup(n8())

def tv1588():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}

assert cm1589:
  {mul(n9(), n15()) == mul(n15(), n9()) : Nat}

def cm1589():
  {==}

assert tv1589:
  Tup(n11())

def tv1589():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}

assert cm1590:
  {mul(n14(), n26()) == mul(n26(), n14()) : Nat}

def cm1590():
  {==}

assert tv1590:
  Tup(n14())

def tv1590():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}

assert cm1591:
  {mul(n19(), n13()) == mul(n13(), n19()) : Nat}

def cm1591():
  {==}

assert tv1591:
  Tup(n17())

def tv1591():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}

assert cm1592:
  {mul(n24(), n24()) == mul(n24(), n24()) : Nat}

def cm1592():
  {==}

assert tv1592:
  Tup(n20())

def tv1592():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}

assert cm1593:
  {mul(n29(), n11()) == mul(n11(), n29()) : Nat}

def cm1593():
  {==}

assert tv1593:
  Tup(n23())

def tv1593():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1594:
  {mul(n10(), n22()) == mul(n22(), n10()) : Nat}

def cm1594():
  {==}

assert tv1594:
  Tup(n26())

def tv1594():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1595:
  {mul(n15(), n9()) == mul(n9(), n15()) : Nat}

def cm1595():
  {==}

assert tv1595:
  Tup(n29())

def tv1595():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

assert cm1596:
  {mul(n20(), n20()) == mul(n20(), n20()) : Nat}

def cm1596():
  {==}

assert tv1596:
  Tup(n4())

def tv1596():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}

assert cm1597:
  {mul(n25(), n31()) == mul(n31(), n25()) : Nat}

def cm1597():
  {==}

assert tv1597:
  Tup(n7())

def tv1597():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}

assert cm1598:
  {mul(n30(), n18()) == mul(n18(), n30()) : Nat}

def cm1598():
  {==}

assert tv1598:
  Tup(n10())

def tv1598():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}

assert cm1599:
  {mul(n11(), n29()) == mul(n29(), n11()) : Nat}

def cm1599():
  {==}

assert tv1599:
  Tup(n13())

def tv1599():
  Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Duo{Z{}, Z{}}}}}}}}}}}}}}

