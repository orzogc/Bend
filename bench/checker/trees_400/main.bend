type Nat:
  Z{}
  S{pred: Nat}

type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

assert Pair:
  forall -A: Type
  forall -B: Type
  Type

def Pair(A, B):
  Sigma<A, _ => B>

assert Copy:
  forall -A: Type
  forall -x: A
  Type

def Copy(A, x):
  &y: A -> {x == y : A}

assert Copiable:
  forall -T: Type
  Type

def Copiable(T):
  @x: T -> Copy(T, x) & Copy(T, x)

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

assert Nat.copy:
  forall n: Nat
  Copy(Nat, n) & Copy(Nat, n)

def Nat.copy(n):
  match n:
    case Z{}:
      ((Z{}, {==}), (Z{}, {==}))
    case S{p}:
      ((a, ea), (b, eb)) = Nat.copy(p)
      ((S{a}, %ea : {S{p} == S{_} : Nat}; {==}), (S{b}, %eb : {S{p} == S{_} : Nat}; {==}))

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

type Bool:
  T{}
  F{}

assert and:
  forall a: Bool
  forall b: Bool
  Bool

def and(a, b):
  match a:
    case T{}:
      b
    case F{}:
      F{}

type Tree:
  L{}
  N{lft: Tree, rgt: Tree}

assert full:
  forall +n: +Nat
  Tree

def full(n):
  match n:
    case Z{}:
      L{}
    case S{p}:
      N{full(p), full(p)}

assert mirror:
  forall t: Tree
  Tree

def mirror(t):
  match t:
    case L{}:
      L{}
    case N{l, r}:
      N{mirror(r), mirror(l)}

assert alltrue:
  forall t: Tree
  Bool

def alltrue(t):
  match t:
    case L{}:
      T{}
    case N{l, r}:
      and(alltrue(l), alltrue(r))

assert ft0:
  {alltrue(full(n7())) == T{} : Bool}

def ft0():
  {==}

assert mt0:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt0():
  {==}

assert ft1:
  {alltrue(full(n12())) == T{} : Bool}

def ft1():
  {==}

assert mt1:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt1():
  {==}

assert ft2:
  {alltrue(full(n11())) == T{} : Bool}

def ft2():
  {==}

assert mt2:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt2():
  {==}

assert ft3:
  {alltrue(full(n10())) == T{} : Bool}

def ft3():
  {==}

assert mt3:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt3():
  {==}

assert ft4:
  {alltrue(full(n9())) == T{} : Bool}

def ft4():
  {==}

assert mt4:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt4():
  {==}

assert ft5:
  {alltrue(full(n8())) == T{} : Bool}

def ft5():
  {==}

assert mt5:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt5():
  {==}

assert ft6:
  {alltrue(full(n7())) == T{} : Bool}

def ft6():
  {==}

assert mt6:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt6():
  {==}

assert ft7:
  {alltrue(full(n12())) == T{} : Bool}

def ft7():
  {==}

assert mt7:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt7():
  {==}

assert ft8:
  {alltrue(full(n11())) == T{} : Bool}

def ft8():
  {==}

assert mt8:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt8():
  {==}

assert ft9:
  {alltrue(full(n10())) == T{} : Bool}

def ft9():
  {==}

assert mt9:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt9():
  {==}

assert ft10:
  {alltrue(full(n9())) == T{} : Bool}

def ft10():
  {==}

assert mt10:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt10():
  {==}

assert ft11:
  {alltrue(full(n8())) == T{} : Bool}

def ft11():
  {==}

assert mt11:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt11():
  {==}

assert ft12:
  {alltrue(full(n7())) == T{} : Bool}

def ft12():
  {==}

assert mt12:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt12():
  {==}

assert ft13:
  {alltrue(full(n12())) == T{} : Bool}

def ft13():
  {==}

assert mt13:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt13():
  {==}

assert ft14:
  {alltrue(full(n11())) == T{} : Bool}

def ft14():
  {==}

assert mt14:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt14():
  {==}

assert ft15:
  {alltrue(full(n10())) == T{} : Bool}

def ft15():
  {==}

assert mt15:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt15():
  {==}

assert ft16:
  {alltrue(full(n9())) == T{} : Bool}

def ft16():
  {==}

assert mt16:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt16():
  {==}

assert ft17:
  {alltrue(full(n8())) == T{} : Bool}

def ft17():
  {==}

assert mt17:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt17():
  {==}

assert ft18:
  {alltrue(full(n7())) == T{} : Bool}

def ft18():
  {==}

assert mt18:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt18():
  {==}

assert ft19:
  {alltrue(full(n12())) == T{} : Bool}

def ft19():
  {==}

assert mt19:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt19():
  {==}

assert ft20:
  {alltrue(full(n11())) == T{} : Bool}

def ft20():
  {==}

assert mt20:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt20():
  {==}

assert ft21:
  {alltrue(full(n10())) == T{} : Bool}

def ft21():
  {==}

assert mt21:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt21():
  {==}

assert ft22:
  {alltrue(full(n9())) == T{} : Bool}

def ft22():
  {==}

assert mt22:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt22():
  {==}

assert ft23:
  {alltrue(full(n8())) == T{} : Bool}

def ft23():
  {==}

assert mt23:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt23():
  {==}

assert ft24:
  {alltrue(full(n7())) == T{} : Bool}

def ft24():
  {==}

assert mt24:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt24():
  {==}

assert ft25:
  {alltrue(full(n12())) == T{} : Bool}

def ft25():
  {==}

assert mt25:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt25():
  {==}

assert ft26:
  {alltrue(full(n11())) == T{} : Bool}

def ft26():
  {==}

assert mt26:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt26():
  {==}

assert ft27:
  {alltrue(full(n10())) == T{} : Bool}

def ft27():
  {==}

assert mt27:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt27():
  {==}

assert ft28:
  {alltrue(full(n9())) == T{} : Bool}

def ft28():
  {==}

assert mt28:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt28():
  {==}

assert ft29:
  {alltrue(full(n8())) == T{} : Bool}

def ft29():
  {==}

assert mt29:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt29():
  {==}

assert ft30:
  {alltrue(full(n7())) == T{} : Bool}

def ft30():
  {==}

assert mt30:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt30():
  {==}

assert ft31:
  {alltrue(full(n12())) == T{} : Bool}

def ft31():
  {==}

assert mt31:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt31():
  {==}

assert ft32:
  {alltrue(full(n11())) == T{} : Bool}

def ft32():
  {==}

assert mt32:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt32():
  {==}

assert ft33:
  {alltrue(full(n10())) == T{} : Bool}

def ft33():
  {==}

assert mt33:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt33():
  {==}

assert ft34:
  {alltrue(full(n9())) == T{} : Bool}

def ft34():
  {==}

assert mt34:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt34():
  {==}

assert ft35:
  {alltrue(full(n8())) == T{} : Bool}

def ft35():
  {==}

assert mt35:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt35():
  {==}

assert ft36:
  {alltrue(full(n7())) == T{} : Bool}

def ft36():
  {==}

assert mt36:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt36():
  {==}

assert ft37:
  {alltrue(full(n12())) == T{} : Bool}

def ft37():
  {==}

assert mt37:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt37():
  {==}

assert ft38:
  {alltrue(full(n11())) == T{} : Bool}

def ft38():
  {==}

assert mt38:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt38():
  {==}

assert ft39:
  {alltrue(full(n10())) == T{} : Bool}

def ft39():
  {==}

assert mt39:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt39():
  {==}

assert ft40:
  {alltrue(full(n9())) == T{} : Bool}

def ft40():
  {==}

assert mt40:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt40():
  {==}

assert ft41:
  {alltrue(full(n8())) == T{} : Bool}

def ft41():
  {==}

assert mt41:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt41():
  {==}

assert ft42:
  {alltrue(full(n7())) == T{} : Bool}

def ft42():
  {==}

assert mt42:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt42():
  {==}

assert ft43:
  {alltrue(full(n12())) == T{} : Bool}

def ft43():
  {==}

assert mt43:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt43():
  {==}

assert ft44:
  {alltrue(full(n11())) == T{} : Bool}

def ft44():
  {==}

assert mt44:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt44():
  {==}

assert ft45:
  {alltrue(full(n10())) == T{} : Bool}

def ft45():
  {==}

assert mt45:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt45():
  {==}

assert ft46:
  {alltrue(full(n9())) == T{} : Bool}

def ft46():
  {==}

assert mt46:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt46():
  {==}

assert ft47:
  {alltrue(full(n8())) == T{} : Bool}

def ft47():
  {==}

assert mt47:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt47():
  {==}

assert ft48:
  {alltrue(full(n7())) == T{} : Bool}

def ft48():
  {==}

assert mt48:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt48():
  {==}

assert ft49:
  {alltrue(full(n12())) == T{} : Bool}

def ft49():
  {==}

assert mt49:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt49():
  {==}

assert ft50:
  {alltrue(full(n11())) == T{} : Bool}

def ft50():
  {==}

assert mt50:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt50():
  {==}

assert ft51:
  {alltrue(full(n10())) == T{} : Bool}

def ft51():
  {==}

assert mt51:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt51():
  {==}

assert ft52:
  {alltrue(full(n9())) == T{} : Bool}

def ft52():
  {==}

assert mt52:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt52():
  {==}

assert ft53:
  {alltrue(full(n8())) == T{} : Bool}

def ft53():
  {==}

assert mt53:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt53():
  {==}

assert ft54:
  {alltrue(full(n7())) == T{} : Bool}

def ft54():
  {==}

assert mt54:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt54():
  {==}

assert ft55:
  {alltrue(full(n12())) == T{} : Bool}

def ft55():
  {==}

assert mt55:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt55():
  {==}

assert ft56:
  {alltrue(full(n11())) == T{} : Bool}

def ft56():
  {==}

assert mt56:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt56():
  {==}

assert ft57:
  {alltrue(full(n10())) == T{} : Bool}

def ft57():
  {==}

assert mt57:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt57():
  {==}

assert ft58:
  {alltrue(full(n9())) == T{} : Bool}

def ft58():
  {==}

assert mt58:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt58():
  {==}

assert ft59:
  {alltrue(full(n8())) == T{} : Bool}

def ft59():
  {==}

assert mt59:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt59():
  {==}

assert ft60:
  {alltrue(full(n7())) == T{} : Bool}

def ft60():
  {==}

assert mt60:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt60():
  {==}

assert ft61:
  {alltrue(full(n12())) == T{} : Bool}

def ft61():
  {==}

assert mt61:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt61():
  {==}

assert ft62:
  {alltrue(full(n11())) == T{} : Bool}

def ft62():
  {==}

assert mt62:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt62():
  {==}

assert ft63:
  {alltrue(full(n10())) == T{} : Bool}

def ft63():
  {==}

assert mt63:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt63():
  {==}

assert ft64:
  {alltrue(full(n9())) == T{} : Bool}

def ft64():
  {==}

assert mt64:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt64():
  {==}

assert ft65:
  {alltrue(full(n8())) == T{} : Bool}

def ft65():
  {==}

assert mt65:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt65():
  {==}

assert ft66:
  {alltrue(full(n7())) == T{} : Bool}

def ft66():
  {==}

assert mt66:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt66():
  {==}

assert ft67:
  {alltrue(full(n12())) == T{} : Bool}

def ft67():
  {==}

assert mt67:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt67():
  {==}

assert ft68:
  {alltrue(full(n11())) == T{} : Bool}

def ft68():
  {==}

assert mt68:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt68():
  {==}

assert ft69:
  {alltrue(full(n10())) == T{} : Bool}

def ft69():
  {==}

assert mt69:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt69():
  {==}

assert ft70:
  {alltrue(full(n9())) == T{} : Bool}

def ft70():
  {==}

assert mt70:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt70():
  {==}

assert ft71:
  {alltrue(full(n8())) == T{} : Bool}

def ft71():
  {==}

assert mt71:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt71():
  {==}

assert ft72:
  {alltrue(full(n7())) == T{} : Bool}

def ft72():
  {==}

assert mt72:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt72():
  {==}

assert ft73:
  {alltrue(full(n12())) == T{} : Bool}

def ft73():
  {==}

assert mt73:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt73():
  {==}

assert ft74:
  {alltrue(full(n11())) == T{} : Bool}

def ft74():
  {==}

assert mt74:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt74():
  {==}

assert ft75:
  {alltrue(full(n10())) == T{} : Bool}

def ft75():
  {==}

assert mt75:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt75():
  {==}

assert ft76:
  {alltrue(full(n9())) == T{} : Bool}

def ft76():
  {==}

assert mt76:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt76():
  {==}

assert ft77:
  {alltrue(full(n8())) == T{} : Bool}

def ft77():
  {==}

assert mt77:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt77():
  {==}

assert ft78:
  {alltrue(full(n7())) == T{} : Bool}

def ft78():
  {==}

assert mt78:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt78():
  {==}

assert ft79:
  {alltrue(full(n12())) == T{} : Bool}

def ft79():
  {==}

assert mt79:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt79():
  {==}

assert ft80:
  {alltrue(full(n11())) == T{} : Bool}

def ft80():
  {==}

assert mt80:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt80():
  {==}

assert ft81:
  {alltrue(full(n10())) == T{} : Bool}

def ft81():
  {==}

assert mt81:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt81():
  {==}

assert ft82:
  {alltrue(full(n9())) == T{} : Bool}

def ft82():
  {==}

assert mt82:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt82():
  {==}

assert ft83:
  {alltrue(full(n8())) == T{} : Bool}

def ft83():
  {==}

assert mt83:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt83():
  {==}

assert ft84:
  {alltrue(full(n7())) == T{} : Bool}

def ft84():
  {==}

assert mt84:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt84():
  {==}

assert ft85:
  {alltrue(full(n12())) == T{} : Bool}

def ft85():
  {==}

assert mt85:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt85():
  {==}

assert ft86:
  {alltrue(full(n11())) == T{} : Bool}

def ft86():
  {==}

assert mt86:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt86():
  {==}

assert ft87:
  {alltrue(full(n10())) == T{} : Bool}

def ft87():
  {==}

assert mt87:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt87():
  {==}

assert ft88:
  {alltrue(full(n9())) == T{} : Bool}

def ft88():
  {==}

assert mt88:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt88():
  {==}

assert ft89:
  {alltrue(full(n8())) == T{} : Bool}

def ft89():
  {==}

assert mt89:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt89():
  {==}

assert ft90:
  {alltrue(full(n7())) == T{} : Bool}

def ft90():
  {==}

assert mt90:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt90():
  {==}

assert ft91:
  {alltrue(full(n12())) == T{} : Bool}

def ft91():
  {==}

assert mt91:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt91():
  {==}

assert ft92:
  {alltrue(full(n11())) == T{} : Bool}

def ft92():
  {==}

assert mt92:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt92():
  {==}

assert ft93:
  {alltrue(full(n10())) == T{} : Bool}

def ft93():
  {==}

assert mt93:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt93():
  {==}

assert ft94:
  {alltrue(full(n9())) == T{} : Bool}

def ft94():
  {==}

assert mt94:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt94():
  {==}

assert ft95:
  {alltrue(full(n8())) == T{} : Bool}

def ft95():
  {==}

assert mt95:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt95():
  {==}

assert ft96:
  {alltrue(full(n7())) == T{} : Bool}

def ft96():
  {==}

assert mt96:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt96():
  {==}

assert ft97:
  {alltrue(full(n12())) == T{} : Bool}

def ft97():
  {==}

assert mt97:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt97():
  {==}

assert ft98:
  {alltrue(full(n11())) == T{} : Bool}

def ft98():
  {==}

assert mt98:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt98():
  {==}

assert ft99:
  {alltrue(full(n10())) == T{} : Bool}

def ft99():
  {==}

assert mt99:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt99():
  {==}

assert ft100:
  {alltrue(full(n9())) == T{} : Bool}

def ft100():
  {==}

assert mt100:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt100():
  {==}

assert ft101:
  {alltrue(full(n8())) == T{} : Bool}

def ft101():
  {==}

assert mt101:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt101():
  {==}

assert ft102:
  {alltrue(full(n7())) == T{} : Bool}

def ft102():
  {==}

assert mt102:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt102():
  {==}

assert ft103:
  {alltrue(full(n12())) == T{} : Bool}

def ft103():
  {==}

assert mt103:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt103():
  {==}

assert ft104:
  {alltrue(full(n11())) == T{} : Bool}

def ft104():
  {==}

assert mt104:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt104():
  {==}

assert ft105:
  {alltrue(full(n10())) == T{} : Bool}

def ft105():
  {==}

assert mt105:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt105():
  {==}

assert ft106:
  {alltrue(full(n9())) == T{} : Bool}

def ft106():
  {==}

assert mt106:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt106():
  {==}

assert ft107:
  {alltrue(full(n8())) == T{} : Bool}

def ft107():
  {==}

assert mt107:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt107():
  {==}

assert ft108:
  {alltrue(full(n7())) == T{} : Bool}

def ft108():
  {==}

assert mt108:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt108():
  {==}

assert ft109:
  {alltrue(full(n12())) == T{} : Bool}

def ft109():
  {==}

assert mt109:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt109():
  {==}

assert ft110:
  {alltrue(full(n11())) == T{} : Bool}

def ft110():
  {==}

assert mt110:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt110():
  {==}

assert ft111:
  {alltrue(full(n10())) == T{} : Bool}

def ft111():
  {==}

assert mt111:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt111():
  {==}

assert ft112:
  {alltrue(full(n9())) == T{} : Bool}

def ft112():
  {==}

assert mt112:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt112():
  {==}

assert ft113:
  {alltrue(full(n8())) == T{} : Bool}

def ft113():
  {==}

assert mt113:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt113():
  {==}

assert ft114:
  {alltrue(full(n7())) == T{} : Bool}

def ft114():
  {==}

assert mt114:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt114():
  {==}

assert ft115:
  {alltrue(full(n12())) == T{} : Bool}

def ft115():
  {==}

assert mt115:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt115():
  {==}

assert ft116:
  {alltrue(full(n11())) == T{} : Bool}

def ft116():
  {==}

assert mt116:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt116():
  {==}

assert ft117:
  {alltrue(full(n10())) == T{} : Bool}

def ft117():
  {==}

assert mt117:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt117():
  {==}

assert ft118:
  {alltrue(full(n9())) == T{} : Bool}

def ft118():
  {==}

assert mt118:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt118():
  {==}

assert ft119:
  {alltrue(full(n8())) == T{} : Bool}

def ft119():
  {==}

assert mt119:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt119():
  {==}

assert ft120:
  {alltrue(full(n7())) == T{} : Bool}

def ft120():
  {==}

assert mt120:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt120():
  {==}

assert ft121:
  {alltrue(full(n12())) == T{} : Bool}

def ft121():
  {==}

assert mt121:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt121():
  {==}

assert ft122:
  {alltrue(full(n11())) == T{} : Bool}

def ft122():
  {==}

assert mt122:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt122():
  {==}

assert ft123:
  {alltrue(full(n10())) == T{} : Bool}

def ft123():
  {==}

assert mt123:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt123():
  {==}

assert ft124:
  {alltrue(full(n9())) == T{} : Bool}

def ft124():
  {==}

assert mt124:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt124():
  {==}

assert ft125:
  {alltrue(full(n8())) == T{} : Bool}

def ft125():
  {==}

assert mt125:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt125():
  {==}

assert ft126:
  {alltrue(full(n7())) == T{} : Bool}

def ft126():
  {==}

assert mt126:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt126():
  {==}

assert ft127:
  {alltrue(full(n12())) == T{} : Bool}

def ft127():
  {==}

assert mt127:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt127():
  {==}

assert ft128:
  {alltrue(full(n11())) == T{} : Bool}

def ft128():
  {==}

assert mt128:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt128():
  {==}

assert ft129:
  {alltrue(full(n10())) == T{} : Bool}

def ft129():
  {==}

assert mt129:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt129():
  {==}

assert ft130:
  {alltrue(full(n9())) == T{} : Bool}

def ft130():
  {==}

assert mt130:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt130():
  {==}

assert ft131:
  {alltrue(full(n8())) == T{} : Bool}

def ft131():
  {==}

assert mt131:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt131():
  {==}

assert ft132:
  {alltrue(full(n7())) == T{} : Bool}

def ft132():
  {==}

assert mt132:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt132():
  {==}

assert ft133:
  {alltrue(full(n12())) == T{} : Bool}

def ft133():
  {==}

assert mt133:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt133():
  {==}

assert ft134:
  {alltrue(full(n11())) == T{} : Bool}

def ft134():
  {==}

assert mt134:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt134():
  {==}

assert ft135:
  {alltrue(full(n10())) == T{} : Bool}

def ft135():
  {==}

assert mt135:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt135():
  {==}

assert ft136:
  {alltrue(full(n9())) == T{} : Bool}

def ft136():
  {==}

assert mt136:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt136():
  {==}

assert ft137:
  {alltrue(full(n8())) == T{} : Bool}

def ft137():
  {==}

assert mt137:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt137():
  {==}

assert ft138:
  {alltrue(full(n7())) == T{} : Bool}

def ft138():
  {==}

assert mt138:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt138():
  {==}

assert ft139:
  {alltrue(full(n12())) == T{} : Bool}

def ft139():
  {==}

assert mt139:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt139():
  {==}

assert ft140:
  {alltrue(full(n11())) == T{} : Bool}

def ft140():
  {==}

assert mt140:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt140():
  {==}

assert ft141:
  {alltrue(full(n10())) == T{} : Bool}

def ft141():
  {==}

assert mt141:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt141():
  {==}

assert ft142:
  {alltrue(full(n9())) == T{} : Bool}

def ft142():
  {==}

assert mt142:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt142():
  {==}

assert ft143:
  {alltrue(full(n8())) == T{} : Bool}

def ft143():
  {==}

assert mt143:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt143():
  {==}

assert ft144:
  {alltrue(full(n7())) == T{} : Bool}

def ft144():
  {==}

assert mt144:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt144():
  {==}

assert ft145:
  {alltrue(full(n12())) == T{} : Bool}

def ft145():
  {==}

assert mt145:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt145():
  {==}

assert ft146:
  {alltrue(full(n11())) == T{} : Bool}

def ft146():
  {==}

assert mt146:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt146():
  {==}

assert ft147:
  {alltrue(full(n10())) == T{} : Bool}

def ft147():
  {==}

assert mt147:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt147():
  {==}

assert ft148:
  {alltrue(full(n9())) == T{} : Bool}

def ft148():
  {==}

assert mt148:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt148():
  {==}

assert ft149:
  {alltrue(full(n8())) == T{} : Bool}

def ft149():
  {==}

assert mt149:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt149():
  {==}

assert ft150:
  {alltrue(full(n7())) == T{} : Bool}

def ft150():
  {==}

assert mt150:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt150():
  {==}

assert ft151:
  {alltrue(full(n12())) == T{} : Bool}

def ft151():
  {==}

assert mt151:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt151():
  {==}

assert ft152:
  {alltrue(full(n11())) == T{} : Bool}

def ft152():
  {==}

assert mt152:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt152():
  {==}

assert ft153:
  {alltrue(full(n10())) == T{} : Bool}

def ft153():
  {==}

assert mt153:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt153():
  {==}

assert ft154:
  {alltrue(full(n9())) == T{} : Bool}

def ft154():
  {==}

assert mt154:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt154():
  {==}

assert ft155:
  {alltrue(full(n8())) == T{} : Bool}

def ft155():
  {==}

assert mt155:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt155():
  {==}

assert ft156:
  {alltrue(full(n7())) == T{} : Bool}

def ft156():
  {==}

assert mt156:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt156():
  {==}

assert ft157:
  {alltrue(full(n12())) == T{} : Bool}

def ft157():
  {==}

assert mt157:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt157():
  {==}

assert ft158:
  {alltrue(full(n11())) == T{} : Bool}

def ft158():
  {==}

assert mt158:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt158():
  {==}

assert ft159:
  {alltrue(full(n10())) == T{} : Bool}

def ft159():
  {==}

assert mt159:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt159():
  {==}

assert ft160:
  {alltrue(full(n9())) == T{} : Bool}

def ft160():
  {==}

assert mt160:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt160():
  {==}

assert ft161:
  {alltrue(full(n8())) == T{} : Bool}

def ft161():
  {==}

assert mt161:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt161():
  {==}

assert ft162:
  {alltrue(full(n7())) == T{} : Bool}

def ft162():
  {==}

assert mt162:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt162():
  {==}

assert ft163:
  {alltrue(full(n12())) == T{} : Bool}

def ft163():
  {==}

assert mt163:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt163():
  {==}

assert ft164:
  {alltrue(full(n11())) == T{} : Bool}

def ft164():
  {==}

assert mt164:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt164():
  {==}

assert ft165:
  {alltrue(full(n10())) == T{} : Bool}

def ft165():
  {==}

assert mt165:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt165():
  {==}

assert ft166:
  {alltrue(full(n9())) == T{} : Bool}

def ft166():
  {==}

assert mt166:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt166():
  {==}

assert ft167:
  {alltrue(full(n8())) == T{} : Bool}

def ft167():
  {==}

assert mt167:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt167():
  {==}

assert ft168:
  {alltrue(full(n7())) == T{} : Bool}

def ft168():
  {==}

assert mt168:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt168():
  {==}

assert ft169:
  {alltrue(full(n12())) == T{} : Bool}

def ft169():
  {==}

assert mt169:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt169():
  {==}

assert ft170:
  {alltrue(full(n11())) == T{} : Bool}

def ft170():
  {==}

assert mt170:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt170():
  {==}

assert ft171:
  {alltrue(full(n10())) == T{} : Bool}

def ft171():
  {==}

assert mt171:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt171():
  {==}

assert ft172:
  {alltrue(full(n9())) == T{} : Bool}

def ft172():
  {==}

assert mt172:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt172():
  {==}

assert ft173:
  {alltrue(full(n8())) == T{} : Bool}

def ft173():
  {==}

assert mt173:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt173():
  {==}

assert ft174:
  {alltrue(full(n7())) == T{} : Bool}

def ft174():
  {==}

assert mt174:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt174():
  {==}

assert ft175:
  {alltrue(full(n12())) == T{} : Bool}

def ft175():
  {==}

assert mt175:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt175():
  {==}

assert ft176:
  {alltrue(full(n11())) == T{} : Bool}

def ft176():
  {==}

assert mt176:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt176():
  {==}

assert ft177:
  {alltrue(full(n10())) == T{} : Bool}

def ft177():
  {==}

assert mt177:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt177():
  {==}

assert ft178:
  {alltrue(full(n9())) == T{} : Bool}

def ft178():
  {==}

assert mt178:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt178():
  {==}

assert ft179:
  {alltrue(full(n8())) == T{} : Bool}

def ft179():
  {==}

assert mt179:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt179():
  {==}

assert ft180:
  {alltrue(full(n7())) == T{} : Bool}

def ft180():
  {==}

assert mt180:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt180():
  {==}

assert ft181:
  {alltrue(full(n12())) == T{} : Bool}

def ft181():
  {==}

assert mt181:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt181():
  {==}

assert ft182:
  {alltrue(full(n11())) == T{} : Bool}

def ft182():
  {==}

assert mt182:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt182():
  {==}

assert ft183:
  {alltrue(full(n10())) == T{} : Bool}

def ft183():
  {==}

assert mt183:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt183():
  {==}

assert ft184:
  {alltrue(full(n9())) == T{} : Bool}

def ft184():
  {==}

assert mt184:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt184():
  {==}

assert ft185:
  {alltrue(full(n8())) == T{} : Bool}

def ft185():
  {==}

assert mt185:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt185():
  {==}

assert ft186:
  {alltrue(full(n7())) == T{} : Bool}

def ft186():
  {==}

assert mt186:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt186():
  {==}

assert ft187:
  {alltrue(full(n12())) == T{} : Bool}

def ft187():
  {==}

assert mt187:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt187():
  {==}

assert ft188:
  {alltrue(full(n11())) == T{} : Bool}

def ft188():
  {==}

assert mt188:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt188():
  {==}

assert ft189:
  {alltrue(full(n10())) == T{} : Bool}

def ft189():
  {==}

assert mt189:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt189():
  {==}

assert ft190:
  {alltrue(full(n9())) == T{} : Bool}

def ft190():
  {==}

assert mt190:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt190():
  {==}

assert ft191:
  {alltrue(full(n8())) == T{} : Bool}

def ft191():
  {==}

assert mt191:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt191():
  {==}

assert ft192:
  {alltrue(full(n7())) == T{} : Bool}

def ft192():
  {==}

assert mt192:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt192():
  {==}

assert ft193:
  {alltrue(full(n12())) == T{} : Bool}

def ft193():
  {==}

assert mt193:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt193():
  {==}

assert ft194:
  {alltrue(full(n11())) == T{} : Bool}

def ft194():
  {==}

assert mt194:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt194():
  {==}

assert ft195:
  {alltrue(full(n10())) == T{} : Bool}

def ft195():
  {==}

assert mt195:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt195():
  {==}

assert ft196:
  {alltrue(full(n9())) == T{} : Bool}

def ft196():
  {==}

assert mt196:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt196():
  {==}

assert ft197:
  {alltrue(full(n8())) == T{} : Bool}

def ft197():
  {==}

assert mt197:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt197():
  {==}

assert ft198:
  {alltrue(full(n7())) == T{} : Bool}

def ft198():
  {==}

assert mt198:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt198():
  {==}

assert ft199:
  {alltrue(full(n12())) == T{} : Bool}

def ft199():
  {==}

assert mt199:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt199():
  {==}

assert ft200:
  {alltrue(full(n11())) == T{} : Bool}

def ft200():
  {==}

assert mt200:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt200():
  {==}

assert ft201:
  {alltrue(full(n10())) == T{} : Bool}

def ft201():
  {==}

assert mt201:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt201():
  {==}

assert ft202:
  {alltrue(full(n9())) == T{} : Bool}

def ft202():
  {==}

assert mt202:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt202():
  {==}

assert ft203:
  {alltrue(full(n8())) == T{} : Bool}

def ft203():
  {==}

assert mt203:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt203():
  {==}

assert ft204:
  {alltrue(full(n7())) == T{} : Bool}

def ft204():
  {==}

assert mt204:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt204():
  {==}

assert ft205:
  {alltrue(full(n12())) == T{} : Bool}

def ft205():
  {==}

assert mt205:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt205():
  {==}

assert ft206:
  {alltrue(full(n11())) == T{} : Bool}

def ft206():
  {==}

assert mt206:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt206():
  {==}

assert ft207:
  {alltrue(full(n10())) == T{} : Bool}

def ft207():
  {==}

assert mt207:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt207():
  {==}

assert ft208:
  {alltrue(full(n9())) == T{} : Bool}

def ft208():
  {==}

assert mt208:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt208():
  {==}

assert ft209:
  {alltrue(full(n8())) == T{} : Bool}

def ft209():
  {==}

assert mt209:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt209():
  {==}

assert ft210:
  {alltrue(full(n7())) == T{} : Bool}

def ft210():
  {==}

assert mt210:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt210():
  {==}

assert ft211:
  {alltrue(full(n12())) == T{} : Bool}

def ft211():
  {==}

assert mt211:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt211():
  {==}

assert ft212:
  {alltrue(full(n11())) == T{} : Bool}

def ft212():
  {==}

assert mt212:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt212():
  {==}

assert ft213:
  {alltrue(full(n10())) == T{} : Bool}

def ft213():
  {==}

assert mt213:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt213():
  {==}

assert ft214:
  {alltrue(full(n9())) == T{} : Bool}

def ft214():
  {==}

assert mt214:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt214():
  {==}

assert ft215:
  {alltrue(full(n8())) == T{} : Bool}

def ft215():
  {==}

assert mt215:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt215():
  {==}

assert ft216:
  {alltrue(full(n7())) == T{} : Bool}

def ft216():
  {==}

assert mt216:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt216():
  {==}

assert ft217:
  {alltrue(full(n12())) == T{} : Bool}

def ft217():
  {==}

assert mt217:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt217():
  {==}

assert ft218:
  {alltrue(full(n11())) == T{} : Bool}

def ft218():
  {==}

assert mt218:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt218():
  {==}

assert ft219:
  {alltrue(full(n10())) == T{} : Bool}

def ft219():
  {==}

assert mt219:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt219():
  {==}

assert ft220:
  {alltrue(full(n9())) == T{} : Bool}

def ft220():
  {==}

assert mt220:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt220():
  {==}

assert ft221:
  {alltrue(full(n8())) == T{} : Bool}

def ft221():
  {==}

assert mt221:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt221():
  {==}

assert ft222:
  {alltrue(full(n7())) == T{} : Bool}

def ft222():
  {==}

assert mt222:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt222():
  {==}

assert ft223:
  {alltrue(full(n12())) == T{} : Bool}

def ft223():
  {==}

assert mt223:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt223():
  {==}

assert ft224:
  {alltrue(full(n11())) == T{} : Bool}

def ft224():
  {==}

assert mt224:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt224():
  {==}

assert ft225:
  {alltrue(full(n10())) == T{} : Bool}

def ft225():
  {==}

assert mt225:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt225():
  {==}

assert ft226:
  {alltrue(full(n9())) == T{} : Bool}

def ft226():
  {==}

assert mt226:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt226():
  {==}

assert ft227:
  {alltrue(full(n8())) == T{} : Bool}

def ft227():
  {==}

assert mt227:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt227():
  {==}

assert ft228:
  {alltrue(full(n7())) == T{} : Bool}

def ft228():
  {==}

assert mt228:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt228():
  {==}

assert ft229:
  {alltrue(full(n12())) == T{} : Bool}

def ft229():
  {==}

assert mt229:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt229():
  {==}

assert ft230:
  {alltrue(full(n11())) == T{} : Bool}

def ft230():
  {==}

assert mt230:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt230():
  {==}

assert ft231:
  {alltrue(full(n10())) == T{} : Bool}

def ft231():
  {==}

assert mt231:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt231():
  {==}

assert ft232:
  {alltrue(full(n9())) == T{} : Bool}

def ft232():
  {==}

assert mt232:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt232():
  {==}

assert ft233:
  {alltrue(full(n8())) == T{} : Bool}

def ft233():
  {==}

assert mt233:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt233():
  {==}

assert ft234:
  {alltrue(full(n7())) == T{} : Bool}

def ft234():
  {==}

assert mt234:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt234():
  {==}

assert ft235:
  {alltrue(full(n12())) == T{} : Bool}

def ft235():
  {==}

assert mt235:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt235():
  {==}

assert ft236:
  {alltrue(full(n11())) == T{} : Bool}

def ft236():
  {==}

assert mt236:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt236():
  {==}

assert ft237:
  {alltrue(full(n10())) == T{} : Bool}

def ft237():
  {==}

assert mt237:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt237():
  {==}

assert ft238:
  {alltrue(full(n9())) == T{} : Bool}

def ft238():
  {==}

assert mt238:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt238():
  {==}

assert ft239:
  {alltrue(full(n8())) == T{} : Bool}

def ft239():
  {==}

assert mt239:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt239():
  {==}

assert ft240:
  {alltrue(full(n7())) == T{} : Bool}

def ft240():
  {==}

assert mt240:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt240():
  {==}

assert ft241:
  {alltrue(full(n12())) == T{} : Bool}

def ft241():
  {==}

assert mt241:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt241():
  {==}

assert ft242:
  {alltrue(full(n11())) == T{} : Bool}

def ft242():
  {==}

assert mt242:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt242():
  {==}

assert ft243:
  {alltrue(full(n10())) == T{} : Bool}

def ft243():
  {==}

assert mt243:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt243():
  {==}

assert ft244:
  {alltrue(full(n9())) == T{} : Bool}

def ft244():
  {==}

assert mt244:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt244():
  {==}

assert ft245:
  {alltrue(full(n8())) == T{} : Bool}

def ft245():
  {==}

assert mt245:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt245():
  {==}

assert ft246:
  {alltrue(full(n7())) == T{} : Bool}

def ft246():
  {==}

assert mt246:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt246():
  {==}

assert ft247:
  {alltrue(full(n12())) == T{} : Bool}

def ft247():
  {==}

assert mt247:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt247():
  {==}

assert ft248:
  {alltrue(full(n11())) == T{} : Bool}

def ft248():
  {==}

assert mt248:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt248():
  {==}

assert ft249:
  {alltrue(full(n10())) == T{} : Bool}

def ft249():
  {==}

assert mt249:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt249():
  {==}

assert ft250:
  {alltrue(full(n9())) == T{} : Bool}

def ft250():
  {==}

assert mt250:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt250():
  {==}

assert ft251:
  {alltrue(full(n8())) == T{} : Bool}

def ft251():
  {==}

assert mt251:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt251():
  {==}

assert ft252:
  {alltrue(full(n7())) == T{} : Bool}

def ft252():
  {==}

assert mt252:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt252():
  {==}

assert ft253:
  {alltrue(full(n12())) == T{} : Bool}

def ft253():
  {==}

assert mt253:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt253():
  {==}

assert ft254:
  {alltrue(full(n11())) == T{} : Bool}

def ft254():
  {==}

assert mt254:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt254():
  {==}

assert ft255:
  {alltrue(full(n10())) == T{} : Bool}

def ft255():
  {==}

assert mt255:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt255():
  {==}

assert ft256:
  {alltrue(full(n9())) == T{} : Bool}

def ft256():
  {==}

assert mt256:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt256():
  {==}

assert ft257:
  {alltrue(full(n8())) == T{} : Bool}

def ft257():
  {==}

assert mt257:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt257():
  {==}

assert ft258:
  {alltrue(full(n7())) == T{} : Bool}

def ft258():
  {==}

assert mt258:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt258():
  {==}

assert ft259:
  {alltrue(full(n12())) == T{} : Bool}

def ft259():
  {==}

assert mt259:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt259():
  {==}

assert ft260:
  {alltrue(full(n11())) == T{} : Bool}

def ft260():
  {==}

assert mt260:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt260():
  {==}

assert ft261:
  {alltrue(full(n10())) == T{} : Bool}

def ft261():
  {==}

assert mt261:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt261():
  {==}

assert ft262:
  {alltrue(full(n9())) == T{} : Bool}

def ft262():
  {==}

assert mt262:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt262():
  {==}

assert ft263:
  {alltrue(full(n8())) == T{} : Bool}

def ft263():
  {==}

assert mt263:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt263():
  {==}

assert ft264:
  {alltrue(full(n7())) == T{} : Bool}

def ft264():
  {==}

assert mt264:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt264():
  {==}

assert ft265:
  {alltrue(full(n12())) == T{} : Bool}

def ft265():
  {==}

assert mt265:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt265():
  {==}

assert ft266:
  {alltrue(full(n11())) == T{} : Bool}

def ft266():
  {==}

assert mt266:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt266():
  {==}

assert ft267:
  {alltrue(full(n10())) == T{} : Bool}

def ft267():
  {==}

assert mt267:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt267():
  {==}

assert ft268:
  {alltrue(full(n9())) == T{} : Bool}

def ft268():
  {==}

assert mt268:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt268():
  {==}

assert ft269:
  {alltrue(full(n8())) == T{} : Bool}

def ft269():
  {==}

assert mt269:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt269():
  {==}

assert ft270:
  {alltrue(full(n7())) == T{} : Bool}

def ft270():
  {==}

assert mt270:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt270():
  {==}

assert ft271:
  {alltrue(full(n12())) == T{} : Bool}

def ft271():
  {==}

assert mt271:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt271():
  {==}

assert ft272:
  {alltrue(full(n11())) == T{} : Bool}

def ft272():
  {==}

assert mt272:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt272():
  {==}

assert ft273:
  {alltrue(full(n10())) == T{} : Bool}

def ft273():
  {==}

assert mt273:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt273():
  {==}

assert ft274:
  {alltrue(full(n9())) == T{} : Bool}

def ft274():
  {==}

assert mt274:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt274():
  {==}

assert ft275:
  {alltrue(full(n8())) == T{} : Bool}

def ft275():
  {==}

assert mt275:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt275():
  {==}

assert ft276:
  {alltrue(full(n7())) == T{} : Bool}

def ft276():
  {==}

assert mt276:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt276():
  {==}

assert ft277:
  {alltrue(full(n12())) == T{} : Bool}

def ft277():
  {==}

assert mt277:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt277():
  {==}

assert ft278:
  {alltrue(full(n11())) == T{} : Bool}

def ft278():
  {==}

assert mt278:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt278():
  {==}

assert ft279:
  {alltrue(full(n10())) == T{} : Bool}

def ft279():
  {==}

assert mt279:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt279():
  {==}

assert ft280:
  {alltrue(full(n9())) == T{} : Bool}

def ft280():
  {==}

assert mt280:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt280():
  {==}

assert ft281:
  {alltrue(full(n8())) == T{} : Bool}

def ft281():
  {==}

assert mt281:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt281():
  {==}

assert ft282:
  {alltrue(full(n7())) == T{} : Bool}

def ft282():
  {==}

assert mt282:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt282():
  {==}

assert ft283:
  {alltrue(full(n12())) == T{} : Bool}

def ft283():
  {==}

assert mt283:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt283():
  {==}

assert ft284:
  {alltrue(full(n11())) == T{} : Bool}

def ft284():
  {==}

assert mt284:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt284():
  {==}

assert ft285:
  {alltrue(full(n10())) == T{} : Bool}

def ft285():
  {==}

assert mt285:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt285():
  {==}

assert ft286:
  {alltrue(full(n9())) == T{} : Bool}

def ft286():
  {==}

assert mt286:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt286():
  {==}

assert ft287:
  {alltrue(full(n8())) == T{} : Bool}

def ft287():
  {==}

assert mt287:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt287():
  {==}

assert ft288:
  {alltrue(full(n7())) == T{} : Bool}

def ft288():
  {==}

assert mt288:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt288():
  {==}

assert ft289:
  {alltrue(full(n12())) == T{} : Bool}

def ft289():
  {==}

assert mt289:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt289():
  {==}

assert ft290:
  {alltrue(full(n11())) == T{} : Bool}

def ft290():
  {==}

assert mt290:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt290():
  {==}

assert ft291:
  {alltrue(full(n10())) == T{} : Bool}

def ft291():
  {==}

assert mt291:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt291():
  {==}

assert ft292:
  {alltrue(full(n9())) == T{} : Bool}

def ft292():
  {==}

assert mt292:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt292():
  {==}

assert ft293:
  {alltrue(full(n8())) == T{} : Bool}

def ft293():
  {==}

assert mt293:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt293():
  {==}

assert ft294:
  {alltrue(full(n7())) == T{} : Bool}

def ft294():
  {==}

assert mt294:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt294():
  {==}

assert ft295:
  {alltrue(full(n12())) == T{} : Bool}

def ft295():
  {==}

assert mt295:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt295():
  {==}

assert ft296:
  {alltrue(full(n11())) == T{} : Bool}

def ft296():
  {==}

assert mt296:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt296():
  {==}

assert ft297:
  {alltrue(full(n10())) == T{} : Bool}

def ft297():
  {==}

assert mt297:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt297():
  {==}

assert ft298:
  {alltrue(full(n9())) == T{} : Bool}

def ft298():
  {==}

assert mt298:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt298():
  {==}

assert ft299:
  {alltrue(full(n8())) == T{} : Bool}

def ft299():
  {==}

assert mt299:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt299():
  {==}

assert ft300:
  {alltrue(full(n7())) == T{} : Bool}

def ft300():
  {==}

assert mt300:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt300():
  {==}

assert ft301:
  {alltrue(full(n12())) == T{} : Bool}

def ft301():
  {==}

assert mt301:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt301():
  {==}

assert ft302:
  {alltrue(full(n11())) == T{} : Bool}

def ft302():
  {==}

assert mt302:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt302():
  {==}

assert ft303:
  {alltrue(full(n10())) == T{} : Bool}

def ft303():
  {==}

assert mt303:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt303():
  {==}

assert ft304:
  {alltrue(full(n9())) == T{} : Bool}

def ft304():
  {==}

assert mt304:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt304():
  {==}

assert ft305:
  {alltrue(full(n8())) == T{} : Bool}

def ft305():
  {==}

assert mt305:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt305():
  {==}

assert ft306:
  {alltrue(full(n7())) == T{} : Bool}

def ft306():
  {==}

assert mt306:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt306():
  {==}

assert ft307:
  {alltrue(full(n12())) == T{} : Bool}

def ft307():
  {==}

assert mt307:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt307():
  {==}

assert ft308:
  {alltrue(full(n11())) == T{} : Bool}

def ft308():
  {==}

assert mt308:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt308():
  {==}

assert ft309:
  {alltrue(full(n10())) == T{} : Bool}

def ft309():
  {==}

assert mt309:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt309():
  {==}

assert ft310:
  {alltrue(full(n9())) == T{} : Bool}

def ft310():
  {==}

assert mt310:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt310():
  {==}

assert ft311:
  {alltrue(full(n8())) == T{} : Bool}

def ft311():
  {==}

assert mt311:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt311():
  {==}

assert ft312:
  {alltrue(full(n7())) == T{} : Bool}

def ft312():
  {==}

assert mt312:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt312():
  {==}

assert ft313:
  {alltrue(full(n12())) == T{} : Bool}

def ft313():
  {==}

assert mt313:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt313():
  {==}

assert ft314:
  {alltrue(full(n11())) == T{} : Bool}

def ft314():
  {==}

assert mt314:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt314():
  {==}

assert ft315:
  {alltrue(full(n10())) == T{} : Bool}

def ft315():
  {==}

assert mt315:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt315():
  {==}

assert ft316:
  {alltrue(full(n9())) == T{} : Bool}

def ft316():
  {==}

assert mt316:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt316():
  {==}

assert ft317:
  {alltrue(full(n8())) == T{} : Bool}

def ft317():
  {==}

assert mt317:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt317():
  {==}

assert ft318:
  {alltrue(full(n7())) == T{} : Bool}

def ft318():
  {==}

assert mt318:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt318():
  {==}

assert ft319:
  {alltrue(full(n12())) == T{} : Bool}

def ft319():
  {==}

assert mt319:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt319():
  {==}

assert ft320:
  {alltrue(full(n11())) == T{} : Bool}

def ft320():
  {==}

assert mt320:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt320():
  {==}

assert ft321:
  {alltrue(full(n10())) == T{} : Bool}

def ft321():
  {==}

assert mt321:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt321():
  {==}

assert ft322:
  {alltrue(full(n9())) == T{} : Bool}

def ft322():
  {==}

assert mt322:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt322():
  {==}

assert ft323:
  {alltrue(full(n8())) == T{} : Bool}

def ft323():
  {==}

assert mt323:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt323():
  {==}

assert ft324:
  {alltrue(full(n7())) == T{} : Bool}

def ft324():
  {==}

assert mt324:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt324():
  {==}

assert ft325:
  {alltrue(full(n12())) == T{} : Bool}

def ft325():
  {==}

assert mt325:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt325():
  {==}

assert ft326:
  {alltrue(full(n11())) == T{} : Bool}

def ft326():
  {==}

assert mt326:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt326():
  {==}

assert ft327:
  {alltrue(full(n10())) == T{} : Bool}

def ft327():
  {==}

assert mt327:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt327():
  {==}

assert ft328:
  {alltrue(full(n9())) == T{} : Bool}

def ft328():
  {==}

assert mt328:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt328():
  {==}

assert ft329:
  {alltrue(full(n8())) == T{} : Bool}

def ft329():
  {==}

assert mt329:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt329():
  {==}

assert ft330:
  {alltrue(full(n7())) == T{} : Bool}

def ft330():
  {==}

assert mt330:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt330():
  {==}

assert ft331:
  {alltrue(full(n12())) == T{} : Bool}

def ft331():
  {==}

assert mt331:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt331():
  {==}

assert ft332:
  {alltrue(full(n11())) == T{} : Bool}

def ft332():
  {==}

assert mt332:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt332():
  {==}

assert ft333:
  {alltrue(full(n10())) == T{} : Bool}

def ft333():
  {==}

assert mt333:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt333():
  {==}

assert ft334:
  {alltrue(full(n9())) == T{} : Bool}

def ft334():
  {==}

assert mt334:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt334():
  {==}

assert ft335:
  {alltrue(full(n8())) == T{} : Bool}

def ft335():
  {==}

assert mt335:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt335():
  {==}

assert ft336:
  {alltrue(full(n7())) == T{} : Bool}

def ft336():
  {==}

assert mt336:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt336():
  {==}

assert ft337:
  {alltrue(full(n12())) == T{} : Bool}

def ft337():
  {==}

assert mt337:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt337():
  {==}

assert ft338:
  {alltrue(full(n11())) == T{} : Bool}

def ft338():
  {==}

assert mt338:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt338():
  {==}

assert ft339:
  {alltrue(full(n10())) == T{} : Bool}

def ft339():
  {==}

assert mt339:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt339():
  {==}

assert ft340:
  {alltrue(full(n9())) == T{} : Bool}

def ft340():
  {==}

assert mt340:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt340():
  {==}

assert ft341:
  {alltrue(full(n8())) == T{} : Bool}

def ft341():
  {==}

assert mt341:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt341():
  {==}

assert ft342:
  {alltrue(full(n7())) == T{} : Bool}

def ft342():
  {==}

assert mt342:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt342():
  {==}

assert ft343:
  {alltrue(full(n12())) == T{} : Bool}

def ft343():
  {==}

assert mt343:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt343():
  {==}

assert ft344:
  {alltrue(full(n11())) == T{} : Bool}

def ft344():
  {==}

assert mt344:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt344():
  {==}

assert ft345:
  {alltrue(full(n10())) == T{} : Bool}

def ft345():
  {==}

assert mt345:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt345():
  {==}

assert ft346:
  {alltrue(full(n9())) == T{} : Bool}

def ft346():
  {==}

assert mt346:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt346():
  {==}

assert ft347:
  {alltrue(full(n8())) == T{} : Bool}

def ft347():
  {==}

assert mt347:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt347():
  {==}

assert ft348:
  {alltrue(full(n7())) == T{} : Bool}

def ft348():
  {==}

assert mt348:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt348():
  {==}

assert ft349:
  {alltrue(full(n12())) == T{} : Bool}

def ft349():
  {==}

assert mt349:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt349():
  {==}

assert ft350:
  {alltrue(full(n11())) == T{} : Bool}

def ft350():
  {==}

assert mt350:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt350():
  {==}

assert ft351:
  {alltrue(full(n10())) == T{} : Bool}

def ft351():
  {==}

assert mt351:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt351():
  {==}

assert ft352:
  {alltrue(full(n9())) == T{} : Bool}

def ft352():
  {==}

assert mt352:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt352():
  {==}

assert ft353:
  {alltrue(full(n8())) == T{} : Bool}

def ft353():
  {==}

assert mt353:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt353():
  {==}

assert ft354:
  {alltrue(full(n7())) == T{} : Bool}

def ft354():
  {==}

assert mt354:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt354():
  {==}

assert ft355:
  {alltrue(full(n12())) == T{} : Bool}

def ft355():
  {==}

assert mt355:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt355():
  {==}

assert ft356:
  {alltrue(full(n11())) == T{} : Bool}

def ft356():
  {==}

assert mt356:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt356():
  {==}

assert ft357:
  {alltrue(full(n10())) == T{} : Bool}

def ft357():
  {==}

assert mt357:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt357():
  {==}

assert ft358:
  {alltrue(full(n9())) == T{} : Bool}

def ft358():
  {==}

assert mt358:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt358():
  {==}

assert ft359:
  {alltrue(full(n8())) == T{} : Bool}

def ft359():
  {==}

assert mt359:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt359():
  {==}

assert ft360:
  {alltrue(full(n7())) == T{} : Bool}

def ft360():
  {==}

assert mt360:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt360():
  {==}

assert ft361:
  {alltrue(full(n12())) == T{} : Bool}

def ft361():
  {==}

assert mt361:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt361():
  {==}

assert ft362:
  {alltrue(full(n11())) == T{} : Bool}

def ft362():
  {==}

assert mt362:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt362():
  {==}

assert ft363:
  {alltrue(full(n10())) == T{} : Bool}

def ft363():
  {==}

assert mt363:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt363():
  {==}

assert ft364:
  {alltrue(full(n9())) == T{} : Bool}

def ft364():
  {==}

assert mt364:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt364():
  {==}

assert ft365:
  {alltrue(full(n8())) == T{} : Bool}

def ft365():
  {==}

assert mt365:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt365():
  {==}

assert ft366:
  {alltrue(full(n7())) == T{} : Bool}

def ft366():
  {==}

assert mt366:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt366():
  {==}

assert ft367:
  {alltrue(full(n12())) == T{} : Bool}

def ft367():
  {==}

assert mt367:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt367():
  {==}

assert ft368:
  {alltrue(full(n11())) == T{} : Bool}

def ft368():
  {==}

assert mt368:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt368():
  {==}

assert ft369:
  {alltrue(full(n10())) == T{} : Bool}

def ft369():
  {==}

assert mt369:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt369():
  {==}

assert ft370:
  {alltrue(full(n9())) == T{} : Bool}

def ft370():
  {==}

assert mt370:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt370():
  {==}

assert ft371:
  {alltrue(full(n8())) == T{} : Bool}

def ft371():
  {==}

assert mt371:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt371():
  {==}

assert ft372:
  {alltrue(full(n7())) == T{} : Bool}

def ft372():
  {==}

assert mt372:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt372():
  {==}

assert ft373:
  {alltrue(full(n12())) == T{} : Bool}

def ft373():
  {==}

assert mt373:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt373():
  {==}

assert ft374:
  {alltrue(full(n11())) == T{} : Bool}

def ft374():
  {==}

assert mt374:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt374():
  {==}

assert ft375:
  {alltrue(full(n10())) == T{} : Bool}

def ft375():
  {==}

assert mt375:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt375():
  {==}

assert ft376:
  {alltrue(full(n9())) == T{} : Bool}

def ft376():
  {==}

assert mt376:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt376():
  {==}

assert ft377:
  {alltrue(full(n8())) == T{} : Bool}

def ft377():
  {==}

assert mt377:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt377():
  {==}

assert ft378:
  {alltrue(full(n7())) == T{} : Bool}

def ft378():
  {==}

assert mt378:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt378():
  {==}

assert ft379:
  {alltrue(full(n12())) == T{} : Bool}

def ft379():
  {==}

assert mt379:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt379():
  {==}

assert ft380:
  {alltrue(full(n11())) == T{} : Bool}

def ft380():
  {==}

assert mt380:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt380():
  {==}

assert ft381:
  {alltrue(full(n10())) == T{} : Bool}

def ft381():
  {==}

assert mt381:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt381():
  {==}

assert ft382:
  {alltrue(full(n9())) == T{} : Bool}

def ft382():
  {==}

assert mt382:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt382():
  {==}

assert ft383:
  {alltrue(full(n8())) == T{} : Bool}

def ft383():
  {==}

assert mt383:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt383():
  {==}

assert ft384:
  {alltrue(full(n7())) == T{} : Bool}

def ft384():
  {==}

assert mt384:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt384():
  {==}

assert ft385:
  {alltrue(full(n12())) == T{} : Bool}

def ft385():
  {==}

assert mt385:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt385():
  {==}

assert ft386:
  {alltrue(full(n11())) == T{} : Bool}

def ft386():
  {==}

assert mt386:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt386():
  {==}

assert ft387:
  {alltrue(full(n10())) == T{} : Bool}

def ft387():
  {==}

assert mt387:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt387():
  {==}

assert ft388:
  {alltrue(full(n9())) == T{} : Bool}

def ft388():
  {==}

assert mt388:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt388():
  {==}

assert ft389:
  {alltrue(full(n8())) == T{} : Bool}

def ft389():
  {==}

assert mt389:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt389():
  {==}

assert ft390:
  {alltrue(full(n7())) == T{} : Bool}

def ft390():
  {==}

assert mt390:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt390():
  {==}

assert ft391:
  {alltrue(full(n12())) == T{} : Bool}

def ft391():
  {==}

assert mt391:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt391():
  {==}

assert ft392:
  {alltrue(full(n11())) == T{} : Bool}

def ft392():
  {==}

assert mt392:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt392():
  {==}

assert ft393:
  {alltrue(full(n10())) == T{} : Bool}

def ft393():
  {==}

assert mt393:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt393():
  {==}

assert ft394:
  {alltrue(full(n9())) == T{} : Bool}

def ft394():
  {==}

assert mt394:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt394():
  {==}

assert ft395:
  {alltrue(full(n8())) == T{} : Bool}

def ft395():
  {==}

assert mt395:
  {mirror(full(n6())) == full(n6()) : Tree}

def mt395():
  {==}

assert ft396:
  {alltrue(full(n7())) == T{} : Bool}

def ft396():
  {==}

assert mt396:
  {mirror(full(n9())) == full(n9()) : Tree}

def mt396():
  {==}

assert ft397:
  {alltrue(full(n12())) == T{} : Bool}

def ft397():
  {==}

assert mt397:
  {mirror(full(n7())) == full(n7()) : Tree}

def mt397():
  {==}

assert ft398:
  {alltrue(full(n11())) == T{} : Bool}

def ft398():
  {==}

assert mt398:
  {mirror(full(n10())) == full(n10()) : Tree}

def mt398():
  {==}

assert ft399:
  {alltrue(full(n10())) == T{} : Bool}

def ft399():
  {==}

assert mt399:
  {mirror(full(n8())) == full(n8()) : Tree}

def mt399():
  {==}

