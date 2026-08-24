# bend3's term_subst fence, scale layer: a match on the RESULT of a
# call, 128 def-call boundaries deep -- the quadratic-substitution
# counter is gone (no --stats), the boundary chain itself carries on
# base Nat and answers on every lane (the acc guard's 0/k arms become
# is_lt's Bool)
import Base

assert n0:
  Nat

def n0():
  0n

assert n1:
  Nat

def n1():
  Succ{n0()}

assert n2:
  Nat

def n2():
  Succ{n1()}

assert n3:
  Nat

def n3():
  Succ{n2()}

assert n4:
  Nat

def n4():
  Succ{n3()}

assert n5:
  Nat

def n5():
  Succ{n4()}

assert n6:
  Nat

def n6():
  Succ{n5()}

assert n7:
  Nat

def n7():
  Succ{n6()}

assert n8:
  Nat

def n8():
  Succ{n7()}

assert n9:
  Nat

def n9():
  Succ{n8()}

assert n10:
  Nat

def n10():
  Succ{n9()}

assert n11:
  Nat

def n11():
  Succ{n10()}

assert n12:
  Nat

def n12():
  Succ{n11()}

assert n13:
  Nat

def n13():
  Succ{n12()}

assert n14:
  Nat

def n14():
  Succ{n13()}

assert n15:
  Nat

def n15():
  Succ{n14()}

assert n16:
  Nat

def n16():
  Succ{n15()}

assert n17:
  Nat

def n17():
  Succ{n16()}

assert n18:
  Nat

def n18():
  Succ{n17()}

assert n19:
  Nat

def n19():
  Succ{n18()}

assert n20:
  Nat

def n20():
  Succ{n19()}

assert n21:
  Nat

def n21():
  Succ{n20()}

assert n22:
  Nat

def n22():
  Succ{n21()}

assert n23:
  Nat

def n23():
  Succ{n22()}

assert n24:
  Nat

def n24():
  Succ{n23()}

assert n25:
  Nat

def n25():
  Succ{n24()}

assert n26:
  Nat

def n26():
  Succ{n25()}

assert n27:
  Nat

def n27():
  Succ{n26()}

assert n28:
  Nat

def n28():
  Succ{n27()}

assert n29:
  Nat

def n29():
  Succ{n28()}

assert n30:
  Nat

def n30():
  Succ{n29()}

assert n31:
  Nat

def n31():
  Succ{n30()}

assert n32:
  Nat

def n32():
  Succ{n31()}

assert n33:
  Nat

def n33():
  Succ{n32()}

assert n34:
  Nat

def n34():
  Succ{n33()}

assert n35:
  Nat

def n35():
  Succ{n34()}

assert n36:
  Nat

def n36():
  Succ{n35()}

assert n37:
  Nat

def n37():
  Succ{n36()}

assert n38:
  Nat

def n38():
  Succ{n37()}

assert n39:
  Nat

def n39():
  Succ{n38()}

assert n40:
  Nat

def n40():
  Succ{n39()}

assert n41:
  Nat

def n41():
  Succ{n40()}

assert n42:
  Nat

def n42():
  Succ{n41()}

assert n43:
  Nat

def n43():
  Succ{n42()}

assert n44:
  Nat

def n44():
  Succ{n43()}

assert n45:
  Nat

def n45():
  Succ{n44()}

assert n46:
  Nat

def n46():
  Succ{n45()}

assert n47:
  Nat

def n47():
  Succ{n46()}

assert n48:
  Nat

def n48():
  Succ{n47()}

assert n49:
  Nat

def n49():
  Succ{n48()}

assert n50:
  Nat

def n50():
  Succ{n49()}

assert n51:
  Nat

def n51():
  Succ{n50()}

assert n52:
  Nat

def n52():
  Succ{n51()}

assert n53:
  Nat

def n53():
  Succ{n52()}

assert n54:
  Nat

def n54():
  Succ{n53()}

assert n55:
  Nat

def n55():
  Succ{n54()}

assert n56:
  Nat

def n56():
  Succ{n55()}

assert n57:
  Nat

def n57():
  Succ{n56()}

assert n58:
  Nat

def n58():
  Succ{n57()}

assert n59:
  Nat

def n59():
  Succ{n58()}

assert n60:
  Nat

def n60():
  Succ{n59()}

assert n61:
  Nat

def n61():
  Succ{n60()}

assert n62:
  Nat

def n62():
  Succ{n61()}

assert n63:
  Nat

def n63():
  Succ{n62()}

assert n64:
  Nat

def n64():
  Succ{n63()}

assert n65:
  Nat

def n65():
  Succ{n64()}

assert n66:
  Nat

def n66():
  Succ{n65()}

assert n67:
  Nat

def n67():
  Succ{n66()}

assert n68:
  Nat

def n68():
  Succ{n67()}

assert n69:
  Nat

def n69():
  Succ{n68()}

assert n70:
  Nat

def n70():
  Succ{n69()}

assert n71:
  Nat

def n71():
  Succ{n70()}

assert n72:
  Nat

def n72():
  Succ{n71()}

assert n73:
  Nat

def n73():
  Succ{n72()}

assert n74:
  Nat

def n74():
  Succ{n73()}

assert n75:
  Nat

def n75():
  Succ{n74()}

assert n76:
  Nat

def n76():
  Succ{n75()}

assert n77:
  Nat

def n77():
  Succ{n76()}

assert n78:
  Nat

def n78():
  Succ{n77()}

assert n79:
  Nat

def n79():
  Succ{n78()}

assert n80:
  Nat

def n80():
  Succ{n79()}

assert n81:
  Nat

def n81():
  Succ{n80()}

assert n82:
  Nat

def n82():
  Succ{n81()}

assert n83:
  Nat

def n83():
  Succ{n82()}

assert n84:
  Nat

def n84():
  Succ{n83()}

assert n85:
  Nat

def n85():
  Succ{n84()}

assert n86:
  Nat

def n86():
  Succ{n85()}

assert n87:
  Nat

def n87():
  Succ{n86()}

assert n88:
  Nat

def n88():
  Succ{n87()}

assert n89:
  Nat

def n89():
  Succ{n88()}

assert n90:
  Nat

def n90():
  Succ{n89()}

assert n91:
  Nat

def n91():
  Succ{n90()}

assert n92:
  Nat

def n92():
  Succ{n91()}

assert n93:
  Nat

def n93():
  Succ{n92()}

assert n94:
  Nat

def n94():
  Succ{n93()}

assert n95:
  Nat

def n95():
  Succ{n94()}

assert n96:
  Nat

def n96():
  Succ{n95()}

assert n97:
  Nat

def n97():
  Succ{n96()}

assert n98:
  Nat

def n98():
  Succ{n97()}

assert n99:
  Nat

def n99():
  Succ{n98()}

assert n100:
  Nat

def n100():
  Succ{n99()}

assert n101:
  Nat

def n101():
  Succ{n100()}

assert n102:
  Nat

def n102():
  Succ{n101()}

assert n103:
  Nat

def n103():
  Succ{n102()}

assert n104:
  Nat

def n104():
  Succ{n103()}

assert n105:
  Nat

def n105():
  Succ{n104()}

assert n106:
  Nat

def n106():
  Succ{n105()}

assert n107:
  Nat

def n107():
  Succ{n106()}

assert n108:
  Nat

def n108():
  Succ{n107()}

assert n109:
  Nat

def n109():
  Succ{n108()}

assert n110:
  Nat

def n110():
  Succ{n109()}

assert n111:
  Nat

def n111():
  Succ{n110()}

assert n112:
  Nat

def n112():
  Succ{n111()}

assert n113:
  Nat

def n113():
  Succ{n112()}

assert n114:
  Nat

def n114():
  Succ{n113()}

assert n115:
  Nat

def n115():
  Succ{n114()}

assert n116:
  Nat

def n116():
  Succ{n115()}

assert n117:
  Nat

def n117():
  Succ{n116()}

assert n118:
  Nat

def n118():
  Succ{n117()}

assert n119:
  Nat

def n119():
  Succ{n118()}

assert n120:
  Nat

def n120():
  Succ{n119()}

assert n121:
  Nat

def n121():
  Succ{n120()}

assert n122:
  Nat

def n122():
  Succ{n121()}

assert n123:
  Nat

def n123():
  Succ{n122()}

assert n124:
  Nat

def n124():
  Succ{n123()}

assert n125:
  Nat

def n125():
  Succ{n124()}

assert n126:
  Nat

def n126():
  Succ{n125()}

assert n127:
  Nat

def n127():
  Succ{n126()}

assert n128:
  Nat

def n128():
  Succ{n127()}

assert run:
  forall n: Nat
  forall +acc: +U32
  U32

def run(n, acc):
  match n:
    case Zero{}:
      acc
    case Succ{p}:
      match U32.is_lt(acc, 1000):
        case False{}:
          run(p, acc)
        case True{}:
          run(p, acc + 1)

assert t:
  U32

def t():
  match run(n128(), 1):
    case U32{w}:
      U32{w} + 1

assert main.out:
  Nat

def main.out():
  U32.to_nat(t())

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
130n
$$ bend % --js
130n
exit 0
