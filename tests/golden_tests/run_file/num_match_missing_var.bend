if 0 t f = f
if 1 t f = t

if2 n t f = switch n {
  0: f
  _: t
  _: f
}

if3 n t f = switch n {
  0: f
  _: t
  1: t
}

main = (if2 1 2 3)
