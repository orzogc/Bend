Take_ n list =
  switch _ = (== n 0) {
  | 0: (Take n list)
  | _: []
  }
Take n (List/nil) = []
Take n (List/cons x xs) = (List/cons x (Take_ (- n 1) xs))

main = (Take 2 [3, 2, 1, 5, 5, 5])
