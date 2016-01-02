```
define foldr(f, e, [])   = e
     | foldr(f, e, x:xs) = f(x, foldr(f, e, xs));

define filter(p, xs) =
  let check(x, xs) = x : xs when p(x)
    | check(_, xs) = xs
  in foldr(check, [], xs);
```
