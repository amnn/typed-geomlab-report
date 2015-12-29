```
{ Operator Sections }
define _lsect(f, x) = function (y) f(x, y);
define _rsect(f, y) = function (x) f(x, y);

{ Ranges }
define _range(a, b) = if a > b then [] else a:_range(a+1, b):

{ List Comprehensions }
define _mapa(f, [],   acc) = acc
     | _mapa(f, x:xs, acc) = f(x, _mapa(f, xs, acc));
```
