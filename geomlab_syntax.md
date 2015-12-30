```
{ { i } }

{ ii }
define length([])   = 0
     | length(x:xs) = 1 + length(xs);

{ iii }
define filter(p, x:xs) = x : filter(p, xs) when p(x)
     | filter(p, _:xs) =     filter(p, xs)
     | filter(_, [])   = [];

{ iv }
function (x) x;

{ v }
[1..3];

{ vi }
[ 10*x + y | x <- [1..3], y <- [1..3] when (x+y) mod 2 = 0];

{ vii }
(+10);
```
