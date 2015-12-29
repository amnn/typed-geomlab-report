```
{ Comments are surrounded by curly brackets
  { And can be nested }. }

{ Pattern Matching }
{ In the formal parameters of functions. }
define length([])   = 0
     | length(x:xs) = 1 + length(xs);

{ Guards }
{ Prefixed by the `when` keyword, and appearing at the end
  of an equation defining (a part of) a function. For a case
  to match, the patterns must match *and* the guard must
  evaluate to true. }
define filter(p, x:xs) = x : filter(p, xs) when p(x)
     | filter(p, _:xs) =     filter(p, xs)
     | filter(_, [])   = [];

{ Ranges }
[1..3]; { --> [1, 2, 3] }

{ List Comprehensions }
[ 10*x + y | x <- [1..3], y <- [1..3] when (x+y) mod 2 = 0];
{ --> [11, 13, 22, 31, 33] }

{ Operator Sections }
(+10); { Equivalent to: } function (x) x + 10;
```
