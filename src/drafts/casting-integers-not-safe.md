% Casting from `int256` to a lower precision integer is not safe unless magnitude is correct
% Sean Seefried
% Sat 11 June 2022

Casting from `intXXX` to `intYYY` (where `XXX > YYY`) seems to just discard the bits at the front.

e.g. Take  this `int256` value as an example: `-155375551331732109056687343`
Now we cast it to `int88`. A comparison of the bit patterns appears below:


```
ffffffffffffffffffffffffffffffffffffffffff7f79f27c189600a779c311
                                          7f79f27c189600a779c311
```

The first 168 bits have just been chopped off.

This wasn't safe to begin with since `-155375551331732109056687343` is outside the range of `int88`. This is because `type(int88).min = -154742504910672534362390527` which is `633046421059574694296816` larger.

Since the casting algorithm is so _blunt_ it's quite possible to cast a negative number to a positive number, and here is no exception.
