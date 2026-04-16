A .math file is shaped like this:

A Hypothesis block, defined by the "Hypothesis" keyword followed by a colon, and then, indented, the actual definitions

Then, after that, the Proof block, defined by the "Proof" keyword and a colon, followed by, indented, the statements in the proof

The current keywords are

*let*, which can define an edge, a triangle or an angle, like: "let ABC" or "let XY"

*iso*, which after the definition of a triangle defines its two sides as equal. If followed by *base* it can define which two sides are, for example "let ABC iso base AB" would mean that AC = BC, and "let ABC iso base AC" would mean that AB = BC. If no base is given, the first two points will be implied as base.

A triangle (in future any plane) is written as its points, so it could be ABC or ABCD.

An angle is written as angABC, where A, B and C are the three points defining it.

An edge is defined by its two extremes