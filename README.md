MathLang is a Programming Language aimed at defining and validating mathematical proofs.

Its main aim is to be as similar to real mathematical proofs in syntax and, when there's no correspondent, but pure programming, as readable as possible to anyone, which is done through the use of multiple keywords pointing to the same object and aliases, other than simplified syntax.

It defines the .math file format, which is mainly comprised of a Hypothesis block, defining what is true by definition, and a Proof block, where statements can be validated, new propositions can be proven and, in the end, some Thesis can be proven (there is no specified "thesis" block for now, as it would be just a specifier.)

To facilitate in proofs, you can define types based on existing types, adding constraints.

For example, one could say:
```
operation isEven Int -> Bool
    gives first mod 2 equals 2
    
type Even
    accepts Int
    matches isEven self
    
Hypothesis:
    let a be Even = 2  # Nothing happens, valid
    let b be Even = 3  # Errors out, constraint wasn't met
    let c be Even = "example"  # Errors out, Even type doesn't accept Strings
```

This syntax translates to:
1. Define the "isEven" operation, which takes an Integer as argument and gives a Boolean value as output
2. Define the type "Even", which accepts assignment from Integers and requires, as constraint, that any assignment to it matches the "isEven" operation (it must return true)
3. 'a' is a variable of type Even. 2, a literal Integer, was assigned to it, valid, and it matches the constraint, so nothing happens.
4. 'b' is also a variable of type Even, and while 3 is also a literal Integer, it doesn't match isEven, so the assignment will give an error.
5. 'c', again, is a var of type Even, but the value assigned to it, a String, isn't accepted by that type.

But the most foundational block of any mathematical system are its axioms and, from them, theorems.

In MathLang, an axiom can be defined using this syntax:
```
axiom SideSwitching:
    Given:
        let a be Int
        let b be Int
    Then:
        a + b equals b + a

Hypothesis:
    let c be Int
    let d be Int

Proof:
    SideSwitching{c, d} => c + d equals d + c
```

Using axioms, even unknown relationships can be established from basic constraints (a and b being Integers).
    
Theorems are, in most ways, akin to axioms, with the one main difference being they are first validated and then able to be directly used, for example:

