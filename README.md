[Fpy](https://github.com/fprime-community/fpy) is an advanced sequencing language for the NASA JPL [F Prime flight software framework](https://github.com/nasa/fprime).

# Goals of fpy-cert
* Specfiy the syntax and semantics of Fpy
* Implement a reference compiler to LLVM IR for Fpy
* Translation validation between Fpy source and the output LLVM IR

# Current status
* Rather than starting immediately with the full language, fpy-cert is working with FpyE, a "toy" language whose syntax is a subset of Fpy's
* FpyE is short for FpyExpression, and its syntax will be equivalent to Fpy's `expr` syntax
* FpyE 

# Implementation details
The abstract syntax of FpyE is represented as a `Term` variant.

Values in Fpy are a specific constructor of the `Term` variant which accepts a `Value` variant.
```
(* construct a term representing the unit value *)
t_value (v_unit)
```

Syntactic types in Fpy are just a `Ty` variant. The only relatively interesting type syntactically is the 

