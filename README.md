[Fpy](https://github.com/fprime-community/fpy) is an advanced sequencing language for the NASA JPL [F Prime flight software framework](https://github.com/nasa/fprime).

# Goals of fpy-cert
* Specfiy the syntax and semantics of Fpy
* Implement a reference compiler to LLVM IR for Fpy
* Translation validation between Fpy source and the output LLVM IR

# Current status
* Rather than starting immediately with the full language, fpy-cert is working with FpyE, a "toy" language whose syntax is a subset of Fpy's
* FpyE is short for FpyExpression, and its syntax will be equivalent to Fpy's `expr` syntax.

# Implementation details
## Syntax
The abstract syntax of Fpy is represented as a `Term` variant.

Values in Fpy are a specific constructor of the `Term` variant which accepts a `Value` variant.
```
(* construct a term representing the unit value *)
t_value (v_unit)
```

Syntactic types in Fpy are just a `Ty` variant.


## Static semantics
The denotation of a syntactic type is `Value -> Prop`.

The next goals are writing a type checker, and a subtyping relation.

## Dynamic semantics

Fpy's dynamic semantics are specified in two parts: a denotation in interaction trees of uninterpreted events, and an interpretation of a subset of these events in a host environment.

### Denotation in interaction trees
First, terms are denoted as (interaction trees)[https://dl.acm.org/doi/abs/10.1145/3371119]. Interaction trees (ITrees) are a data structure which can model programs that send and receive values from some outside environment via events. You can define some events which the tree can emit, and the event constructors can take values to send to the environment. The events have "return types", and for each event you raise, you must specify a continuation function of a value of the return type, thus allowing you to handle values from the environment without knowing them ahead of time.


In other words, events are observable to the outside system, and unobservable behavior must be implemented as a continuation on a value returned by an event. I think of the unobservable behavior inside of the continuation as a kind of "sub-semantics", as it's really a second kind of denotational semantics inside the overall denotational semantics of ITrees.

There are a few groups of events that Fpy programs can raise currently:
* Panic events
    * Overflow (void)
    * TlmNotFound (Z -> void)
* Host events
    * GetTlm (Z -> Value)
* Ill-formed events
    * TypeError (string -> void)

Note that, on their own, these events have no interpretation. This first step knows nothing about what these events actually do, beyond their input and output types. Also note that if the output type is void, then the continuation is dead code, because no value can be constructed of type void. So events that output void act to end the program.

#### Sub-semantics of interaction trees
Inside of ITree continuations, the denotation uses the Rocq Stdlib, plus Vellvm's integer and float libraries (which are not necessarily specific to LLVM IR). The Vellvm float library in turn uses Flocq, a formalization of IEEE-754 floating point numbers.

### Interpretation of events

Once we have a program in terms of events and continuations, we can interpret these events in some host environment. For instance, let `S` be a function from integer telemetry channel ids to `option Value`. For an event `G = (GetTlm z, continuation)`, where `continuation : Value -> ITree`, if `S[z] = Some v`, then we can replace `G` with `continuation v`. Otherwise, if `S[z] = None`, we can replace `G` with `TlmNotFound z`.

By this method, we can rewrite the program without any non-void events. At this point we should either have a single void event (must be just one because continuation must be empty), or the program returns a single value (meaning it successfully ran and evaluated to a value).
