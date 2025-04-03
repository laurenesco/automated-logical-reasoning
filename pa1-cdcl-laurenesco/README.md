[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-22041afd0340ce965d47ae6ef1cefeee28c7c493a6346c4f15d667ab976d596c.svg)](https://classroom.github.com/a/CSmNR6hj)
# CDCL SAT solver.

This repository contains the framework you must extend to solve
Programming Assignment 1. In the following sections, we describe how you can build
and extend the framework. We present commands for UNIX-based
systems. However, these commands are simple enough, and it shouldn't
be hard to port them to other platforms.

## Building and Running the Project.

### Prerequisite.

This project is built with maven. If your system does not have maven
installed, follow system-specific instructions on how to install it
[here](https://maven.apache.org/install.html).

### Building the JAR file.

In order to build the project simply type the following command:

```
$ mvn package
```

This will create a JAR named
`pa1-1.0-SNAPSHOT-jar-with-dependencies.jar` under directory `target`.


### Running the Project.

To run the project simply run the following command:

```
$ java -cp target/pa1-1.0-SNAPSHOT-jar-with-dependencies.jar <fully qualified name of Main class>
```

The program accepts the formula through the standard input. If you are 
typing the expression manually on the terminal, you must also explicitly
type EOF (Ctrl+d in UNIX systems). The easiest way would be to redirect
the input from a file to the application, like the following:

```
$ java -cp target/pa1-1.0-SNAPSHOT-jar-with-dependencies.jar edu.utexas.cs.alr.SATDriver < <path to input file>
```

`edu.utexas.cs.alr.SATDriver` is the main class for this programming
assignment. It invokes method `SatUtils.checkSAT` and it prints either `SAT`
or `UNSAT` depending on the return value of the `checkSAT`.

By default, invoking the tool with this class is going
to throw an `UnsupportedOperationException` with the message
"implement this". To complete this programming assignment, 
you must implement the body of `SatUtil.checkSat` that throws this type of exception.

### Input Format.

The program accepts propositional formulas in prefix format. For
instance, the input `(impl x1 (not x2))` represents the propositional
formula `x1 -> not x2`. Propositional variables are of the form `xN`,
where N is a positive integer (i.e., `N > 0`). The BNF grammar for the
input format can be found in
`src/main/antlr4/edu/utexas/cs/alr/parser/Expr.g4`. You can find some
sample input formulas under directory
`resources/sample-inputs`. Furthermore, directory
`resources/test-cases` contains several test cases you can use to test
your implementation. Directory `sat` contains statisfiable formulas,
whereas directory `unsat` contains unsatisfiable formulas.

## Framework Outline.

The framework provides some basic functionality for creating and
manipulating ASTs for propositional formulas. You must use the
provided components in order to implement the missing parts of the
framework (as also mentioned above). You can generally create any
additional classes you need for implementing the required
functionality. But you **cannot** modify the main classes (mentioned
above) and use any libraries except for Java's standard library.

### Performing Tseitin's Transformation.

Package `edu.utexas.cs.alr.util.ExprUtils` contains an implementation of
Tseitin's transformation. This is already wired up for you in `edu.utexas.cs.alr.SatDriver`.

### The Implication Graph.

A critical step towards implementing the CDCL algorithm is to
design and implement an implication graph. This is a key part
of the assignment and so we provide some general guidelines.
In general, your implication graph should be able to:

* track a set of root nodes.
* track the current decision level.
* track the decision level at each node.
* track the clause associated with each edge.
* track unique implication points.
* etc.

### Creating and manipulating expressions.

You should not have to use any of the information in this section
as the required infrastructure is already implemented. This is 
included merely as a reference.

Package `edu.utexas.cs.alr.ast` contains classes that describe
ASTs for propositional formulas. Every class is a subtype of
`edu.utexas.cs.alr.ast.Expr`. The base class contains a single
abstract method called `getKind`, which returns the type of the
expression (e.g., OR, AND, IMPL, etc.).

To create an AST node you must use class
`edu.utexas.cs.alr.ast.ExprFactory`. This class provides one
static method for each type of node. For example, the following
code snippet creates an AST for expression `(and x1 (not x2))`.

```
import edu.utexas.cs.alr.ast.*;

...

VarExpr x1 = ExprFactory.mkVAR(1),
        x2 = ExprFactory.mkVAR(2);
NegExpr notX2 = ExprFactory.mkNEG(x2);
AndExpr and = ExprFactory.mkAND(x1, notX2);
```

This factory class memorizes all the expressions it creates and always returns
the same expression for syntactically equivalent propositional formulas. That is,
if you invoke a static method with the same arguments multiple types, the return
value is always going to be the first expression the factory returned. For example,
consider the following code snippet:

```
import edu.utexas.cs.alr.ast.*;

...

VarExpr x1 = ExprFactory.mkVAR(1),
        x2 = ExprFactory.mkVAR(2);

AndExpr and1 = ExprFactory.mkAND(x1, x2),
        and2 = ExprFactory.mkAND(x1, x2);

assert and1 == and2; // This assertion holds
```

The assertion above is guaranteed to hold. That means, in case you want whether two
`Expr` objects are syntactically equivalent, you just need to compare them with Java's
`==` operator.
