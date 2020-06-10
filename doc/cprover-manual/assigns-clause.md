## CBMC Assigns Clause

### Introduction
Here is described the syntax and semantics of the "assigns" clause as implemented in CBMC. This construct allows the user to specify a list of memory locations which may be written within a particular scope. While an assigns clause may, in general, be interpreted with either "writes" or "modifies" semantics, this design is based on the former.
This means that memory not captured by the assigns clause must not be written within the given scope, even if the value(s) therein are not modified.

The latest iteration of this design focuses on specifying assigns clauses for simple variable types, structs, and their pointers. Arrays and recursive pointer structures are left to future contibutions.


##### Syntax
A special construct is introduced to specify assigns clauses. Its syntax is defined as follows.

```
 <assigns_clause> := __CPROVER_assigns ( <target_list> )
```
```
 <target_list> := <target>
                | <target_list> , <target>
```
```
 <target> := <member_target>
           | * <target>
```
```
 <member_target> := <primary_target>
                  | <member_target> . <member_name>
                  | <member_target> -> <member_name>
```
```
 <primary_target> := <identifier>
                  | ( <target> )
```


The `<assigns_clause>` states that only memory identified by the identifiers (`<primary_target>`), structure members (`<member_identifier>`), and dereference expressions listed in the contained `<target_list>` may be written within the associated scope, as follows.

##### Semantics
The semantics of an assigns clause *c* of some function *f* can be understood in two contexts. First, one may consider how the expressions in *c* are treated when a call to *f* is replaced by its contract specification, assuming the contract specification is a sound characterization of the behavior of *f*. Second, one may consider how *c* is applied the function body of *f* in order to determine whether *c* is a sound characterization of the behavior of *f*. We begin by exploring these two perspectives for assigns clauses which contain only scalar expressions.

Let the i<sup>th</sup> expression in some assigns clause *c* be denoted *exprs*<sub>*c*</sub>[i], the j<sup>th</sup> formal parameter of some function *f* be denoted *params*<sub>*f*</sub>[j], and the k<sup>th</sup> argument passed in a call to function *f* be denoted *args*<sub>*f*</sub>[k] (an identifying index may be added to distinguish a *particular* call to *f*, but for simplicity it is omitted here).

###### Replacement
Assuming an assigns clause *c* is a sound characterization of the behavior of the function *f*, a call  to *f* may be replaced a series of non-deterministic assignments. For each expression *e* &#8712; *exprs*<sub>*c*</sub>, let there be an assignment &#632; := &#8727;, where &#632; is *args*<sub>*f*</sub>[i] if *e* is identical to some *params*<sub>*f*</sub>[i], and *e* otherwise.

###### Enforcement
In order to determine whether an assigns clause *c* is a sound characterization of the behavior of a function *f*, the body of the function is instrumented with a set of expressions *assignable* representing the memory frame in which assignments may be made. The set *assignable* is constructed follows.

1. For each expression *e* &#8712; *exprs*<sub>*c*</sub>, create a temporary variable *tmp*<sub>*e*</sub> to store \&(*e*), the address of *e*, at the start of *f*. Add *tmp*<sub>*e*</sub> to *addignable*.
2. Additionally, for each expression *e* &#8712; *exprs*<sub>*c*</sub> of struct type, start again at step 1 for each  member *x* of *e* (denoted *e*.*x*).

Additionally, perform steps 1 and 2 for each object created by a memory-allocating function (e.g. `malloc`). For example, the statement `x = (int *)malloc(sizeof(int))` would result in a pointer to `x` being added to *assignable*. If memory is allocated for a struct, the subcomponents are added to *assignable* as well.

Then, while sequentially traversing the associated function body, statements which may modify memory are instrumented with a preceeding assertion to ensure that they only modify memory referenced by *assignable*, as follows.

- Before each assignment statement, *lhs* := *rhs*, add an assertion (structured as a disjunction)

assert(&#8707; *tmp*<sub>*e*</sub>. __CPROVER_same_object(&(*lhs*), *tmp*<sub>*e*</sub>) && __CPROVER_POINTER_OFFSET(&(*lhs*)) == __CPROVER_POINTER_OFFSET(*tmp*<sub>*e*</sub>) && sizeof(lhs) == sizeof(\**tmp*<sub>*e*</sub>))
- Before each function call with an assigns clause *a*, add an assertion for each *e*<sub>*a*</sub> &#8712; *exprs*<sub>*a*</sub> (also formulated as a disjunction)

assert(&#8707; *tmp*<sub>*e*</sub>. __CPROVER_same_object(&(*e*<sub>*a*</sub>), *tmp*<sub>*e*</sub>) && __CPROVER_POINTER_OFFSET(&(*e*<sub>*a*</sub>)) == __CPROVER_POINTER_OFFSET(*tmp*<sub>*e*</sub>) && sizeof(*e*<sub>*a*</sub>) == sizeof(\**tmp*<sub>*e*</sub>))

These assertions ensure that the modified memory has the same size, offset, and object identifier in the memory model as something in *assignable*. Additionally, for each function call without an assigns clause, add an assertion assert(*false*) to ensure that the assigns contract will only hold if all called functions have an assigns clause which is compatible with that of the calling function.

Finally, a set of freely-assignable symbols *free* is tracked during the traversal of the function body. These are locally-defined variables and formal parameters without dereferences. For example, in a variable declaration `<type> x = <initial_value>`, `x` would be added to *free*. Assignment statements where the left-hand-side is in *free* are not instrumented with the above assertion.
