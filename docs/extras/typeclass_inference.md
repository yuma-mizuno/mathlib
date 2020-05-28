# Typeclass inference #

### Summary ###

This document is about the `[ ]` "square bracket" notation that is often seen in Lean code, for example `[group G]`, which somehow turns a type `G` into a group. Things in square brackets are managed by Lean's typeclass inference system. This document is an overview of everything, and in particular the first few sections contain plenty of overlap with Theorem Proving In Lean. The later sections are more detailed information about how type class inference works in Lean.

We'll start by briefly explaining the difference between `[ ]` brackets, `( )` brackets and `{ }` brackets. The type class inference system's job is to find terms whose types are in square brackets. We'll give an overview of how the system works, and will then go on to discuss its limitations, how to use it and how not to use it. The earlier sections might be useful for beginners, the later sections for people interested in implementation issues (*TODO* rewrite once finished). The perspective and examples are unashamedly mathematical.

## Introduction ##

Here is an overview of the various kinds of brackets that show up when defining function inputs in Lean. This document is mostly concerned with the square brackets `[ ]` but here we give a brief overview of the other main kinds too. Everything here is covered in Theorem Proving In Lean, although the write-up here is more geared towards mathematicians.

When defining a function in Lean, we use brackets to denote the inputs. For example

```lean
def double (n : ℕ) := n + n
```

defines a function `double` with one input `n`. These tound brackets `( )` are easiest to understand; these are arguments which Lean expects the user to supply. For example

```lean
#reduce double 4 -- 8
#reduce double -- Lean prints out the definition of the function
```

Without the input, the function doesn't run.

But there are other types of brackets that Lean can use when defining functions. The first ones that users typically learn about are the squiggly brackets `{ }`. Here is an example of their usage:

```lean
def mem_inter {X : Type} {U V : set X} {x : X} (hU : x ∈ U) (hV : x ∈ V) : x ∈ U ∩ V :=
begin
  show x ∈ U ∧ x ∈ V, -- equivalent to goal by definition
  split,
  { exact hU },
  { exact hV }
end

variables (B C : set ℕ)

example (h1 : 37 ∈ B) (h2 : 37 ∈ C) : 37 ∈ B ∩ C := mem_inter h1 h2
```

The function `mem_inter` takes six inputs: a type `X`, two subsets `U` and `V` of `X`, a term `x` of type `X`, and proofs `hU` and `hV`
that ` x ∈ U`  and `x ∈ V` respectively. But the first four of these inputs are in squiggly brackets `{ }`, which means that Lean does
not expect the user to supply them. As you can see in the example, the user just supplies the last two inputs `hU` and `hV`, the ones in
`()` brackets. The person who defined this function is saying "Go on Lean, just ask for `hU` and `hV`, take a look at what the user inputs,
and figure out the other four inputs yourself by solving a logic puzzle and considering the only possible way to make everything have the
right type". And indeed one can see that this should be possible; if `B` and `C` are subsets of the natural numbers (that is, terms of
type `set ℕ`), and the user inputs proofs that `37 ∈ B` and `37 ∈ C` to this function when Lean is expecting `hU` and `hV`, then Lean can
figure out that `x` must be `37`, `U` must be `B`, `V` must be `C` and `X` must be `ℕ`. This process is called `type unification` and it is what
you are asking Lean to do if you use `{ }` squiggly brackets.

But how about this?

```lean
import tactic

def assoc_assoc {G : Type} [add_group G] (g : G) : g + (g + (g + g)) = ((g + g) + g) + g :=
begin
  rw add_assoc,
  rw add_assoc
end

def x := (4 : ℤ)

example : x + (x + (x + x)) = ((x + x) + x) + x := assoc_assoc x
```

There are three inputs to `assoc_assoc` -- a type `G` (think of `G` as a set if you are more used to this way of thinking), a term of type
`add_group G` (that is, a term carrying all the definitions of the addition, additive inverse, and additive identity in `G`, and also
all the proofs that they satisfy the axioms of an additive group), and a term `g` of type `G` (i.e. an element `g` of `G`, if you
are used to thinking set-theoretically). The user is only asked to input `g`, Lean can now guess `G` using type unification (it's the
type of `g`) -- but how can Lean guess the group structure on `G` just by thinking about the types of everything? It can't. Indeed,
if you feed in a random element `x` of a random set `X` into `assoc_assoc` you will get an error

```
failed to synthesize type class instance for
X : Type,
x : X
⊢ add_group X
```

However, in the example above we fed in the integer `x` into `assoc_assoc`, and `x` was defined to be the integer `4`. Lean can then
figure out using unification `G` must be `ℤ` -- and now it realises that it needs to find an additive group structure on `ℤ`. Because
`[add_group G]` is in square brackets, Lean looks up the definition of of the additive group structure on the integers in a big database of definitions and theorems called the type class inference system. In Lean, when the integers are defined and made into an additive group,
the definition of the group structure was added into the database, and that's why the example succeeds.

## Type class inference -- the basics. ##

All the material in this section is covered in Theorem Proving In Lean.

If `G` is a type, then `add_group G` is a structure. Informally, a term of type `add_group G` is an additive group structure on `G`. To make a term of this type you will ultimately end up running the constructor for this structure, and the constructor is a function which demands as input an addition map `G → G → G`, a negation map `G → G`, a zero term of type `G`, and a proof of each of the group axioms for an additive group.

If you're making your own additive group, then of course you're going to have to make these maps and prove these theorems about them yourself somehow. But what about a completely standard type such as the integers? Addition and negation and zero and all the axioms will have already been done for you. How do we get to those definitions, especially if we are a beginner and don't know our way around the Lean library files?

Here's the trick. `add_group G` is more than a structure -- it is a *class*; we can check this using Lean's `#print` command:

```lean
#print add_group
/-
@[class, priority 100]
structure add_group : Type u → Type u
fields:
add_group.add : Π {α : Type u} [c : add_group α], α → α → α
...
-/
```

We see that `add_group` has been tagged with the `class` attribute. This means that a certain part of Lean's C++ code, the type class inference system, comes into play. At some point in core Lean (in `init/data/int/basic.lean` in fact), Lean defines addition, negation and zero on the integers, and then proves all the axioms for an additive group. At this point we can hence make a term of type `add_group ℤ`. It would however be a mistake to define this term using the standard `def` command:

```lean
def int.add_group : add_group ℤ := ... -- bad!
```

Defining it this way would make it hard for users to find. The way to do it would be to use a modification of `def` used specially for classes, called `instance`.

```lean
instance int.add_group : add_group ℤ := ... -- good!
```

Just like a class is just a structure tagged with the `[class]` attribute, an instance is nothing more than a definition tagged with the `[instance]` attribute.

When Lean sees `assoc_assoc x` above and it knows that `x` is an integer, it sees the square brackets around `[add_group G]`, notes that `add_group` has been tagged with `[class]`, and then says to the type class inference system something like "please can you look through all the definitions tagged with `[instance]` and see if you can find or make one of type `add_group ℤ`?" If the type class inference system can find a term of type `add_group ℤ`, it returns it, and Lean uses this term as the missing input to the `assoc_assoc` function.

It is possible to actually make this query directly to Lean, like this:

```lean
def ABC : add_group ℤ := by apply_instance -- no errors
```

Now the term `ABC` has type `add_group ℤ` -- the type class inference machine found a term of this type and returned it. It is the fact that Lean can magically generate terms like this, that makes the whole type class inference system work. Note that we don't need to make `ABC` an instance this time around -- the instance is already in Lean's system. We only use the `instance` command when we're adding new instances to the system, not when we're getting old ones out.

If the type class inference system cannot find a term of the type we're looking for then we get an error. For example the natural numbers are not an additive group, so even though addition on the natural numbers is associative, our `assoc_assoc` function (which asks for an additive group structure on G) should fail.

```lean
def assoc_assoc {G : Type} [add_group G] (g : G) : g + (g + (g + g)) = ((g + g) + g) + g :=
begin
  rw add_assoc,
  rw add_assoc
end

def y := (5 : ℕ)

example : y + (y + (y + y)) = ((y + y) + y) + y := assoc_assoc y
/-
failed to synthesize type class instance for
⊢ add_group ℕ
-/
```
The error means that the type class inference system tried to find a term of type `add_group ℕ` in its database, but failed. This failure is unsurprising -- the addition on the natural numbers does not give it a group structure, as additive inverses do not in general exist. If we wanted to prove this example using `assoc_assoc` we should weaken our demands -- we should only demand that `G` is an additive semigroup; an additive semigroup doesn't have additive inverses but it does have associativity of addition, and the natural numbers are an example. Here is a version of assoc_assoc which works for natural numbers. We have shortened the proof just to add some variety, but the key change is that `[add_group G]` has become `[add_semigroup G]`. 

```lean
example: add_semigroup ℕ := by apply_instance -- works!

def assoc_assoc {G : Type} [add_semigroup G] (g : G) : g + (g + (g + g)) = ((g + g) + g) + g :=
by repeat {rw add_assoc}

variable (y : ℕ)

example : y + (y + (y + y)) = ((y + y) + y) + y := assoc_assoc y
```

## How does type class inference work?

The naive model for type class inference is that all the instances you need are definitions which are tagged with the `instance` tag. But this simplistic model cannot be how things work. For example `ℤ^n` is an additive group for all natural numbers `n`, and this works:

```lean
example: add_group 
Not just instances.

Example of maps from field to group, or group structure on product.

Only one instance.

TODO -- add search -- explain how to put the trace on.

Dig out chat from Bristol.

Understand Patrick's wrapper stuff.

https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/how.20does.20type.20class.20inference.20work.3F
*******************************************************************

TPIL says it's a dreaded prolog-like search

Lean 

