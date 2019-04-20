# Typeclass inference #

### Summary ###

This document is about the `[ ]` "square bracket" notation that is often seen in Lean code, for example `[group G]`, which turns a type `G` into a group. We'll start by briefly explaining the difference between `[ ]` brackets, `( )` brackets and `{ }` brackets. We'll then go on to talk a little about how the type class inference system (that is, the system which handles all the terms in square brackets) works. We'll see how the type class inference system can cleverly fill in some of these square bracket terms for you, we'll see limits with what it can do, how to use it and how not to use it.

## Introduction ##

Here is an overview of the bracket system in Lean, concentrating mostly on the square brackets `[ ]`. Everything here is covered in Theorem Proving In Lean, although the write-up here is more geared towards mathematicians.

When writing a function, if you want to say precisely which type every input term has, you will need brackets. For example

```lean
def double (n : ℕ) := n + n
```

Round brackets `( )` are easiest to understand; these are arguments which Lean expects you to supply. For example

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
```

The function `mem_inter` takes six inputs: a type `X`, two subsets `U` and `V` of `X`, a term `x` of type `X`, and proofs `hU` and `hV` that ` x ∈ U`  and `x ∈ V` respectively. But the first four of these inputs are in squiggly brackets `{ }`, which means that the person who defined this function is saying "Go on Lean, take a look at what the user inputs when you ask for `hU` and `hV`, and then figure out all the other inputs yourself". And indeed one can see that this should be possible; if `B` and `C` are subsets of the natural numbers (that is, terms of type `set ℕ`), and the user inputs proofs that `3 ∈ B` and `3 ∈ C` to this function, then Lean can figure out that `x` must be `3`, `U` must be `B`, `V` must be `C` and `X` must be `ℕ`. This process is called `type unification` and it is what you are asking Lean to do if you use `{ }` squiggly brackets.

But how about this?

```lean
def assoc_assoc {G : Type} [add_group G] (g : G) : g + (g + (g + g)) = ((g + g) + g) + g :=
begin
  rw add_assoc,
  rw add_assoc
end

def x := (4 : ℤ)

example : x + (x + (x + x)) = ((x + x) + x) + x := assoc_assoc x
```

There are three inputs to `assoc_assoc` -- a type `G`, a term of type `group G` (that is, the definitions of the multiplication, inverse and identity in `G` and the proofs that they satisfy the axioms of a group), and a term `g` of type `G`. The user is asked for `g`, Lean can now guess `G` using type unification -- but how can Lean guess the group structure on `G` just by thinking about the types of everything? It can't. When faced with the term `assoc_assoc x`, Lean can figure out that `x` must be `4` and `G` must be `ℤ` -- but how can it figure out the additive group structure on `ℤ`? Lean needs to come up with an addition function `ℤ → ℤ → ℤ` for example -- it knows the type, but how does it figure out the term?

The answer is that it "looks it up in a big table". In other words, it uses type class inference.

## Type class inference -- the basics. ##

All the material in this section is covered in Theorem Proving In Lean.

If `G` is a type, then `add_group G` is a structure -- it's the structure of groups with group law `+`. To make a term of this structure you will ultimately end up running the constructor for this structure, and the constructor is a function which demands as input an addition map `G → G → G`, a negation map `G → G`, a zero term of type `G`, and a proof of each of the group axioms for an additive group. However `add_group G` is more than a structure -- it is a *class*; we can check this using Lean's `#print` command:

```lean
#print add_group
/-
@[class, priority 100]
structure add_group : Type u → Type u
fields:
add_group.add : Π {α : Type u} [c : add_group α], α → α → α
...
-/

We see that `add_group` has been tagged with the `class` attribute. This means that a certain part of Lean's C++ code, the type class inference system, comes into play. At some point in core Lean (in `init/data/int/basic.lean` in fact), Lean defines addition, negation and zero on the integers, and then proves all the axioms for an additive group. We can hence make a term of type `add_group ℤ`. It would however be a mistake to define this term using the standard `def` command:

```lean
def int.add_group : add_group ℤ := ... -- bad!
```

The way to do it would be to use a modification of `def` used specially for classes, called `instance`.

```lean
instance int.add_group : add_group ℤ := ... -- good!
```

Just like a class is just a structure tagged with the `[class]` tag, an instance is just a definition tagged with the `[instance]` tag.

When Lean sees `assoc_assoc x` above and it knows that `x` is an integer, it sees the square brackets around `[add_group G]`, notes that `add_group` has been tagged with `[class]`, and then says to the type class inference system something like "please can you look through all the definitions tagged with `[instance]` and see if you can find one of type `add_group ℤ`?" If the type class inference system can find a term of type `add_group ℤ`, it returns it, and Lean uses this term as the missing input to the `assoc_assoc` function.

It is possible to actually make this query directly to Lean, like this:

```lean
def ABC : add_group ℤ := by apply_instance -- no errors
```

Now the term `ABC` has type `add_group ℤ` -- the type class inference machine found a term of this type and returned it. It is the fact that Lean can magically generate terms like this, that makes the whole type class inference system work.

If the type class inference system cannot find a term of the type we're looking for then we get an error. For example the natural numbers are not an additive group, so even though addition on the natural numbers is associative, our `assoc_assoc` function (which asks for an additive group structure) should fail.

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
The error means that the type class inference system tried to find a term of type `add_group ℕ` in its database, but failed. This failure is unsurprising -- the addition on the natural numbers does not give it a group structure, as additive inverses do not in general exist. If we wanted to prove this example using `assoc_assoc` we should weaken our demands -- we should only demand that `G` is an additive semigroup; a semigroup doesn't have inverses but it does have associativity, and the natural numbers are an example. Here is a version of assoc_assoc which works for natural numbers:

```lean
example: add_semigroup ℕ := by apply_instance -- works!

def assoc_assoc {G : Type} [add_semigroup G] (g : G) : g + (g + (g + g)) = ((g + g) + g) + g :=
by repeat {rw add_assoc}

variable (y : ℕ)

example : y + (y + (y + y)) = ((y + y) + y) + y := assoc_assoc y
```

## How does type class inference work?##

Not just instances.

Example of maps from field to group, or group structure on product.

Only one instance.

TODO -- add search -- explain how to put the trace on.

Dig out chat from Bristol.

Understand Patrick's wrapper stuff.

https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/how.20does.20type.20class.20inference.20work.3F
*******************************************************************

Lean 



To define functions and proofs recursively you can use the equation compiler, if you have a well founded relation on that type

For example the definition of gcd on naturals uses well founded recursion

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)
```

Because < is a well founded relation on naturals, and because `y % succ x < succ x` this recursive function is well_founded.

Whenever you use the equation compiler there will be a default well founded relation on the type being recursed on and the equation compiler will automatically attempt to prove the function is well founded.

If the equation compiler fails, there are two main reasons for this. The first is that it has failed to prove the required inequality. The second is that it is not using the correct well founded relation.

### Proving required inequality ###

If we modify the gcd example above, by removing the `have`, we get an error.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := gcd (y % succ x) (succ x)
```
```
failed to prove recursive application is decreasing, well founded relation
  @has_well_founded.r (Σ' (a : ℕ), ℕ)
    (@psigma.has_well_founded ℕ (λ (a : ℕ), ℕ) (@has_well_founded_of_has_sizeof ℕ nat.has_sizeof)
       (λ (a : ℕ), @has_well_founded_of_has_sizeof ℕ nat.has_sizeof))
Possible solutions:
  - Use 'using_well_founded' keyword in the end of your definition to specify tactics for synthesizing well founded relations and decreasing proofs.
  - The default decreasing tactic uses the 'assumption' tactic, thus hints (aka local proofs) can be provided using 'have'-expressions.
The nested exception contains the failure state for the decreasing tactic.
nested exception message:
failed
state:
gcd : (Σ' (a : ℕ), ℕ) → ℕ,
x y : ℕ
⊢ y % succ x < succ x
```

The error message has given us a goal, `y % succ x < succ x`. Including a proof of this goal as part of our definition using `have` removes the error.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)
```

Note that the `have` must not be in tactics mode, i.e. inside any `begin` `end`. If you are in tactics mode, there is the option of putting the `have` statement inside the exact statement, as in the following example.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y :=
begin
  exact have y % succ x < succ x := mod_lt _ (succ_pos _),
  gcd (y % succ x) (succ x)
end
```

### order of arguments ###

Sometimes the default relation the equation compiler uses is not the correct one. For example swapping the order of x and y in the above example causes a failure

```lean
def gcd : nat → nat → nat
| y 0        := y
| y (succ x) := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (succ x) (y % succ x)
```

Now the error message is asking us to prove `succ x < y`. This is because by default the equation compiler tries to recurse on the first argument. More precisely, the relation that the equation compiler tries to use in this example is on the type of pairs of natural numbers `Σ' (a : ℕ), ℕ`, and it uses a lexicographical relation where the pair `⟨a, b⟩ ≺ ⟨c, d⟩` iff `a < c ∨ (a = c ∧ b < d)` This situation can be resolved, either by changing the order of the arguments or by specifying a `rel_tac` as decribed later in this doc.

Sometimes moving an argument outside of the equation compiler, can help the equation compiler prove a recursion is well_founded. For example the following proof from `data.nat.prime` fails.

```lean
lemma prod_factors : ∀ (n), 0 < n → list.prod (factors n) = n
| 0       h := (lt_irrefl _).elim h
| 1       h := rfl
| n@(k+2) h :=
  let m := min_fac n in have n / m < n := factors_lemma,
  show list.prod (m :: factors (n / m)) = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [list.prod_cons, prod_factors _ h₁, nat.mul_div_cancel' (min_fac_dvd _)]
```

But moving the `h` into a lambda after the `:=` makes it work

```lean
lemma prod_factors : ∀ (n), 0 < n → list.prod (factors n) = n
| 0       := λ h, (lt_irrefl _).elim h
| 1       := λ h, rfl
| n@(k+2) := λ h,
  let m := min_fac n in have n / m < n := factors_lemma,
  show list.prod (m :: factors (n / m)) = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [list.prod_cons, prod_factors _ h₁, nat.mul_div_cancel' (min_fac_dvd _)]
```

This is because for some reason, in the first example, the equation compiler tries to use the always false relation.

Conjecture : this is because the type of `h` depends on `n` and the equation compiler can only synthesize useful relations on non dependent products

### using_well_founded rel_tac ###

Sometimes you need to change the well founded relation to prove that a recursion is well founded. To do this you need a `has_well_founded` instance. This is a structure with two fields, a relation and a proof that this relation is well founded. The easiest way to define a well founded relation is using a function to the natural numbers. For example on multisets the relation `λ s t, card s < card t` is a well founded relation.

The following proof in `data.multiset` uses this relation.

```lean
@[elab_as_eliminator] lemma strong_induction_on {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s
| s := λ ih, ih s $ λ t h,
  have card t < card s, from card_lt_of_lt h,
  strong_induction_on t ih
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}
```

The final line tells the equation compiler to use this relation. It is not necessary to fully understand the final line to be able to use well_founded tactics. The most important part is `⟨_, measure_wf card⟩` This is the well_founded instance. `measure_wf` is a proof that any relation generated from a function to the natural numbers, i.e. for a function `f : α → ℕ`, the relation `λ x y, f x < f y`. The underscore is a placeholder for the relation, as it can be inferred from the type of the proof. Note that the well founded relation must be on a `psigma` type corresponding to the product of the types of the arguments after the vertical bar, if there are multiple arguments after the vertical bar.

In the gcd example the `psigma` type is `Σ' (a : ℕ), ℕ`. In order to solve the problem in the example where the order of the arguments was flipped, you could define a well founded relation on `Σ' (a : ℕ), ℕ` using the function `psigma.snd`, the function giving the second element of the pair, and then the error disappears.

```lean
def gcd : nat → nat → nat
| y 0        := y
| y (succ x) := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (succ x) (y % succ x)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩]}
```
