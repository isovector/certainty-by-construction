# Decidability {#sec:decidability}


Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Integer using (ℤ)
open import Chapter1-Agda using () renaming (_,_ to _,⅋_; _×_ to _×⅋_)
    ```


```agda
module Chapter6-Decidability where
```


Prerequisites

:   ```agda
open import Chapter1-Agda
  using (Bool; true; false)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)
    ```

:   ```agda
open import Chapter3-Proofs
  using (_≡_; module PropEq; module ≡-Reasoning; suc-injective)
open PropEq
    ```

:   ```agda
open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ; _,_)
    ```


In the last chapter, we thoroughly investigated the notion of doing proof work
in Agda. We gave a propositional definition what it means for two things to be
equal, derived relevant properties of equality, built a domain-specific language
for doing equational reasoning, and proved many facts about the algebra of the
natural numbers.

Perhaps now we can smugly think that we know all there is to know about
proofs---but this is patently false. For example, we haven't the notion of
falseness itself! Furthermore, everything we've built so far works only for
*statically-known* values. But is it possible that we can use dependent types in
contexts where we don't know all the values we need to work with? Maybe the
values came from the user via an interactive system. Are we forced to throw away
everything we've done and degrade our guarantees to those of a weaker
programming language?

Thankfully the answer to all of these is "no," and we will explore each in this
chapter. Additionally, we will also get our hands dirty modeling and proving
facts about more computer-sciencey objects. After all, these proof techniques
are applicable outside of the ivory tower, too!


## Negation {#sec:negation}

Recall that we've now seen how to express that two values are (propositionally)
equal, via the `type:_≡_` type, proven via `ctor:refl`. We'd now like to work
out a means of discussing *inequality!*


Hidden

:   ```agda
-- fix bind
    ```


Perhaps you might think we can make a slight tweak to the `type:_≡_`
construction. While `ctor:refl` `:` `bind:x:x ≡ x`, perhaps we could define
`def:_≢_` (input as [`==n`](AgdaMode)) as something like:

```agda
module Sandbox-Inequality where
  data _≢_ {A : Set} : A → A → Set where
    ineq : {x y : A} → x ≢ y
```

Unfortunately, this approach does not---and cannot---work. While we've attempted
to assert that `x` and `y` are inequal by virtue of being different bindings of
`A`, Agda gives us no guarantees that they are *distinct* values of `A`! It's
as if were to write a function:

```agda
  f : ℕ → ℕ → ℕ
  f x y = x + y
```

Here, `x` and `y` are different *variables,* but that doesn't mean they must
have different *values.* We can happily evaluate this at `expr:f 2 2`. Thus,
just because the variables are distinct doesn't mean the values must be. This
attempt at modeling `def:_≢_` is therefore fundamentally flawed. Let's try
something else.

Recall the *principle of explosion,* the property of a contradictory system,
which states that "from false, anything is possible." This gives us a hint as to
how we might go about encoding an inequality. Rather than treating it as such,
we can instead rewrite $x \neq y$ as "$x = y$ is false."

Let's try our hand at this principle of explosion. The idea being, in order to
show that some claim `P` is false, we instead encode the problem as "from a
proof of `P` we can derive anything else."

```agda
module Sandbox-Explosion where
  _IsFalse : Set → Set₁  -- ! 1
  P IsFalse = P → {A : Set} → A
```

You'll notice at [1](Ann) that the type of `type:_IsFalse` is `expr:Set → Set₁`,
which is our first time seeing a `type:Level` in the wild. Such is necessary
because the definition of `type:_IsFalse` expands out to a
polymorphically-quantified `A :` `type:Set`. Whenever we have a `type:Set`
parameter, the defining object itself must live in `type:Set₁`.

From here, We can now try to find a proof that two is not equal to three, as
per:

```agda
  2≢3⅋₀ : (2 ≡ 3) IsFalse
  2≢3⅋₀ = ?
```

Since `type:_IsFalse` expands to a function type, we can (rather unintuitively)
do a [MakeCase:](AgdaCmd) here to get a *parameter* of type `expr:2 ≡ 3`:

```agda
  2≢3⅋₁ : (2 ≡ 3) IsFalse
  2≢3⅋₁ x = {! !}
```

Of course, you and I know that there is no such proof that `expr:2 ≡ 3`.
Nevertheless, we can ask Agda to [MakeCase:x](AgdaCmd) here, which will produce
a strange result:

```agda
  2≢3 : (2 ≡ 3) IsFalse
  2≢3 ()
```

What happened is that Agda noticed that *there are no constructors* for the type
`expr:2 ≡ 3`. Therefore, this function `def:2≢3` can never be called, since
there is argument that will typecheck. Since Agda notices that the whole thing
is moot anyway, we aren't required to write any implementation, which explains
the funny `()` notation, also known as an *absurd pattern match.* Absurd pattern
matches don't require an definition, and we illustrate that by not giving any
equals sign.

By virtue of having written a definition of `def:2≢3` that typechecks, we have
successfully proven the fact that two is not equal to three. Mission
accomplished! Nevertheless, while this is an absolutely valid encoding and
serves to illustrate the idea, it's not quite how we usually write negation in
Agda. For that, we need the bottom type.


## Bottom {#sec:bottom}

While it's acceptable to use the principle of explosion directly, there is a
simpler way of encoding the problem, namely by "factoring out" the pieces.

Rather than showing all contradictions lead to explosion, we can instead say all
contradictions lead to a specific type, and then show that all values of that
type lead to explosion. The resulting machinery means you can always use the
principle of explosion if you'd like, but in practice allows for simpler-to-use
types when doing negative proofs.

This "pre-explosive" type we'll work with is called the *bottom* type, written
`type:⊥` and input as [`bot`](AgdaMode). Its definition is short and sweet:

```agda
module Definition-Bottom where
  data ⊥ : Set where
```

That's it. There are no constructors for `type:⊥`, meaning that *every* pattern
match on `type:⊥` must be absurd as we saw in the last section. Besides a
slightly different type signature, we can show `def:2≢3` again---with an
identical proof, but this time using bottom:

```agda
  2≢3 : 2 ≡ 3 → ⊥
  2≢3 ()
```

Why does this work? Recall the definition of a function: for any input in the
domain, it must return an element in the codomain. But there are no elements in
bottom, so any function whose codomain is bottom cannot possibly be a
function---as it has nowhere to send inputs! The only possible workaround here
is if the function's domain *also* has no elements.

By this argument, any function we can successfully define which maps into bottom
necessarily constrains at least one of its parameters to also have no elements.

We still need to show that an element of `type:⊥` leads to the principle of
explosion. This function is called bottom elimination," and is itself another
easy proof:

```agda
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()
```

Mathematically, proofs of this flavor are called *vacuously true.* Which is to
say, they are true only because they presuppose a contradiction. From another
perspective, vacuously true proofs have already "baked in" the principle of
explosion.

Nevertheless, we can give a vacuous proof that all elements of bottom---of which
there are none---are equal, or, at least, that they would be equal if there were
any:

```agda
  ⊥-unique : {x y : ⊥} → x ≡ y
  ⊥-unique {x} = ⊥-elim x
```

We have now shown that bottom is a satisfactory definition of false, and that
functions into bottom are therefore proofs that at least one of their parameters
is a contradiction. Hence, we can define `type:¬_` ([`neg`](AgdaMode)), which
states that a given mathematical statement is false:

```agda
  ¬_ : {ℓ : Level} → Set ℓ → Set ℓ
  ¬ P = P → ⊥
  infix 3 ¬_
```

In this definition of `type:¬_`, we have used universe polymorphism in order to
give negation for every possible `type:Level`, simultaneously. This is a common
pattern in Agda---to make each and every `type:Set` you bind
universe-polymorphic.


## Inequality

With a satisfactory definition for propositional negation, we can
define inequality (input as [`neq`](AgdaMode)):


```agda
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = ¬ x ≡ y
  infix 4 _≢_
```

When defining new relations, it's always a reward experience to investigate
which properties hold of the new construction. As you might expect, inequality
is symmetric:

```agda
  ≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
  ≢-sym x≢y y=x = x≢y (sym y=x)
```

and it is *not* reflexive. Perhaps this is obvious to you, but if not, recall
that reflexivity would require us to show `bind:x:x ≢ x` for any `x`, which is
exactly the *opposite* of what we're trying to encode here.

Interestingly however, we *can* prove that `type:_≢_` isn't reflexive by showing
that if there were construction, it would lead immediately to contradiction.
Let's show this in a few steps. First, we will define a type `type:Reflexive`
which will state the reflexivity property. This isn't strictly necessary, but it
lessens the cognitive burden later down the line.

A relation `_≈_ :` `bind:ℓ A:A → A → Set ℓ` is *reflexive* if, for any `x : A`,
we can construct `x ≈ x`. This definition can be encoded as a type:

```agda
  Reflexive
      : {c ℓ : Level} {A : Set c}
      → (A → A → Set ℓ)
      → Set (ℓ ⊔ c)
  Reflexive {A = A} _≈_ = {x : A} → x ≈ x -- ! 1
```

Having a value of `type:Reflexive` `_≈_` states that `_≈_` is just such a
reflexive relation. Note that, at [1](Ann), `_≈_` is on the left side of the
equals sign, and is thus just a parameter---allowing us to state *which*
relation is reflexive.

To illustrate exactly what's happening here, we can show that propositional
equality is reflexive:

```agda
  ≡-refl : {A : Set} → Reflexive {A = A} _≡_
  ≡-refl = refl
```

Notice how the type `expr:Reflexive _≡_` expands to the type of `ctor:refl`,
that is, `bind:A:{x : A} → x ≡ x`. We are required to explicitly bind `A :`
`type:Set` here, so that we can use it to fill in the implicit `A` parameter of
`type:Reflexive`. In principle, Agda could be inferred from the type of
`type:_≡_`, but Agda has know way of knowing if we'd like to talk about
`type:_≡_` in its fully-polymorphic type, or if we'd like it specialized to
some particular type like `type:ℕ`. The distinction isn't extremely poignant in
this example, but there do exist monomorphic relations which we might still want
to say are reflexive.

Nevertheless, we have shown that `type:_≡_` is reflexive by giving a proof that
`ctor:refl` always exists.

Contrasting against this example the proof that `type:_≢_` is *not* reflexive.
The type of such a statement is a very subtle thing:

```agda
  ¬≢-refl⅋₀ : ¬ ({A : Set} → Reflexive {A = A} _≢_)  -- ! 1
  ¬≢-refl⅋₀ = ?
```

Compare this type to the more "obvious" type:

```agda
  ¬≢-refl-bad⅋₀ : {A : Set} → ¬ Reflexive {A = A} _≢_  -- ! 2
  ¬≢-refl-bad⅋₀ = ?
```

The difference between [1](Ann) and [2](Ann) is in the placement of the binder
for `A :` `type:Set`. In the latter type, in the latter, we receive a
specific `A`, and are then required to give back a proof that there is no
`def:≢-refl` *for that specific type.* Contrast that against [1](Ann), in which
we are required to show that there does not exist a `def:≢-refl` that works for
*every* type `A`.

End users of `def:¬≢-refl` don't care one way or another, since they only ever
need one type at a time (or can use a variable if they'd like to show this for
many types.) Nevertheless, the difference here is absolutely crucial when we'd
actually like to *prove* the thing. Let's look at this more closely.

At a very high level, the proof here is "`def:≢-refl` must be false because it's
the negation of `def:≡-refl`, which is easily shown to be true." While the type
of the argument to `def:¬≢-refl` is `type:Reflexive _≢_`, we can use
[TypeContext/Normalise](AgdaCmd) to ask Agda to expand out this definition,
resulting in:

```info
x ≡ x → ⊥
```

Under the lens of this expanded type, it seems reasonable to call the argument
to our function `¬≡-refl`, as in the following:

```agda
  ¬≢-refl⅋₁ : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl⅋₁ ¬≡-refl = {! !}
```

Of course, we do in fact have a proof of `bind:x:x ≡ x`, namely `ctor:refl`, so
we can try solving the hole as:

```agda
  ¬≢-refl⅋₂ : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl⅋₂ ¬≡-refl = ¬≡-refl refl
```

Uh oh, something went wrong. This yellow background means that elaboration
failed, which means that Agda was unable to determine some of the implicit
arguments. We can help it out by explicitly introducing holes for each implicit
argument and solving them ourselves:

```agda
  ¬≢-refl⅋₃ : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl⅋₃ ¬≡-refl = ¬≡-refl {?} {?} refl
```

You'll notice that the yellow warning has disappeared, and we're left only with
some holes to fill. The first hole has type `type:Set`, while the second has type
`?0`, meaning its type depends on the answer to our first hole. We're free to
choose any type we'd like for this first hole, so let's try `type:ℕ`:

```agda
  ¬≢-refl⅋₄ : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl⅋₄ ¬≡-refl = ¬≡-refl {ℕ} {?} refl
```

This refines our other hole to have type `type:ℕ`, and now all we need is to
pick an arbitrary natural:

```agda
  ¬≢-refl : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl ≢-refl = ≢-refl {ℕ} {0} refl
```

What was to be demonstrated has thus been proved. But how? We've shown that
there can be no proof of `expr:Reflexive _≢_` for *every type* `A`, because if
there were such a proof, we could instantiate it at the naturals, and use it to
prove that `expr:0 ≢ 0`. Such is obviously bunk, because we can refute `expr:0 ≢
0`, and therefore the argument rests on false premises.

Let's see what goes wrong if we try the same approach on `def:¬≢-refl-bad`.
Since `A` is now a top-level parameter, we can bind it in the function body,
meaning we have one fewer implicit to fill in:

```agda
  ¬≢-refl-bad : {A : Set} → ¬ Reflexive {A = A} _≢_
  ¬≢-refl-bad {A} ¬≡-refl = ¬≡-refl {?} refl
```

But we run into problems trying to fill this last hole. It unfortunately has
type `A`, *for some unknown type `A`!* We can't possibly fill this in, because
we don't know what type `A` is. In fact, `A` could be `type:⊥`, in which case
there aren't even any values we *could* put here.

The takeaway from this argument is the importance of where you put your
quantifiers. When the necessary parameters are *inside* the negation, we are
able to instantiate them at our convenience when looking for a counterexample.
But if they are outside the negation, we are at the mercy of the proof-caller.
Such might dramatically change how we'd go about showing a counterexample, and
often precludes it entirely.


## Negation Considered as a Callback

There is an apt computational perspective to this problem of negating
quantifiers, which exposes itself when we expand all the definitions. After
fully normalizing the types of both `def:¬≢-refl` and `def:¬≢-refl-bad`, we
are left with these:

```agda
  ¬≢-refl⅋⅋      : ({A : Set} → {x : A} → x ≡ x → ⊥) → ⊥
  ¬≢-refl-bad⅋⅋  : {A : Set} → ({x : A} → x ≡ x → ⊥) → ⊥
```


Hidden

:   ```agda
  ¬≢-refl⅋⅋  = _
  ¬≢-refl-bad⅋⅋ = _
    ```

The salient feature of these two types is that they both take functions as
arguments. Whenever you see a function as an argument, you can interpret this
argument as a *callback.* Viewed as such, the question becomes *who is
responsible for providing what?* In the first case, it is the *implementer* of
`def:¬≢-refl` who gets to pick `A`, while in the second, the *caller* of
`def:¬≢-refl-bad` is responsible. And true to the name of this function, the
caller might very well pick an antagonistic `A` in an attempt to thwart us!


## Intransitivity of Inequality

In the same vein as `def:¬≢-refl`, we can also show that `type:_≢_` doesn't satisfy
transitivity. The pen and paper proof is straightforward, since if inequality
were transitive we could show:

$$
\begin{aligned}
2 &\neq 3 \\
&\neq 2
\end{aligned}
$$

This is known in the business as a "whoopsie daisy." Such a counterexample shows
inequality cannot be transitive, because if it were, we could show reflexivity,
which we already know is false. We can prove the non-transitivity of inequality
more formally in Agda by giving a definition for transitivity:

```agda
  Transitive
      : {c ℓ : Level} {A : Set c}
      → (A → A → Set ℓ)
      → Set (c ⊔ ℓ)
  Transitive {A = A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z
```

Spend a moment to parse and understand this type for yourself. Do you agree that
this corresponds to the definition of transitivity (@sec:transitivity)?

Showing the counterexample is easy---following our exact pen and paper proof
above---since we already have a proof `def:2≢3`. Given a hypothetical
`def:≢-trans`, we could combine this with `expr:sym 2≢3`, to get a proof that
`expr:2 ≢ 2`. Such a thing is in direct contradiction with `ctor:refl` `:`
`expr:2 ≡ 2`, which acts as the refutation:

```agda
  ¬≢-trans : ¬ ({A : Set} → Transitive {A = A} _≢_)
  ¬≢-trans ≢-trans = ≢-trans {ℕ} 2≢3 (≢-sym 2≢3) refl
```


## No Monus Left-Identity Exists {#sec:no-monus-id}

To illustrate using negation in the real world, let's prove a claim made back in
@sec:identities: that there is no left-identity for the monus operation
`def:_∸_`. First, let's import it.


Hidden

:   ```agda
open import Data.Empty
  using (⊥)
    ```

:   ```agda
open import Relation.Binary.PropositionalEquality
  using (_≢_)
    ```


```agda
open import Relation.Nullary
  using (¬_)

module Example-NoMonusLeftIdentity where
  open Chapter2-Numbers using (_∸_)
```

In order to prove this, let's first think about what we'd like to say, and what
the actual argument is. We'd like to say: "it is not the case that there exists
a number `e :` `type:ℕ` such that for any `x :` `ℕ` it is the case that `bind:x
e:e ∸ x ≡ x`." A bit of a mouthful certainly, but it encodes rather directly.
Replace "there exists a number `e :` `type:ℕ` such that" with `expr:Σ ℕ (λ e →
?)`---recalling `type:Σ` from @sec:sigma. After replacing the "for any `x :`
`type:ℕ`" with `expr:(x : ℕ) → ?`, we're ready to go:

```agda
  ¬∸-identityˡ⅋₀ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x)
  ¬∸-identityˡ⅋₀ = ?
```

Proving this is straightforward; we take the refutation at its word, and
therefore get a function `e-is-id :` `bind:e:(x : ℕ) → e ∸ x ≡ x`. If we
instantiate this function at $x = 0$, it evaluates to a proof that `bind:e:e ≡ 0`.
Fair enough. But we can now instantiate the same function at $x = 1$, which then
produces a proof that `bind:e:e ∸ 1 ≡ 1`. However, we already know that $e = 0$,
so we can replace it, getting `expr:0 ∸ 1 ≡ 1`, which itself simplifies down to
 `expr:0 ≡ 1`. Such is an obvious contradiction, and therefore there is no such
identity for monus.

We can write the same argument in Agda by binding and splitting our argument,
and then using a `keyword:with`-abstraction (@sec:maybe) on `e-is-id` at both 0
and 1:

```agda
  ¬∸-identityˡ⅋₁ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x)
  ¬∸-identityˡ⅋₁ (e , e-is-id)
    with e-is-id 0 | e-is-id 1
  ... | e≡0 | e-1≡1 = ?
```

If we now pattern match ([MakeCase](AgdaCmd)) on `e≡0` and `e-1≡1` *in that
order*, Agda will follow the same line of reasoning as we did, and determine
that the second pattern match is necessarily absurd:

```agda
  ¬∸-identityˡ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x)
  ¬∸-identityˡ (e , e-is-id)
    with e-is-id 0 | e-is-id 1
  ... | refl | ()
```


## Decidability

It is now time to return to the question of how does one use dependent types in
the "real world." That is, the proofs we've seen so far work fine and dandy when
everything is known statically, but things begin to fall apart when you want to
get input from a user, read from a file, or do anything of a dynamic nature.
What can we do when we don't have all of our necessary information known at
compile time?

The answer is unsurprising: just compute it!

Recall that every concrete proof we've given is represented by a value. That
means it has a representation in memory, and therefore, that it's the sort of
thing we can build at runtime. The types obscure the techniques that you already
know how to do from a career of computing things with elbow grease, but
everything you know still works.

In a language with a less powerful system, how do you check if the number the
user input is less than five? You just do a runtime check to see if it's less
than five before going on. We can do exactly the same thing in Agda, except
that we'd like to return a *proof* that our number is equal to five, rather than
just a boolean. As a first attempt, you can imagine we could implement such a
thing like this:

```agda
module Sandbox-Decidability where
  open Chapter2-Numbers
    using (Maybe; just; nothing)

  n=5? : (n : ℕ) → Maybe (n ≡ 5)
  n=5? 5 = just refl
  n=5? _ = nothing
```

Given `def:n=5?`, we can call this function and branch on its result. If the result
is a `ctor:just`, we now have a proof that `n` was indeed 5, and can use it
as we'd please. Of course, if the argument *wasn't* five, this definition
doesn't allow us to learn anything at all---all we get back is `ctor:nothing`!

Instead, it would be much more useful to get back a proof that `bind:n:¬ (n ≡ 5)`,
in case we'd like to do something with that information. From this little
argument, we conclude that returning `type:Maybe` isn't quite the right choice.
More preferable would be a type with slightly more structure, corresponding to a
*decision* about whether `bind:n:n ≡ 5`:

```agda
  data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where
    yes  :    P → Dec P
    no   : ¬  P → Dec P
```


Hidden

:     ```agda
  -- FIX
      ```


The type `bind:P:Dec P` state that either `P` definitely holds, or that it
definitely *doesn't* hold. Of course, only one of these can ever be true at
once, and thus `bind:P:Dec P` corresponds to an answer that we know one way or
the other.

As an anti-example, given two numbers, it's not too hard to determine if the two
are equal:

```agda
open import Relation.Nullary using (Dec; yes; no)

module Nat-Properties where
  _==_ : ℕ → ℕ → Bool
  zero   == zero   = true
  zero   == suc y  = false
  suc x  == zero   = false
  suc x  == suc y  = x == y
```

While `def:_==_` *is* a decision procedure, it doesn't give us back any
proof-relevant term. We'd like instead to get back a proof that the two numbers
were or were not equal. A better name for such a function is `def:_≟_` (input as
[`?=`](AgdaMode)).

```agda
  _≟⅋₋₁_ : (x y : ℕ) → Dec (x ≡ y)
  _≟⅋₋₁_ = ?
```

The goal is slightly modify the definition of `def:_≡_` such that whenever it
returns `ctor:true` we instead get back a `ctor:yes`, and likewise replace
`ctor:false` with `ctor:no`. Giving back the `ctor:yes`es is easy enough, but
the `ctor:no`s take a little more thought:

```agda
  _≟⅋₀_ : (x y : ℕ) → Dec (x ≡ y)
  zero   ≟⅋₀ zero   = yes refl
  zero   ≟⅋₀ suc y  = no ?
  suc x  ≟⅋₀ zero   = no ?
  suc x  ≟⅋₀ suc y with x ≟⅋₀ y
  ... | yes refl  = yes refl
  ... | no x≢y    = no ?
```

The first hole here has type `bind:y:zero ≡ suc y → ⊥`, which we can
[Refine](AgdaCmd) to a lambda:

```agda
  _≟⅋₁_ : (x y : ℕ) → Dec (x ≡ y)
  zero   ≟⅋₁ zero   = yes refl
  zero   ≟⅋₁ suc y  = no λ { x → {! !} }
  suc x  ≟⅋₁ zero   = no ?
  suc x  ≟⅋₁ suc y with x ≟⅋₁ y
  ... | yes refl  = yes refl
  ... | no x≢y    = no ?
```

Inside our lambda we have a term `x` whose type is `bind:y:zero ≡ suc y`. We
know this can never happen, since `ctor:zero` and `ctor:suc` are different
constructors. Therefore, we can solve this (and the next) hole with absurd
pattern matches inside of the lambda:

```agda
  _≟⅋₂_ : (x y : ℕ) → Dec (x ≡ y)
  zero   ≟⅋₂ zero   = yes refl
  zero   ≟⅋₂ suc y  = no λ ()
  suc x  ≟⅋₂ zero   = no λ ()
  suc x  ≟⅋₂ suc y with x ≟⅋₂ y
  ... | yes refl  = yes refl
  ... | no x≢y    = no ?
```

We are left with only one hole, but it has type `bind:x y:suc x ≡ suc y → ⊥`,
and thus our absurd pattern trick can't work here. However, we do have a proof
that `bind:x y:x ≢ y`, from which we must derive a contradiction. The idea is
that if refine our hole to a lambda, it will have a parameter of type `bind:x
y:suc x ≡ suc y`, which if we pattern match on, Agda will learn that `bind:x y:x
≡ y`. From there, we can invoke the fact that `bind:x y:x ≢ y`, and we have the
contradiction we've been looking for. It's a bit of a brain buster, but as
usual, the types lead the way:

```agda
  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero   ≟ zero   = yes refl
  zero   ≟ suc y  = no λ ()
  suc x  ≟ zero   = no λ ()
  suc x  ≟ suc y with x ≟ y
  ... | yes refl   = yes refl
  ... | no x≢y     = no λ { refl → x≢y refl }
```

Take a moment to reflect on this. Where before `def:_==_` simply returned
`ctor:false`, we are now responsible for *deriving a contradiction.*
Alternatively said, we must now *reify* our reasoning, and *prove* that our
algorithm does what it says. The advantage of returning a proof of the negation
is that downstream callers can use it to show their own impossible code-paths.

We can package up decidable equality into its own type:

```agda
  DecidableEquality : {ℓ : Level} (A : Set ℓ) → Set ℓ
  DecidableEquality A = (x y : A) → Dec (x ≡ y)
```

and give a more "semantically-inclined" type to our old function:


```agda
  _≟ℕ_ : DecidableEquality ℕ
  _≟ℕ_ = _≟_
```


## Transforming Decisions

-- TODO(sandy): write about me

```agda
  map-dec  : {ℓ₁ ℓ₂ : Level} {P : Set ℓ₁} {Q : Set ℓ₂}
          → (P → Q)  → (Q → P)
          → Dec P    → Dec Q
  map-dec to from (yes  p)   = yes  (to p)
  map-dec to from (no   ¬p)  = no   (λ q → ¬p (from q))
```


## Binary Trees {#sec:bintrees}

Perhaps you are tired of always working with numbers. After all, isn't this
supposed to be a book about applying mathematical techniques to computer
science? As it happens, all the techniques we have explored so far are
applicable to data structures just as much as they are to numbers and the
more mathematical purviews.

It is a matter of tradition to begin every exploration of data structures in
functional programming with lists. I'm personally exhausted of this tradition,
and suspect you are too. Therefore, we will instead touch upon the binary trees:
how to construct them, and how to prove things about them.

A binary tree is either `ctor:empty`, or it is a `ctor:branch`ing node
containing a value and two subtrees. We can codify this as follows:

```agda
open import Relation.Binary using (DecidableEquality)

module BinaryTrees where
  data BinTree {ℓ : Level} (A : Set ℓ) : Set ℓ where
    empty   : BinTree A
    branch  : BinTree A → A → BinTree A → BinTree A
```

To illustrate how this type works, we can build a binary tree as follows:

```agda
  tree : BinTree ℕ
  tree =
    branch
      (branch (branch empty 0 empty) 0 (branch empty 2 empty))
      4
      (branch empty 6 empty)
```

corresponding to this tree:


~~~~ {design=code/Languages/Tree.hs label="\AgdaFunction{tree}"}
asRose $ "4" [ "0" [ "0" ["", ""], "2" ["", ""]] , "6" ["", ""]]
~~~~

where the little points are each an instance of the `ctor:empty` constructor.


Hidden

:   ```agda
  -- fix bind
    ```


For convenience, it's often helpful to be able to talk about a single-element
tree, which we can encode as a `ctor:branch` with two `ctor:empty` children.
This is another good use-case for a `keyword:pattern` synonym. The following
defines a new pattern called `ctor:leaf` `:` `bind:A:A → BinTree A`:


```agda
  pattern leaf a = branch empty a empty
```

Having written `ctor:leaf`, we're now able to pattern match on singleton trees,
as in:

```agda
  is-singleton : {A : Set} → BinTree A → Bool
  is-singleton (leaf _)  = true
  is-singleton _         = false
```

In addition, we can use patterns as expressions, as in:

```agda
  five-tree : BinTree ℕ
  five-tree = leaf 5
```

It's now possible to write `def:tree` more succinctly:

```agda
  tree⅋ : BinTree ℕ
  tree⅋ =
    branch
      (branch (leaf 0) 0 (leaf 4))
      2
      (leaf 6)
```


## Proving Things about Binary Trees

With a suitable definition under our belt, it's time to suit up and enter the
proof mines. The first thing we might want to do with a binary tree is determine
whether it contains a particular element. Note that our `type:BinTree` type
doesn't necessarily represent binary *search* trees (BSTs.)

We can show an element is in a `type:BinTree` inductively by looking at three
cases:

1. the thing we're looking for is at the root of the tree, or
2. it's in the left subtree, or
3. it's in the right subtree.

Of course, in cases 2 and 3 we will work inductively, eventually finding a base
case 1. We can encode these three cases directly in the type `type:_∈_` (input
as [in](AgdaMode)):

```agda
  data _∈⅋_ {ℓ : Level} {A : Set ℓ} : A → BinTree A → Set ℓ where
    here   : {a : A}    {l r : BinTree A}           → a ∈⅋ branch l a r
    left   : {a b : A}  {l r : BinTree A} → a ∈⅋ l  → a ∈⅋ branch l b r
    right  : {a b : A}  {l r : BinTree A} → a ∈⅋ r  → a ∈⅋ branch l b r
```

This definition works perfectly well, but it's rather wordy. Notice that *over
half* of it is just bringing implicit bindings into scope. There's nothing wrong
with it, but it does somewhat obscure exactly what's going on.

This is a perfect use-case for Agda's `keyword:variable` block---already seen
above when we were discussing `type:Level`s---which allows us to define implicit
bindings that should exist for the remainder of the scope.

Variable blocks are started with the keywords `keyword:private variable`, and
then begin a new layout. We can create a few variables:

```agda
  private variable
    ℓ : Level
    A : Set ℓ
    a b : A
    l r : BinTree A
```

Variable bindings can depend on one another. Here we've introduced a
`type:Level` called `ℓ`, a type `A` of that level, two variables `a` and `b` of
that type, and two binary trees called `l` and `r`.

Having put these variables into scope, we can rewrite `type:_∈_` in a style that
better highlights the three cases:

```agda
  data _∈_ : A → BinTree A → Set where
    here   :          a ∈ branch l a r
    left   : a ∈ l →  a ∈ branch l b r
    right  : a ∈ r →  a ∈ branch l b r
```

Much, much tidier.

As a demonstration of the `type:_∈_` type, we can give a proof that 6 is indeed
in `def:tree`. Six is the root of the right-subtree, which makes our proof
delightfully declarative:

```agda
  6∈tree : 6 ∈ tree
  6∈tree = right here
```

As usual, see what happens if you give the wrong proof, or change 6 in the type.
Agda will correctly yell at you, indicating we've done the right thing here.


## Decidability of Tree Membership

We've given decidability proofs for equality; can we also give one for
`type:_∈_`? Certainly we can: given a decidable procedure for `A`, we can
just try it at every node in the tree and see what shakes out.

But before writing it, however, the following definitions will be useful to help
corral the types:

```agda
  Decidable  : {c ℓ : Level} {A : Set c}
             → (A → Set ℓ) → Set (c ⊔ ℓ)
  Decidable {A = A} P = (a : A) → Dec (P a)

  Decidable₂  : {c ℓ : Level} {A : Set c}
              → (A → A → Set ℓ) → Set (c ⊔ ℓ)
  Decidable₂ {A = A} _~_ = (x y : A) → Dec (x ~ y)
```


Footgun

:   Notice that we needed to give local definitions here for `ℓ` and `A`, rather
    than just use our `keyword:variable`s like before. This is a limitation in
    how Agda sorts out variables; written with `A` and `ℓ` bound to the
    `keyword:variable`s, Agda for some reason considers the `ℓ` in our type to
    be *different* than the `ℓ` in `A :` `type:Set` `ℓ`!


The `type:Dec` type corresponds to a particular *decision*, while
`type:Decidable` states that we can make a decision for *every input.* It's the
same difference between saying that you, personally, have an age, and saying
that *everyone* has an age.

Implementing `def:∈?` isn't hard, but has a lot of moving pieces, so let's work
it through together. Begin with the type:

```agda
  ∈?⅋₀ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₀ = ?
```

What we're saying here is that if we have decidable equality for some type `A`,
we can then give a decision procedure to check whether any element is in any
tree. Expanding out the arguments helps to see this:

```agda
  ∈?⅋₁ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₁ _≟_ t a = ?
```

As usual, we can [MakeCase](AgdaCmd) on the only value with an inductive data
type, that is, `t`:

```agda
  ∈?⅋₂ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₂ _≟_ empty a = {! !}
  ∈?⅋₂ _≟_ (branch l x r) a = {! !}
```

The `ctor:empty` case is easy, since we know there are no values in
`ctor:empty`, and thus that the answer must be `ctor:no`.

```agda
  ∈?⅋₃ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₃ _≟_ empty a = no λ ()
  ∈?⅋₃ _≟_ (branch l x r) a = {! !}
```

Checking out the `ctor:branch` case requires us to determine whether `x` is
equal to `a`, which we can do by invoking `x ≟ y` in a `keyword:with`
abstraction.

```agda
  ∈?⅋₄ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₄ _≟_ empty a = no λ ()
  ∈?⅋₄ _≟_ (branch l x r) a
    with x ≟ a
  ... | x≡a? = {! !}
```

Pattern match on `x≡a?`---if the answer is `ctor:yes`, then pattern matching on
the subsequent proof that `bind:a x:a ≡ x` will allow us to use the `ctor:here`
constructor to fill the hole:

```agda
  ∈?⅋₅ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₅ _≟_ empty a = no λ ()
  ∈?⅋₅ _≟_ (branch l x r) a
    with  x ≟ a
  ... |   yes  refl  = yes here
  ... |   no   x≢a   = {! !}
```

If `x` isn't what we were looking for, we can instead try to look down the left
subtree and see if we get any hits. Change the `keyword:with` abstraction to add
another binding:

```agda
  ∈?⅋₆ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₆ _≟_ empty a = no λ ()
  ∈?⅋₆ _≟_ (branch l x r) a
    with  x ≟ a      | ∈?⅋₆ _≟_ l a
  ... |   yes  refl  | _     = yes here
  ... |   no   x≢a   | x∈l?  = {! !}
```

We can play the same game here: pattern matching on `x∈l?` and rebuilding a
`ctor:yes` if we were successful. Before you ask, you can type `∉` via
[`inn`](AgdaMode).

```agda
  ∈?⅋₇ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₇ _≟_ empty a = no λ ()
  ∈?⅋₇ _≟_ (branch l x r) a
    with  x ≟ a      | ∈?⅋₇ _≟_ l a
  ... |   yes  refl  | _         = yes here
  ... |   no   _     | yes  x∈l  = yes (left x∈l)
  ... |   no   x≢a   | no   x∉l  = {! !}
```

If we didn't find what we were looking for, well, just try again in the right
branch:

```agda
  ∈?⅋₈ : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈?⅋₈ _≟_ empty a = no λ ()
  ∈?⅋₈ _≟_ (branch l x r) a
    with  x ≟ a      | ∈?⅋₈ _≟_ l a  | ∈?⅋₈ _≟_ r a
  ... |   yes  refl  | _             | _         = yes here
  ... |   no   _     | yes  a∈l      | _         = yes (left a∈l)
  ... |   no   _     | no   _        | yes  a∈r  = yes (right a∈r)
  ... |   no   x≢a   | no   a∉l      | no   a∉r  = {! !}
```

Should the answer to *all* of our queries be `ctor:no`, we can be certain that
`bind:a t:¬ a ∈ t`. All that's left is to say `ctor:no`, and then refute
whichever piece of evidence we've got:

```agda
  ∈? : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t)
  ∈? _≟_ empty a = no λ ()
  ∈? _≟_ (branch l x r) a
    with  x ≟ a      | ∈? _≟_ l a  | ∈? _≟_ r a
  ... |   yes  refl  | _           | _         = yes here
  ... |   no   _     | yes  a∈l    | _         = yes (left a∈l)
  ... |   no   _     | no   _      | yes  a∈r  = yes (right a∈r)
  ... |   no   x≢a   | no   a∉l    | no   a∉r
      = no λ  { here          → x≢a refl
              ; (left   a∈l)  → a∉l a∈l
              ; (right  a∈r)  → a∉r a∈r
              }
```

The resulting code compiles just fine, which, given the strength of our type
system, means it *works* just fine. We can convince ourselves by asking Agda,
leaving underscores in the `type:Dec` constructors---in essence, leaving Agda to
fill in the underscores but confirm that we picked the right constructors:

```agda
  open Nat-Properties
    using (_≟ℕ_)

  _ : ∈? _≟ℕ_ tree 2 ≡ yes _
  _ = refl

  _ : ∈? _≟ℕ_ tree 7 ≡ no _
  _ = refl
```

It's worth comparing and contrasting the implementation of `def:∈?` to that of
`def:_≟ℕ_`, as this is the form that *every* decision problem takes---at least
those concerned with the shape of a particular value.


## The All Predicate

Something else we might want to be able to prove is that every element in a
`type:BinTree` satisfies some property `P`---perhaps that it consists only of
odd numbers, as an odd example. For a more enterprise sort of example, perhaps
we'd like a proof that every employee in our tree has been properly connected to
payroll.

Building `type:All` is easy enough. We can replace every instance of `A` with `P
A`, and every instance of `type:BinTree` with `type:All`. Modulo a few indices
at the end, we're left with a reminiscent definition:

```agda
  data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (P : A → Set ℓ₂)
        : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where
    empty   : All P empty
    branch  : All P l → P a → All P r → All P (branch l a r)
```

In the `ctor:branch` case, we must show that `P` holds for everything in both
subtrees, as well as for the value at the root. By induction, we have thus
covered every element in the tree.

Like we did above for `type:BinTree`, it will be convenient to make a
`ctor:leaf` pattern here too. Because pattern synonyms don't come with a type
signature and constructor names can be reused, pattern synonyms work over any
type that has all of the necessary constructors. However, this is only the case
if those constructors existed before the pattern was defined.


Since `type:All` reuses the constructor names `ctor:empty` and `ctor:branch`, we
need only redefine `ctor:leaf` in order for it to work work not only over
`type:BinTree`, but `type:All` too.

```agda
  pattern leaf a = branch empty a empty
```

We can show that `type:All` works as expected, by coming up with a quick
predicate like the evenness of a number. Let's bring the machinery back into
scope:


```agda
  open Chapter2-Numbers
    using (IsEven; z-even; ss-even)
```

and now we would like to show that every element in `def:tree` is even:

```agda
  tree-all-even⅋₀ : All IsEven tree
  tree-all-even⅋₀ = ?
```

Thankfully, Agda is capable of proving this fact on our behalf, via
[Auto](AgdaCmd):

```agda
  tree-all-even : All IsEven tree
  tree-all-even =
    branch
      (branch
        (branch empty z-even empty)
        z-even
        (branch empty (ss-even z-even) empty))
      (ss-even (ss-even z-even))
      (branch empty (ss-even (ss-even (ss-even z-even))) empty)
```


Hidden

:   ```agda
  -- fix bind
    ```

Notice the repeated use of `expr:branch empty ? empty` here. Sometimes Agda can
work out that it should use your pattern synonyms, and sometimes it can't.
Unfortunately this is one of the times it can't, but we can clean it up
ourselves by judiciously invoking `ctor:leaf`:

```agda
  tree-all-even⅋ : All IsEven tree
  tree-all-even⅋ =
    branch
      (branch
        (leaf z-even)
        z-even
        (leaf (ss-even z-even)))
      (ss-even (ss-even z-even))
      (leaf (ss-even (ss-even (ss-even z-even))))
```


Hidden

:   ```agda
  -- fix bind
    ```


Exercise (Medium)

:   Show that `bind:P:All P` is `type:Decidable`, given `bind:P:Decidable P`.


Solution

:   ```agda
  all? : {P : A → Set} → Decidable P → Decidable (All P)
  all? p? empty = yes empty
  all? p? (branch l a r) with p? a | all? p? l | all? p? r
  ... | no ¬pa  | _       | _       = no λ { (branch _ pa _)  → ¬pa pa }
  ... | yes _   | no ¬al  | _       = no λ { (branch al _ _)  → ¬al al }
  ... | yes _   | yes _   | no ¬ar  = no λ { (branch _ _ ar)  → ¬ar ar }
  ... | yes pa  | yes al  | yes ar  = yes (branch al pa ar)
    ```

As this exercise shows, decision procedures are often extremely formulaic. You
decide each individual piece, and combine them together if possible. If not, you
must find a way to project a contradiction out of the bigger structure.


## Binary Search Trees

Binary search trees (BSTs) are a refinement of binary trees, with the property
that everything in the left subtree is less than or equal to the root, and
everything in the right subtree is greater than or equal to the root. This will
be our next challenge to define in Agda.

You might be starting to see a pattern here. We always just look at the
individual cases, figure out what we need for each, and then build an indexed
type that ensures the properties are all met. In this case, we know that an
`ctor:empty` `type:BinTree` is still a BST, so that's easy enough. In the case
of a `ctor:branch`, however, we have several properties we'd like to check:

1. Everything in the left subtree is less than the root, and
2. everything in the right tree is greater than the root, furthermore
3. the left subtree is itself a BST, and finally
4. the right subtree is also a BST.

Having worked out the details, the type itself has a straightforward encoding,
after realizing that we'd like to parameterize the whole thing by an ordering
relation.

```agda
  data IsBST {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (_<_ : A → A → Set ℓ₂)
      : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where
    bst-empty : IsBST _<_ empty
    bst-branch
        : All (_< a) l
        → All (a <_) r
        → IsBST _<_ l
        → IsBST _<_ r
        → IsBST _<_ (branch l a r)
```

Given the standard notion of ordering over the natural numbers:

```agda
  open Chapter4-Relations
    using (_≤_; z≤n; s≤s; _<_)
```

we can again ask Agda for a proof that `def:tree` is a BST under the `type:_≤_`
ordering relation, by invoking [Auto](AgdaCmd) to give us a definition of
`def:tree-is-bst`:

```agda
  tree-is-bst : IsBST _≤_ tree
  tree-is-bst =
    bst-branch
      (branch (leaf z≤n) z≤n (leaf (s≤s (s≤s z≤n))))
      (leaf (s≤s (s≤s (s≤s (s≤s z≤n)))))
      (bst-branch
        (leaf z≤n)
        (leaf z≤n)
        (bst-branch empty empty bst-empty bst-empty)
        (bst-branch empty empty bst-empty bst-empty))
      (bst-branch empty empty bst-empty bst-empty)
```

Proofs like this are an awful lot of work, but thankfully we never need to write
them by hand. For concrete values, we can always ask Agda to solve them for us,
and for parameterized values, we can build them by induction.

Speaking of induction, can we decide whether a given tree is a BST? Sure! The
pattern is exactly the same, decide each piece, derive contradictions on
`ctor:no`, and assemble the final proof if everything is `ctor:yes`. This time,
rather than doing all of our `keyword:with` abstraction at once, we will test
one property at a time---leading to a more "vertical" definition:

```agda
  is-bst?
      : {_≤_ : A → A → Set}
      → Decidable₂ _≤_
      → Decidable (IsBST _≤_)
  is-bst? _≤?_ empty = yes bst-empty
  is-bst? _≤?_ (branch l a r)
    with all? (_≤? a) l
  ... | no   l≰ = no λ { (bst-branch l≤ _ _ _) → l≰ l≤ }
  ... | yes  l≤
    with all? (a ≤?_) r
  ... | no   ≰r = no λ { (bst-branch _ ≤r _ _) → ≰r ≤r }
  ... | yes  ≤r
    with is-bst? _≤?_ l
  ... | no   ¬bst-l = no λ { (bst-branch _ _ bst-l _) → ¬bst-l bst-l }
  ... | yes  bst-l
    with is-bst? _≤?_ r
  ... | no   ¬bst-r  = no λ { (bst-branch _ _ _ bst-r) → ¬bst-r bst-r }
  ... | yes  bst-r   = yes (bst-branch l≤ ≤r bst-l bst-r)
```

You might be wondering whether there is an easier way to assemble these proofs.
Unfortunately, there is not. Nothing in the theory precludes us from generating
them, but at time of writing, there is alas no automatic means of deriving such.


## Trichotomy

What we have done thus far is show that there exist things called binary search
trees, and we have given a definition of what properties we mean when we say
something is or isn't a binary search tree. This is a great
start---prescriptively speaking---but this is not exactly where most computer
science textbooks go when they discuss BSTs. Instead, they immediately dive into
the meat of "what can you do with a BST."

*Insertion* is something you can do with a BST, and lest we be left behind by
the traditional pedagogical material, let's turn our discussion in that
direction. The algorithm is easy enough---if the tree is `ctor:empty`, add a
`ctor:leaf`. Otherwise, compare the value you'd like to insert with the value at
the root. If they're equal, you're done. Otherwise, recursively insert the value
into the correct subtrees.

The implicit claim here is that this algorithm preserves the `type:IsBST`
invariant, but that is never explicitly stated. For the record, this algorithm
*does* indeed preserve the `type:IsBST` invariant. However, this poses some
challenges for us, since in order to show this we must necessarily derive a
proof, which is going to recursively depend on a proof that inserted into the
correct subtree.

What we have to work with thus far is only the fact that `type:_<_` is
decidable. But if we were to work directly with the decidability `type:_<_`, our
algorithm would need to first check whether `bind:a x:a < x`, and if it isn't,
check that `bind:a x:x < a`, and if it isn't check that `bind:a x:x ≡ a`, and if
*that also isn't,* well, then we definitely have a problem.

However, it should be the case that exactly one of `bind:a x:a < x`, `bind:a x:x
< a`, and `bind:a x:x ≡ a` should be true for any `x` and `a` you could
possibly desire. We could attempt to prove this directly, but it doesn't sound
like an enjoyable experience. As we have seen above, every invocation of
decidability doubles the amount of work we need to do, since we need to use the
proof or show a subsequent contradiction.

Instead, we can generalize the idea of decidability to a *trichotomy*, which is
the idea that exactly one of three choices must hold. From this perspective,
`type:Dec` is merely a type that states exactly one of `P` or `type:¬` `P`
holds, and so the notion of trichotomy shouldn't be earth-shattering. We can
define `type:Tri` (analogous to `type:Dec`) as as proof that exactly one of `A`,
`B` or `C` holds:

```agda
  data Tri {a b c : Level} (A : Set a) (B : Set b) (C : Set c)
        : Set (a ⊔ b ⊔ c) where
    tri< :    A → ¬  B → ¬  C → Tri A B C
    tri≈ : ¬  A →    B → ¬  C → Tri A B C
    tri> : ¬  A → ¬  B →    C → Tri A B C
```

Just as we defined `type:Decidable₂`, we will now lift this notion of `def:Tri`
to an analogous `type:Trichotomous`: stating that for two relations, one
equality-like, and one less-than-like, we can always determine which of the
three options holds.

```agda
  Trichotomous
      : {ℓ eq lt : Level}
      → {A : Set ℓ}
      → (_≈_ : A → A → Set eq)
      → (_<_ : A → A → Set lt)
      → Set (lt ⊔ eq ⊔ ℓ)
  Trichotomous {A = A} _≈_ _<_ =
    (x y : A) → Tri (x < y) (x ≈ y) (y < x)
```

As a good exercise, we'd like to show that `type:ℕ` is trichotomous with respect
to `type:_≡_` and `type:_<_`. Doing so will require a quick lemma. If we know
$x \nless y$ then we also know $x + 1 \nless y + 1$:

```agda
  refute : {x y : ℕ} → ¬ x < y → ¬ suc x < suc y
  refute x≮y (s≤s x<y) = x≮y x<y
```

Given these two lemmas, its not too much work to bash out `def:<-cmp`, the
traditional name for the trichotomy of the natural numbers. The hardest part is
simply massaging all six of the refutations in the recursive case:

```agda
  <-cmp : Trichotomous  _≡_ _<_
  <-cmp zero zero    = tri≈ (λ ())     refl    (λ ())
  <-cmp zero (suc y) = tri< (s≤s z≤n)  (λ ())  (λ ())
  <-cmp (suc x) zero = tri> (λ ())     (λ ())  (s≤s z≤n)
  <-cmp (suc x) (suc y) with <-cmp x y
  ...  | tri< x<y x≉y x≱y
       = tri<  (s≤s x<y)
               (λ { sx≈sy → x≉y (suc-injective sx≈sy) })
               (refute x≱y)
  ...  | tri≈ x≮y x≈y x≱y
       = tri≈  (refute x≮y)
               (cong suc x≈y)
               (refute x≱y)
  ...  | tri> x≮y x≉y x>y
       = tri>  (refute x≮y)
               (λ { sx≈sy → x≉y (suc-injective sx≈sy) })
               (s≤s x>y)
```

Working directly with `type:Tri`, rather than several invocations to
`type:Decidable₂ _<_` will dramatically reduce the proof effort necessary to
define `def:insert` and show that it preserves `type:IsBST`, which we will do in
the next section.


## Insertion into BSTs

We are going to require a `type:_<_` relation, and a proof that it forms a trichotomy
with `type:_≡_` in order to work through the implementation details here. Rather than
pollute all of our type signatures with the necessary plumbing, we can instead
define an anonymous module and add the common parameters to that instead, as in:

```agda
  module _
      {ℓ : Level}
      {_<_ : A → A → Set ℓ}
      (<-cmp : Trichotomous _≡_ _<_) where
```



Anything defined in this module will now automatically inherit `_<_` and
`def:Trichotomous` `_≡_ _<_` arguments, meaning we don't need to pass the
(locally-bound) `<-cmp` function around by hand.

Defining `def:insert` follows exactly the same template as our in-writing
algorithm above---recall, the plan is to replace `ctor:empty` with `ctor:leaf`,
and otherwise recurse down the correct subtree in the case of `ctor:branch`.
After everything we've been doing lately, `def:insert` turns out to be a walk in
the park:

```agda
    insert
        : A
        → BinTree A
        → BinTree A
    insert a empty = leaf a
    insert a (branch l x r) with <-cmp a x
    ... | tri< _ _ _ = branch (insert a l) x r
    ... | tri≈ _ _ _ = branch l x r
    ... | tri> _ _ _ = branch l x (insert a r)
```

We would now like to show that `def:insert` preserves the `type:IsBST` invariant. That
is, we'd like to define the following function:

```agda
    bst-insert⅋
        : (a : A)
        → {t : BinTree A}
        → IsBST _<_ t
        → IsBST _<_ (insert a t)
    bst-insert⅋ = ?
```

Before diving into this proper, we will do a little thinking ahead and realize
that showing `type:IsBST` for a `ctor:branch` constructor requires showing that all
elements in either subtree are properly bounded by the root. Therefore, before
we show that `def:insert` preserves `type:IsBST`, we must first prove that `def:insert`
preserves `type:All`! The type we need to show is that if `P a` and `All P t` hold
(for any `P`), then so too must `All P (insert a t)`:

```agda
    all-insert⅋₀
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₀ = ?
```

After binding our variables (including `t`, carefully positioned so that we can
avoid binding `P`), our function now looks like:

```agda
    all-insert⅋₁
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₁ a pa {t} all-pt = {! !}
```

Asking now for a [MakeCase:all-pt](AgdaCmd) results in:

```agda
    all-insert⅋₂
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₂ a pa {.empty} empty = {! !}
    all-insert⅋₂ a pa {.(branch _ _ _)} (branch l<x px x<r) = {! !}
```

Notice that when we pattern matched on `all-pt`, Agda realized that this fully
determines the results of `t` as well, and it happily expanded them out into
these funny `.``ctor:empty` `.``ctor:branch` patterns. These are called *dot
patterns,* and they correspond to patterns whose form has been fully determined
by pattern matching on something else. We will discuss dot patterns more
thoroughly in @sec:dot-patterns, but for the time being, it suffices to know
that, whenever we have a dot pattern, we can simply replace it with a regular
pattern match:

```agda
    all-insert⅋₃
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₃ a pa {empty} empty = {! !}
    all-insert⅋₃ a pa {branch l x r} (branch l<x xp x<r) = {! !}
```

Finally, there is no reason to pattern match on the implicit `ctor:empty`, since
it doesn't bring any new variables into scope.

```agda
    all-insert⅋₅
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₅ a pa empty = {! !}
    all-insert⅋₅ a pa {branch l x r} (branch l<x px x<r) = {! !}
```

Filling the first hole is merely showing that we have `type:All` for a singleton,
which is our `ctor:leaf` constructor:

```agda
    all-insert⅋₆
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₆ a pa empty = leaf pa
    all-insert⅋₆ a pa {branch l x r} (branch l<x px x<r) = {! !}
```

Attempting to [Refine](AgdaCmd) this last hole results in a funny thing. We know
it must be filled with a `ctor:branch`, but Agda will refuses.If you ask for the
type of the goal, we see something peculiar:

```info
Goal: All P (insert <-cmp a (branch l x r) | <-cmp a x)
```

The vertical bar is not anything that you're allowed to write for yourself, but
the meaning here is that the result of `def:insert` is stuck until Agda knows the
result of `bind:a:<-cmp a`. Our only means of unsticking it is to also do a
`keyword:with` abstraction over `bind:a x:<-cmp a x` and subsequently pattern
match on the result:

```agda
    all-insert⅋₇
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₇ a pa empty = leaf pa
    all-insert⅋₇ a pa {branch l x r} (branch l<x px x<r)
      with <-cmp a x
    ... | tri< a<x _ _ = {! !}
    ... | tri≈ _ a=x _ = {! !}
    ... | tri> _ _ x<a = {! !}
```

Looking at this new set of goals, we see that they are no longer stuck and have
now computed to things we're capable of implementing. By now you should be able
to complete the function on your own:

```agda
    all-insert
        : {P : A → Set ℓ} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert a pa empty = leaf pa
    all-insert a pa {branch l x r} (branch l<x px x<r)
      with <-cmp a x
    ... | tri< a<x _ _  = branch (all-insert a pa l<x) px x<r
    ... | tri≈ _ a=x _  = branch l<x px x<r
    ... | tri> _ _ x<a  = branch l<x px (all-insert a pa x<r)
```

Now that we've finished the `def:all-insert` lemma, we're ready to pop the stack
and show that `def:insert` preserves `type:IsBST`.

Again, when implementing this you will see that the type will get stuck on
`bind:x t:insert x t` `|` `bind:a x:<-cmp a x`, and will require another pattern
match on `bind:a x:<-cmp a x`. This will always be the case when proving things
that pattern match on a `keyword:with` abstraction; it is for this reason that
we say the proof has the same shape as the computation. It's like poetry: it
rhymes.

Implementing `def:bst-insert` isn't any more of a cognitive challenge than
`def:all-insert` was; just pattern match and then build a proof term via
induction:

```agda
    bst-insert
        : (a : A)
        → {t : BinTree A}
        → IsBST _<_ t
        → IsBST _<_ (insert a t)
    bst-insert a bst-empty
      = bst-branch empty empty bst-empty bst-empty
    bst-insert a {branch l x r} (bst-branch l<x x<r lbst rbst)
      with <-cmp a x
    ... | tri< a<x _ _ =
            bst-branch
              (all-insert a a<x l<x)
              x<r
              (bst-insert a lbst)
              rbst
    ... | tri≈ _ a=x _ = bst-branch l<x x<r lbst rbst
    ... | tri> _ _ x<a =
            bst-branch
              l<x
              (all-insert a x<a x<r)
              lbst
              (bst-insert a rbst)
```

With `def:bst-insert` finally implemented, we have now proven that inserting
into a binary search tree results in another binary search tree. It's a bit of
an underwhelming result for all the work we've done, isn't it? In the next
section, we will look at alternative ways of phrasing the problem that can help.


## Intrinsic vs Extrinsic Proofs


Hidden

:   ```agda
  -- fix bind
    ```


This style of proof we have demonstrated, is called an *extrinsic* proof. The
idea here is that we have defined a type `bind:A:BinTree A` and an operation
`def:insert` `:` `bind:A:A → BinTree A → BinTree A` in such a way that they are
not guaranteed to be correct. In order to subsequently prove that they are, we
added an additional layer on top, namely `type:IsBST` and `def:bst-insert` which
assert our invariants after the fact. This is a very natural way of proving
things, and is a natural extension of the way most people write code: do
the implementation first, and tack the tests on afterwards.

However, extrinsic proofs are not our only option! We can instead make a
`type:BST` `A` type which satisfies the binary search tree invariant *by
construction.* By virtue of this being by construction, we are not required to
tack on any additional proof: the existence of the thing itself is proof
enough. We call this notion of proof *intrinsic*, as the proof is intrinsic to
the construction of the object itself. In a sense, intrinsic proofs don't exist
at all; they're just cleverly-defined objects of study.

Intrinsic proofs are desirable because they only require you to do the work
once. Recall that when defining both `def:bst-insert` and `def:all-insert`, we
essentially had to mirror the definition of `def:insert` modulo a few changes. It
was quite a lot of work, and you can imagine that this effort would multiply
substantially for each additional operations we'd like to define over BSTs.
Extrinsic proofs make you shoulder this burden all on your own.

That's not to say that intrinsic proofs are without downsides. At the forefront,
almost every algorithm you have ever seen is given with an extrinsic proof---if
it comes with a proof at all. Not only are we as computer scientists better
primed for thinking about extrinsic proof, but worse: the field itself is
riddled with them. Almost every algorithm you have ever heard of isn't amenable
to intrinsic proof, as most algorithms violate the intrinsic invariant at some
point. The invariant of most structures is a macro-level property, preserved by
common operations, but rarely preserved *inside* of them.

For example, consider a heap data structure, which is a particular
implementation of a priority queue---at any time, you can extract the
highest-priority thing in the queue. Heaps are usually implemented as binary
trees (or sometimes, clever encodings of binary trees as arrays) with the *heap
property:* the root node is larger than everything else in the tree. The heap
property is also satisfied recursively, so that we have a partial ordering over
all elements in the heap.

Now imagine we'd like to insert something new into the heap. We don't know where
it should go, so we insert it into the first empty leaf we can find, and then
recursively "bubble" it up. That is to say, you put it at a leaf, and then check
to see if it's larger than its parent. If so, you swap the two, and then recurse
upwards. Eventually the newly-insert element is somewhere in the tree such that
the heap invariant is met.

This algorithm works just fine, but it *cannot* be used in an intrinsic heap,
because when we first insert the new element into a bottom-most leaf, the heap
property is immediately broken! It doesn't matter if we eventually fix the
invariant; the intrinsic construction of heaps means it's *impossible* to insert
an element somewhere it doesn't belong, and thus the bubble algorithm cannot be
used.

It is for reasons like these that intrinsic proofs are *hard* for computer
scientists. Fully embracing them requires unlearning a great deal of what our
discipline has taught us, and that is a notoriously difficult thing to do.


## An Intrinsic BST

Constructing an intrinsic BST is not the most straightforward construction, but
thankfully @mcbride_how_2014 has done the hard work for us and we will re-derive
his solution here.

In order to define an intrinsic binary search tree, we will proceed in two
steps. First, we will define a BST indexed by its upper and lower bounds, which
we can subsequently use to ensure everything is in its right place, without
resorting to extrinsic techniques like `type:All`. We will then hide these
indices again to get a nice interface for the whole thing.

Begin with a new module to sandbox our first step:

```agda
module Intrinsic-BST-Impl
    {c ℓ : Level} {A : Set c} (_<_ : A → A → Set ℓ) where
```


Hidden

:   ```agda
  -- fix bind
    ```

As before, we make a `type:BST` type, but this time parameterized by a `lo` and `hi`
bound. In the `ctor:empty` constructor we require a proof that `bind:lo hi:lo <
hi`.

```agda
  data BST (lo hi : A) : Set (c ⊔ ℓ) where
    empty : lo < hi → BST lo hi
```

Our other constructor, `ctor:branch`, now restricts the bounds of its left and right
subtrees so their top and bottom bounds are the root, respectively:

```agda
    xbranch  -- ! 2
        : (a : A)  -- ! 1
        → BST lo a
        → BST a hi
        → BST lo hi
```

Notice at [1](Ann) that the root of the tree comes as the first argument! This
is unlike our extrinsic `ctor:branch`, but is necessary here so that `a` is in scope
when we build our subtrees. The discrepancy in argument order is why this
constructor has been named `ctor:xbranch`, as indicated at [2](Ann).

Fortunately, we can use a pattern synonym to shuffle our parameters back into
the correct shape, as well as one to bring back `ctor:leaf`s:

```agda
  pattern branch lo a hi = xbranch a lo hi
  pattern leaf lo<a a a<hi = branch (empty lo<a) a (empty a<hi)
```

Returning to the issue of `def:insert`, we notice one big problem with putting
the bounds in the type index: it means that `def:insert` could *change the type*
of the `type:BST` if it is outside the original bounds! This is a bad state of
affairs, and will dramatically harm our desired ergonomics. For the time being,
we will sidestep the issue and merely require proofs that `a` is already in
bounds.

The implementation of `def:insert` is nearly identical to our original,
extrinsically-proven version:

```agda
  open BinaryTrees using (Trichotomous; Tri)
  open Tri

  insert
      : {lo hi : A}
      → (<-cmp : Trichotomous _≡_ _<_)
      → (a : A)
      → lo < a
      → a < hi
      → BST lo hi
      → BST lo hi
  insert <-cmp a lo<a a<hi (empty _) = leaf lo<a a a<hi
  insert <-cmp a lo<a a<hi (branch l x r)
    with <-cmp a x
  ... | tri< a<x _ _ = branch (insert <-cmp a lo<a a<x l) x r
  ... | tri≈ _ a=x _ = branch l x r
  ... | tri> _ _ x<a = branch l x (insert <-cmp a x<a a<hi r)
```

This concludes our first step of the problem. We now have an
intrinsically-proven BST---all that remains is to deal with the type-changing
problem, putting an ergonomic facade in front.

A cheeky solution to the problem of `def:insert` possibly changing the type is
to bound all BSTs by the equivalent of negative and positive infinity. This is,
in essence, throwing away the bounds---at least at the top level. If we can hide
those details, we will simultaneously have solved the problem of changing types
and the ergonomics of needing to juggle the bounds. Let's do that now.

The first step is to define a type which *extends* `A` with the notions of
positive and negative infinity. We'll put this in a new module, because we'd
like to instantiate its parameters differently than those of
`module:Intrinsic-BST-Impl`:

```agda
open BinaryTrees using (Trichotomous)

module Intrinsic-BST
          {c ℓ : Level} {A : Set c}
          {_<_ : A → A → Set ℓ}
          (<-cmp : Trichotomous _≡_ _<_) where

  data A↑ : Set c where
    -∞ +∞  : A↑
    ↑      : A → A↑
```

We can type the `↑` symbol here as [`u-`](AgdaMode), and `∞` as [inf](AgdaMode).

The `ctor:↑` constructor lifts an `A` into `type:A↑`, and it is through this
mechanism by which we are justified in saying that `type:A↑` extends `A` with
`ctor:-∞` and `ctor:+∞`.

From here, it's not too hard to define a `type:_<_` relationship over `type:∞`:

```agda
  data _<∞_ : A↑ → A↑ → Set ℓ where
    -∞<↑   : {x    : A}          → -∞   <∞ ↑ x
    ↑<↑    : {x y  : A} → x < y  → ↑ x  <∞ ↑ y
    ↑<+∞   : {x    : A}          → ↑ x  <∞ +∞
    -∞<+∞  : -∞ <∞ +∞
```

This has all the properties you'd expect, that `ctor:-∞` is less than everything
else, `ctor:+∞` is more than everything else, and that we can lift `type:_<_` over `A`.
The trick should be clear: we are not going to instantiate the
`module:Intrinsic-BST-Impl` module at type `A`, but rather at `type:∞`!

Before we can do that, however, we must show that our new `type:_<∞_` is
trichotomous. This is quite a lot of work, but the details are uninteresting to
us by now, and indeed Agda can do the first several cases for us automatically:

```agda
  open BinaryTrees using (Tri)
  open Tri

  <∞-cmp : Trichotomous _≡_ _<∞_
  <∞-cmp  -∞     -∞     = tri≈ (λ ())  refl    (λ ())
  <∞-cmp  -∞     +∞     = tri< -∞<+∞   (λ ())  (λ ())
  <∞-cmp  -∞     (↑ _)  = tri< -∞<↑    (λ ())  (λ ())
  <∞-cmp  +∞     -∞     = tri> (λ ())  (λ ())  -∞<+∞
  <∞-cmp  +∞     +∞     = tri≈ (λ ())  refl    (λ ())
  <∞-cmp  +∞     (↑ _)  = tri> (λ ())  (λ ())  ↑<+∞
  <∞-cmp  (↑ _)  -∞     = tri> (λ ())  (λ ())  -∞<↑
  <∞-cmp  (↑ _)  +∞     = tri< ↑<+∞    (λ ())  (λ ())
```

All that's left is lifting `<-cmp`, which we must do by hand:

```agda
  <∞-cmp (↑ x) (↑ y)
    with <-cmp x y
  ... | tri< x<y ¬x=y ¬y<x =
          tri<
            (↑<↑ x<y)
            (λ { refl → ¬x=y refl })
            (λ { (↑<↑ y<x) → ¬y<x y<x })
  ... | tri≈ ¬x<x refl _ =
          tri≈
            (λ { (↑<↑ x<x) → ¬x<x x<x })
            refl
            (λ { (↑<↑ x<x) → ¬x<x x<x })
  ... | tri> ¬x<y ¬x=y y<x =
          tri>
            (λ { (↑<↑ x<y) → ¬x<y x<y })
            (λ { refl → ¬x=y refl })
            (↑<↑ y<x)
```

The end is nigh! We can now define our final `type:BST` as one bounded by
`ctor:-∞` and `ctor:+∞`:

```agda
  open module Impl = Intrinsic-BST-Impl _<∞_
    hiding (BST; insert)

  BST : Set (c ⊔ ℓ)
  BST = Impl.BST -∞ +∞
```

and finally, define insertion by merely plugging in some trivial proofs:

```agda
  insert : (a : A) → BST → BST
  insert a t = Impl.insert <∞-cmp (↑ a) -∞<↑ ↑<+∞ t
```


## Wrapping Up

-- TODO(sandy): finalize wrapping up

```agda
open import Relation.Binary
  using (Reflexive; Transitive; DecidableEquality)
  using (Trichotomous; Tri)
  renaming (Decidable to Decidable₂)
  public

open import Data.Empty
  using (⊥; ⊥-elim)
  public

open import Relation.Unary
  using (Decidable)
  public

open import Relation.Nullary
  using (Dec; yes; no; ¬_)
  public

open import Relation.Nullary.Decidable
  renaming (map′ to map-dec)
  public

open import Data.Nat.Properties
  using (<-cmp)
  public

open import Relation.Binary.PropositionalEquality
  using (_≢_; ≢-sym)
  public

open BinaryTrees
  using (BinTree; empty; branch; leaf)
  public
```




## Unicode {.unlisted}

```unicodetable
¬ U+00AC NOT SIGN
× U+00D7 MULTIPLICATION SIGN
ˡ U+02E1 MODIFIER LETTER SMALL L
Σ U+03A3 GREEK CAPITAL LETTER SIGMA
λ U+03BB GREEK SMALL LETTER LAMDA
′ U+2032 PRIME
₁ U+2081 SUBSCRIPT ONE
₂ U+2082 SUBSCRIPT TWO
ℓ U+2113 SCRIPT SMALL L
ℕ U+2115 DOUBLE-STRUCK CAPITAL N
ℤ U+2124 DOUBLE-STRUCK CAPITAL Z
↑ U+2191 UPWARDS ARROW
→ U+2192 RIGHTWARDS ARROW
∈ U+2208 ELEMENT OF
∉ U+2209 NOT AN ELEMENT OF
∞ U+221E INFINITY
∸ U+2238 DOT MINUS
≈ U+2248 ALMOST EQUAL TO
≉ U+2249 NOT ALMOST EQUAL TO
≟ U+225F QUESTIONED EQUAL TO
≡ U+2261 IDENTICAL TO
≢ U+2262 NOT IDENTICAL TO
≤ U+2264 LESS-THAN OR EQUAL TO
≮ U+226E NOT LESS-THAN
≰ U+2270 NEITHER LESS-THAN NOR EQUAL TO
≱ U+2271 NEITHER GREATER-THAN NOR EQUAL TO
⊔ U+2294 SQUARE CUP
⊥ U+22A5 UP TACK
```

