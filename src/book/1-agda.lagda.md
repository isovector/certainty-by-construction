# Introduction to Agda

This book in your hands is no ordinary prose. No, it is a living, breathing
document. Certainly this is a curious claim; on what grounds can it be made? The
book you are reading is not just a book, it is also a computer program written
in the *literate style.*

Literate programming is a technique for interspersing prose and computer
programs in the same document. The result is a "polyglot": a single artifact
that can be interpreted simultaneously as a book written in English, or a series
of program modules written in Agda.

The advantage of reading a literate program are that you can be sure the code
*actually works.* This is not by the virtue of having had a diligent
copy-editor; it's merely a byproduct of the process. The book simply can't be
assembled into its current form if it contains any syntax errors or if any of
its tests fail. And as we will see shortly, Agda programs come with very
extensive tests. Furthermore, presenting all the code means I, the author,
cannot sweep any nitty-gritty details under the rug.

When code is presented in this book, it will come in a box like the following:

```agda
module 1-agda where
```

This is not merely an example; it's necessary preamble when starting a new Agda
file. The `module` is Agda's simplest unit of compilation, and every chapter in
this book will begin a new module. Thus, you shouldn't be surprised to see
similar blocks of code at the beginning of each chapter.

One distinct advantage of organizing chapters into modules is that chapters thus
become conceptual units in our program. If a later chapter depends on an earlier
one, this fact must be explicitly documented in the prose by way of an `import`.
If later chapters require code or extend concepts from earlier ones, they can
simply import the necessary pieces. For example, we will require the following
modules from the standard library later on, which we can import as follows:

```agda
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
```

You can think of literate programming being similar to writing comments in your
code, with one important difference: comments rarely evolve with the code they
are meant to document. Comments are a second class citizen: in the land of
programming, code always wins.

The situation is a rather apt metaphor for doing programming in Agda. Most
programming languages are concerned only with "how" --- that is, *how* can we
instruct the computer to get us a result? The desired result of most programs is
implicitly hiding between the lines; the ultimate source of truth as to what a
program *does* is the series of steps it performs. Perhaps some documentation
exists of the function, but there are no guarantees it is correct.

Of course, nothing (automated) checks the prose of this book, but Agda is a
language not only about "how", but also "what." Agda allows us to articulate
extremely precise statements, for example "for any number, there exists a bigger
number":

```agda
no-biggest-number : ∀ (n : ℕ) → ∃[ m ] n ≤ m
```

Don't concern yourself with the exact details of `no-biggest-number` right this
moment. All that's important to takeaway here is that we have articulated a deep
mathematical fact in our language. This, is the *what* of our program.

Of course, Agda also supports the "how", and since it's a programming language,
we are required to give a "how" for every "what." The implementation of
`no-biggest-number` looks like this:

```agda
no-biggest-number n =
  suc n , ≤-trans (≤-reflexive
                    (sym
                      (+-identityʳ n)))
                  (≤-trans
                    (+-mono-≤ {n} ≤-refl z≤n)
                    (≤-reflexive
                      (+-comm n 1)))
```

The implementation here might look overwhelming, but don't fret, the details
aren't important just now, and you'll understand this code just fine after a few
chapters.

