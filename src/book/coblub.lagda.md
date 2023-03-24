# The Co-blub Paradox

It is widely acknowledged that the languages you speak shape the thoughts you
can think; while this is true for natural language, it is doubly so in the case
of programming languages. And it's not hard to see why; while humans have
dedicated neural circuitry for natural language, it would be absurd to suggest
there is dedicated neural circuitry for fiddling around with the semantics of
pushing around arcane symbol abstractly encoded as electrical potentials over a
conductive metal.

Because programming---and mathematics more generally---does not come easily to
us humans, it can be hard to see the forest for the trees. We have no built-in
intuition as to what should be possible, and thus, this intuition is built by
observing the artifacts created by more established practitioners. In these more
"artificial" of human endeavors, newcomers to the field are truly
constructivists---their methods for practicing the art are shaped only by their
previously-observed patterns. Because different programming languages support
different features and idioms, the imaginable shape of what programming *is*
must be shaped by the languages we understand.

In a famous essay, "Beating the Averages," Paul Graham points out the so-called
*Blub paradox.* This, Graham says, is the ordering of programming languages by
powerfulness; a programmer who thinks in a middle-of-the-road language along
this ordering (call it Blub) can identify less powerful languages, but not those
which are more powerful. The idea rings true; one can arrange languages in power
by the features they support, and subsequently check to see if a language
supports all the features felt to be important. If it doesn't, it must be less
powerful. However, this technique doesn't work to identify more powerful
languages---at best, you will see that the compared language supports all the
features you're looking for, but you don't know enough to ask for more.

More formally, we can describe the Blub paradox as a semi-decision procedure.
That is, given an ordering over programming languages (here, by "power",) we can
determine whether a language is less than our comparison language, but not
whether it is more than. We can determine when the answer is definitely "yes,"
but, not when it is "no!"

Over two decades of climbing this lattice of powerful languages, I have come to
understand a lesser-known corollary of the Blub paradox, coining it the
*Co-Blub paradox*[^coblub-name]. This is the observation that knowledge of
lesser languages is *actively harmful* in the context of a more powerful
language. The hoops you unwittingly jumped through in Blub due to lacking
feature X are *anti-patterns* in the presence of feature X. This is obviously
true when stated abstractly, but insidious when one is in the middle of it.

[^coblub-name]: Although precisely speaking, the name should be the co-(Blub
  paradox), as the corollary applies to the paradox as a whole, not only the
  Blub piece. Alas, such is an awkward construction in English, and thus we will
  not use it.

Let's look at a few examples over the ages, to help motivate the problem before
we get into our introspection proper. In the beginning, people programmed
directly in machine code. Not assembly, mind you, but in raw binary-encoded
op-codes. They had a book somewhere showing them what bits needed to be set in
order to cajole the machine into performing any given instruction. Presumably if
this were your job, you'd come to memorize the bit patterns for common
operations, and it wouldn't be nearly as tedious as it seems today.

Then came assembly languages, which provided human-meaningful mnemonics to the
computer's opcodes. No longer did we need to encode a jump as
`11111000110000001100` --- now it was `jl 16`. Still mysterious, to be sure, but
significant gains are realized in legibility. When encoded directly in machine
code, programs were, for the most part, write-only. But assembly languages
don't come for free; first you need to write an assembler: a program that reads
the mnemonics and outputs the raw machine code. If you were already proficient
writing machine code directly, you can imagine the task of implementing an
assembler to feel like make work---a tool to automate a problem you don't have.
In the context of the Co-Blub paradox, knowing the direct encodings of your
opcodes is an anti-pattern when you have an assembly language, as it makes your
contributes inscrutable among your peers.

Programming directly in assembly eventually hit its limits. Every computer had a
different assembly language, which meant if you wanted to run the same program
on a different computer you'd have to completely rewrite the whole thing; often
needing to translate between extremely different concepts and limitations.
Ignoring a lot of history, C came around with the big innovation that software
should be portable between different computers: the same C program should work
regardless of the underlying machine architecture. If you were an assembly
programmer, you ran into the anti-pattern that while you could squeeze more
performance and perform clever optimizations if you were aware of the underlying
architecture, this fundamentally limited you *to that platform.*

By virtue of being, in many ways, a unifying assembly language, C runs very
close to what we think of as "the metal." Although different computer
architectures have minor differences in registers and ways of doing things, they
are all extremely similar variations on a theme. They all expose storable memory
indexed by a number, operations for performing basic logic and arithmetic tasks,
and means of jumping around to what the computer should consider to be the next
instruction. As a result, C exposes this abstraction of what a computer *is* to
its programmers, who are thus required to think about mutable memory and about
how to encode complicated objects as sequences of bytes in that memory. But then
came Java, whose contribution to mainstream programming was to popularize the
idea that memory is cheap and abundant, and thus OK to waste some in order to
alleviate the headache of needing to track it all yourself. As a C programmer
coming to Java, you must unlearn the idea that memory is sacred and scarce, that
you can do a better job of keeping track of it than the compiler can, and,
hardest of all, that it is an important thing to track in the first place.

There is a clear line of progression here; as we move up the lattice of powerful
languages, we notice that more and more details of what we thought were integral
parts of programming turn out to be not particularly relevant to the actual task
at hand. However, the examples thus discussed are already known to the modern
programmer. Let's take a few steps further, into languages deemed esoteric in
the present day. It's easy to see and internalize examples from the past, but
those staring us in the face are much more difficult to spot.

Compare Java then to Lisp, which---among many things---makes the argument that
functions, and even *programs themselves,*  are just as meaningful objects as
are numbers and records. Where Java requires the executable pieces to be
packaged up and moved around with explicit dependencies on the data it requires,
Lisp just lets you write and pass around functions, which automatically carry
around all the data they reference. Java has a *design pattern* for this called
the "command pattern," which requires much ado and ink to be spilled, while in
Lisp it just works in a way that is hard to understand if you are used to
thinking about computer programs as static sequences of instructions. Indeed,
the command pattern is bloated and ultimately unnecessary in Lisp, and
practitioners must first unlearn it before they can begin to see the beauty of
Lisp.

Haskell takes a step further than Lisp, in that it restricts when and where
side-effects are allowed to occur in a program. This sounds like heresy (and
feels like it for the first six months of programming in Haskell) until you come
to appreciate that *almost none* of a program needs to perform side-effects. As
it happens, side-effects are the only salient observation of the computer's
execution model, and by restricting their use, Haskell frees its programmers
from needing to think about how the computer will execute their code---promising
only that it will. As a result, Haskell code looks much more like mathematics
than it looks like a traditional computer program. Furthermore, by abstracting
away the execution model, the runtime is free to parallelize and reorder code,
often even eliding unnecessary execution altogether. The programmer who refuses
to acknowledge this reality and insists on coding with side-effects pays a great
price, both on the amount of code they need to write, in its long-term
reusability, and, most importantly, in the correctness of their computations.

All of this brings us to Agda, which is as far as I've gotten along the power
lattice of programming languages. While Agda looks a great deal like Haskell,
its powerful typesystem allows us to articulate many invariants that are
impossible to write down in other languages. It's tempting to think about Agda
as Haskell-but-with-better-types, but this is missing the point. Agda's type
system is so precise we can *prove* that our solutions are correct, which
alleviates the need to actually *run* the subsequent programs. In essence,
programming in Agda abstracts away the notion of execution entirely. Following
our argument about co-Blub programmers, they will come to Agda with the
anti-pattern that thinking their hard-earned, battle-proven programming
techniques for wrangling runtime performance will come in handy. But this is not
the case; most of the techniques we have learned and consider "computer science"
are in fact *implementation ideas:* that is, specific realizations from infinite
classes of solutions, chosen not for their simplicity or clarity, but for their
*efficiency.*

Thus, the process of learning Agda, in many ways, is learning to separate
the beautiful aspects of problem solving from the multitude of clever hacks we
have accumulated over the years. Much like the fish who is unable to recognize
the ubiquitous water around him, as classically-trained programmers, it is
nigh-impossible to differentiate the salient points from the implementation
details until we find ourselves in a domain where they do not overlap. Indeed,
in Agda, you will often feel the pain of having accidentally conflated the two,
when your proofs end up being much more difficult than you feel they deserve.
Despite the pain and the frustration, this is in fact a feature, and not a bug.
It is a necessary struggle, akin to the type-checker informing you that your
program is wrong. While it can be tempting to blame the tool, the real fault is
in the workmanship.

