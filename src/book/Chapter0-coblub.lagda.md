---
suppress-bibliography: true
...

# The Co-blub Paradox {.unnumbered #sec:coblub}

It is widely acknowledged that the languages you speak shape the thoughts you
can think; while this is true for natural language, it is doubly so in the case
of programming languages. And it's not hard to see why; while humans have
dedicated neural circuitry for natural language, it would be absurd to suggest
that we also have dedicated neural circuitry for fiddling with arcane, abstract
symbols, usually encoded arbitrarily as electrical potentials on a conductive
metal.

Programming---and mathematics more generally---does not come easily to us
humans, and for this reason it can be hard to see the forest for the trees. We
have no built-in intuition as to what should be possible, and thus, this
intuition is built only by observing the work of more-established practitioners.
In the more artificial human endeavors like programming, newcomers to the field
must be constructivists---their art is shaped only by the patterns they have
previously observed. Because different programming languages support different
features and idioms, the imaginable shape of what programming *is* must be
shaped by those languages we understand deeply.

In a famous essay, "Beating the Averages," @graham_beating_2001 points out the
so-called *Blub paradox.* This, Graham says, is the ordering of programming
languages by powerfulness; a programmer who thinks in a middle-of-the-road
language along this ordering (call it Blub) can identify less powerful
languages, but not those which are more powerful. The idea rings true; one can
arrange languages in power by the features they support, and subsequently check
to see if a language supports all the features we feel to be important. If it
doesn't, it must be less powerful. However, this technique doesn't work to
identify more powerful languages---at best, you will see that the compared
language supports all the features you're looking for, but you don't know enough
to ask for more.

Quasi-formally, we can describe the Blub paradox as a semi-decision procedure.
That is, given an ordering over programming languages (here, by their relative
"power",) we can determine whether a language is less than our comparison
language, but not whether it is more than. We can determine when the answer is
definitely "yes," but, not when it is "no!"

Over two decades of climbing this lattice of powerful languages, I have come to
understand a lesser-known corollary of the Blub paradox, coining it the *Co-Blub
paradox.* This is: knowledge of lesser languages is *actively harmful* when
transposed into the context of a more powerful language. The hoops you
unwittingly jumped through in Blub due to lacking feature X are *anti-patterns*
in the presence of feature X. This is obviously true when stated abstractly, but
insidiously hard to see when we are the ones writing the anti-patterns.

Let's look at a few examples over the ages, to help motivate the problem before
we get into our introspection proper. In the beginning, people programmed
directly in machine code. Not assembly, mind you, but in raw binary-encoded
op-codes. They had a book somewhere showing them what bits needed to be set in
order to cajole the machine into performing any given instruction. Presumably if
this were your job, you'd eventually memorize the bit patterns for common
operations, and it wouldn't be nearly as tedious as it seems today.

Then came assembly languages, which provided human-meaningful mnemonics to the
computer's opcodes. No longer did we need to encode a jump as the number 1018892
(`11111000110000001100` in binary)---now it was simply `jl 16`. Still mysterious
to be sure, but you must admit such a thing is infinitely more legible. When
encoded directly in machine code, programs were, for the most part, write-only.
But assembly languages don't come for free; first you need to write an
assembler: a program that reads the mnemonics and outputs the raw machine code.
If you were already proficient writing machine code directly, you can imagine
the task of implementing an assembler to feel like make work---a tool to
automate a problem you don't have. In the context of the Co-Blub paradox,
knowing the direct encodings of your opcodes is an anti-pattern when you have an
assembly language, as it makes your contributions inscrutable to your peers.

Programming directly in assembly eventually hit its limits. Every computer had a
different assembly language, which meant if you wanted to run the same program
on a different computer you'd have to completely rewrite the whole thing; often
needing to translate between extremely different concepts and limitations.
Ignoring a lot of history, C came around with the big innovation that software
should be portable between different computers: the same C program should work
regardless of the underlying machine architecture---more or less. If you were an
assembly programmer, you ran into the anti-pattern that while you could squeeze
more performance and perform clever optimizations if you were aware of the
underlying architecture, this fundamentally limited you *to that platform.*

By virtue of being in many ways a unifying assembly language, C runs very
close to what we think of as "the metal." Although different computer
architectures have minor differences in registers and ways of doing things, they
are all extremely similar variations on a theme. They all expose storable memory
indexed by a number, operations for performing basic logic and arithmetic tasks,
and means of jumping around to what the computer should consider to be the next
instruction. As a result, C exposes this abstraction of what a computer *is* to
its programmers, who are thus required to think about mutable memory and about
how to encode complicated objects as sequences of bytes in that memory.

But then (skipping much history) came along Java, whose contribution to
mainstream programming was to popularize the idea that memory is cheap and
abundant. Thus, Java teaches its adherents that it's OK to waste some bytes in
order to alleviate the headache of needing to wrangle it all on your own. A C
programmer coming to Java must unlearn the idea that memory is sacred and
scarce, that one can do a better job of keeping track of it than the compiler
can. The hardest thing to unlearn is that memory is an important thing to think
about in the first place.

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
the "command pattern," which has required much ado and ink to be spilled. In
Lisp, however, you can just pass functions around as first-class values and
everything works properly. It can be hard to grok why exactly if you are used to
thinking about computer programs as static sequences of instructions. Indeed,
the command pattern is bloated and ultimately unnecessary in Lisp, and
practitioners must first unlearn it before they can begin to see the way of
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

All of this brings us to Agda, which is as far as I've personally come along the
power lattice of programming languages. Agda's powerful type system allows us to
articulate many invariants that are impossible to write down in other languages.
In fact, its type system is so precise we can *prove* that our solutions are
correct, which alleviates the need to actually *run* the subsequent programs. In
essence, programming in Agda abstracts away the notion of execution entirely.
Following our argument about co-Blub programmers, they will come to Agda with
the anti-pattern that thinking their hard-earned, battle-proven programming
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
in the craftsmanship.


## A World Without Execution? {.unnumbered .unlisted}

It's worth stopping and asking ourselves in what way a non-executable
programming language might be useful. If the end result of a coding endeavor is
the eventual result, whether that be an answer (as in a computation) or series
of side-effects (as in most real-world programs,) non-execution seems useless at
best and masturbatory at worst.

Consider the case of rewriting a program from scratch. Even though we reuse none
of the original source code, nor the compiled artifacts, the second time through
writing a program is always much easier. Why should this be so? Writing the
program has an effect on the world, completely apart from the digital artifacts
that result---namely, the way in which your brain changes from having written
the program. Programming is a creative endeavor, and every program leaves its mark on its
creator. It is through these mental battle scars---accumulated from struggling
with and conquering problems---that we become better programmers. Considering a
program to be a digital artifact only ignores the very real groove it made on
its author's brain.

It is for this reason that programmers, in their spare time, will also write
other sorts of programs. Code that are is not necessarily useful, but code that
allows its author to grapple with problems. Many open-source projects got
started as a hobbyist project that someone created in order to learn more about
the internals of databases, or to try their hand at implementing a new
programming language. For programmers, code is a very accessible means of
exploring new ideas, which acts as a forcing function to prevent us from fooling
ourselves into thinking we understand when we don't. After all, it's much easier
to fool ourselves than it is to fool the computer.

So, programmers are familiar with writing programs, not for running the eventual
code, but for the process of having built it in the first place. In effect, the
real output of this process is the neural pathways it engenders.

Agda fits very naturally into this niche; the purpose of writing Agda is not to
be able to run the code, but because Agda is so strict with what it allows.
Having programmed it in Agda will teach you much more about the subject than you
thought there was to know. Agda forces you to grapple with the hard, conceptual
parts of the problem, without worrying very much about how you're going to make
the whole thing go fast later. After all, there's nothing *to* go fast if you
don't know what you're building in the first place.

Consider the universal programmer experience of spending a week implementing a
tricky algorithm or data structure, only to realize upon completion that you
don't need it---either that it doesn't do what you hoped, or it doesn't actually
solve the problem you thought you had. Unfortunately, this is the rule in
software, not the exception. Without total conceptual clarity, our software can
never possibly be correct, if for no other reason than we don't know what
correct *means.* Maybe the program will still give you an answer, but it is
nothing but willful ignorance to assume this output corresponds at all to
reality.

The reality is, conceptual understanding is the difficult part of
programming---the rest is just coloring by numbers. The way we have all learned
how to do programming is to attempt to solve both problems at once: we write
code and try to decipher the problem as we go; it is the rare coder who stops to
think on the whiteboard, and the rarer-still engineer who starts there.

But again recall the case of rewriting a program. Once you have worked through
the difficult pieces, the rest is just going through the motions. There exists
some order in which we must wiggle our fingers to produce the necessary syntax
for the computer to solve our problem, and finding this order is trivial once we
have conceptual clarity of what the solution is.

This, in short, is the value of learning and writing Agda. It's less of a
programming language as it is a tool for thought; one in which we can express
extremely precise ideas, propagate constraints around, and be informed loudly
whenever we fail to live up to the exacting rigor that Agda demands of us. While
traditional programming models are precise only about the "how," Agda allows us
to instead think about the "what," without worrying very much about the "how."
After all, we're all very good at the "how"---it's been drilled into us for our
entire careers.

